package org.batfish.minesweeper.question.verificationutilities;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.RouteFilterLine;
import org.batfish.datamodel.RouteFilterList;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.bgp.community.StandardCommunity;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.communities.ColonSeparatedRendering;
import org.batfish.datamodel.routing_policy.communities.CommunityIs;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchExpr;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchRegex;
import org.batfish.datamodel.routing_policy.communities.CommunitySet;
import org.batfish.datamodel.routing_policy.communities.HasCommunity;
import org.batfish.datamodel.routing_policy.communities.InputCommunities;
import org.batfish.datamodel.routing_policy.communities.LiteralCommunitySet;
import org.batfish.datamodel.routing_policy.communities.MatchCommunities;
import org.batfish.datamodel.routing_policy.communities.SetCommunities;
import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.datamodel.routing_policy.expr.DestinationNetwork;
import org.batfish.datamodel.routing_policy.expr.MatchPrefixSet;
import org.batfish.datamodel.routing_policy.expr.NamedPrefixSet;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferBDDUtils;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class InvariantTest {
  private static final NetworkFactory nf = new NetworkFactory();
  private static final Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
  private static final Node BETANODE = new Node("10.0.0.2", "betaNode");
  private static final Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
  private static final Node DELTANODE = new Node("10.0.0.4", "deltaNode");
  private static final Map<Node, Configuration> configs = new HashMap<>();
  private static final Map<Node, RoutingPolicy> imports = new HashMap<>();
  private static final Map<Node, RoutingPolicy> exports = new HashMap<>();
  private TransferBDD tbdd;
  private ConfigAtomicPredicates configAPs;

  // private static final String IMPORT_POLICY_NAME = "from_entering";
  private static final String EXPORT_POLICY_NAME = "to_leaving";
  private static final String PREFIX_MATCH = "prefixMatch";
  private static final String NEXT_DOOR = "nextDoor";
  private static final PrefixSpace PREFIX =
      new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

  private static ConfigAtomicPredicates getConfigAtomicPredicates(
      Collection<Configuration> configs, Set<RegexConstraint> communityRegexes) {
    return new ConfigAtomicPredicates(
        configs.stream()
            .map(
                config -> {
                  Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                  Map.Entry<Configuration, Collection<RoutingPolicy>> entry =
                      new AbstractMap.SimpleImmutableEntry<>(config, policies);
                  return entry; // need to create variables to adhere to types
                })
            .toList(),
        communityRegexes.stream()
            .flatMap(
                rc -> {
                  String regex = rc.getRegex();
                  return switch (rc.getRegexType()) {
                    case REGEX -> ImmutableList.of(CommunityVar.from(regex)).stream();
                    case STRUCTURE_NAME -> Stream.empty();
                  };
                })
            .collect(ImmutableSet.toImmutableSet()),
        new HashSet<>()); // for AS path stuff
  }

  private BgpProcess getBgpProcess(Node node) {
    Vrf vrf =
        nf.vrfBuilder().setOwner(configs.get(node)).setName(Configuration.DEFAULT_VRF_NAME).build();
    return nf.bgpProcessBuilder()
        .setRouterId(node.getSingleIp())
        .setEbgpAdminCost(0)
        .setIbgpAdminCost(0)
        .setLocalAdminCost(0)
        .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
        .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setVrf(vrf)
        .build();
  }

  @Before
  public void setup() throws IOException {
    // Instantiate configurations
    CommunityMatchExpr comm_100_1 =
        new CommunityMatchRegex(ColonSeparatedRendering.instance(), "^100:1$");
    CommunityMatchExpr comm_100_2 =
        new CommunityMatchRegex(ColonSeparatedRendering.instance(), "^100:2$");
    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_MATCH,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
    Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
    configs.put(
        ALPHANODE,
        alphaCB
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .setDefaultInboundAction(PERMIT)
            .build());
    configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));
    configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2", comm_100_2));
    configs
        .get(ALPHANODE)
        .setCommunitySetMatchExprs(
            ImmutableMap.of(
                "comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
    Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
    configs.put(
        BETANODE,
        betaCB
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .setDefaultInboundAction(PERMIT)
            .build());
    configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1", comm_100_1));
    configs
        .get(BETANODE)
        .setCommunitySetMatchExprs(
            ImmutableMap.of(
                "comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
    Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
    configs.put(
        GAMMANODE,
        gammaCB
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .setDefaultInboundAction(PERMIT)
            .build());
    configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2", comm_100_2));
    configs
        .get(GAMMANODE)
        .setCommunitySetMatchExprs(
            ImmutableMap.of(
                "comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
    Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
    configs.put(
        DELTANODE,
        deltaCB
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .setDefaultInboundAction(PERMIT)
            .build());

    // Create BGP processes
    BgpProcess alphaBgp = getBgpProcess(ALPHANODE);
    alphaBgp.setNeighbors(
        ImmutableSortedMap.of(
            BETANODE.getSingleIp(), getBgpActivePeerConfig(NEXT_DOOR, null, EXPORT_POLICY_NAME)));
    BgpProcess betaBgp = getBgpProcess(BETANODE);
    betaBgp.setNeighbors(
        ImmutableSortedMap.of(
            ALPHANODE.getSingleIp(), getBgpActivePeerConfig(NEXT_DOOR, null, EXPORT_POLICY_NAME),
            GAMMANODE.getSingleIp(), getBgpActivePeerConfig(NEXT_DOOR, null, EXPORT_POLICY_NAME)));
    BgpProcess gammaBgp = getBgpProcess(GAMMANODE);
    gammaBgp.setNeighbors(
        ImmutableSortedMap.of(
            BETANODE.getSingleIp(), getBgpActivePeerConfig(NEXT_DOOR, null, EXPORT_POLICY_NAME),
            DELTANODE.getSingleIp(), getBgpActivePeerConfig(NEXT_DOOR, null, EXPORT_POLICY_NAME)));
    BgpProcess deltaBgp = getBgpProcess(DELTANODE);
    deltaBgp.setNeighbors(
        ImmutableSortedMap.of(
            GAMMANODE.getSingleIp(), getBgpActivePeerConfig(NEXT_DOOR, null, null)));

    BooleanExpr check_comm_100_1 =
        new MatchCommunities(
            new InputCommunities(),
            new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1"))));
    BooleanExpr check_comm_100_2 =
        new MatchCommunities(
            new InputCommunities(),
            new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))));
    BooleanExpr checkPrefixMatch =
        new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_MATCH));

    List<Statement> add_100_1 =
        ImmutableList.of(
            new SetCommunities(
                new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:1")))),
            new Statements.StaticStatement(Statements.ReturnTrue));

    List<Statement> add_100_2 =
        ImmutableList.of(
            new SetCommunities(
                new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:2")))),
            new Statements.StaticStatement(Statements.ReturnTrue));

    List<Statement> permit =
        ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue));
    List<Statement> deny = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));

    RoutingPolicy alphaExport =
        nf.routingPolicyBuilder()
            .setOwner(configs.get(ALPHANODE))
            .setName(EXPORT_POLICY_NAME)
            .setStatements(ImmutableList.of(new If(checkPrefixMatch, add_100_1, permit)))
            .build();
    RoutingPolicy betaExport =
        nf.routingPolicyBuilder()
            .setOwner(configs.get(BETANODE))
            .setName(EXPORT_POLICY_NAME)
            .setStatements(ImmutableList.of(new If(check_comm_100_1, add_100_2, permit)))
            .build();
    RoutingPolicy gammaExport =
        nf.routingPolicyBuilder()
            .setOwner(configs.get(GAMMANODE))
            .setName(EXPORT_POLICY_NAME)
            .setStatements(ImmutableList.of(new If(check_comm_100_2, deny, permit)))
            .build();

    imports.put(ALPHANODE, new RoutingPolicy("BLANK", configs.get(ALPHANODE)));
    imports.put(BETANODE, new RoutingPolicy("BLANK", configs.get(BETANODE)));
    imports.put(GAMMANODE, new RoutingPolicy("BLANK", configs.get(GAMMANODE)));
    imports.put(DELTANODE, new RoutingPolicy("BLANK", configs.get(DELTANODE)));
    exports.put(ALPHANODE, alphaExport);
    exports.put(BETANODE, betaExport);
    exports.put(GAMMANODE, gammaExport);
    exports.put(DELTANODE, new RoutingPolicy("BLANK", configs.get(DELTANODE)));

    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse("100:1"))
            .add(RegexConstraint.parse("100:2"))
            .build();
    configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
    tbdd = new TransferBDD(configAPs);
  }

  private BDD commBDDString(String regex) {
    BDDRoute route = new BDDRoute(tbdd.getFactory(), tbdd.getConfigAtomicPredicates());
    return tbdd.getFactory()
        .orAll(
            tbdd
                .getConfigAtomicPredicates()
                .getStandardCommunityAtomicPredicates()
                .getRegexAtomicPredicates()
                .get(CommunityVar.from(StandardCommunity.parse(regex)))
                .stream()
                .map(i -> route.getCommunityAtomicPredicates()[i])
                .collect(ImmutableSet.toImmutableSet()));
  }

  private static BDD prefixSpaceToBDD(PrefixSpace space, BDDRoute r, boolean positive) {
    BDDFactory factory = r.getPrefix().getFactory();
    if (space.isEmpty()) {
      return factory.one();
    } else {
      BDD result = factory.zero();
      for (PrefixRange range : space.getPrefixRanges()) {
        BDD rangeBDD = isRelevantForDestination(r, range);
        result = result.or(rangeBDD);
      }
      if (!positive) {
        result = result.not();
      }
      return result;
    }
  }

  @Test
  public void communityInvariantToBDDTest() {
    RoutingPolicy policyUsed = exports.get(BETANODE);

    RegexConstraint comm_100_2 = RegexConstraint.parse("100:2");
    RegexConstraint not_comm_100_1 = RegexConstraint.parse("!100:1");
    Invariant.ClauseBuilder match =
        Invariant.createClause(null, null, new RegexConstraints(List.of(comm_100_2)), null, null);
    Invariant.ClauseBuilder avoid =
        Invariant.createClause(
            null, null, new RegexConstraints(List.of(not_comm_100_1)), null, null);
    Invariant.ClauseBuilder both =
        Invariant.createClause(
            null, null, new RegexConstraints(List.of(comm_100_2, not_comm_100_1)), null, null);

    BDD match_100_1 = commBDDString("100:1");
    BDD match_100_2 = commBDDString("100:2");

    Invariant matchInv = new Invariant(tbdd, match.build(tbdd, policyUsed));
    assertEquals(matchInv.getBDDCopy(), match_100_2.id());

    Invariant avoidInv = new Invariant(tbdd, avoid.build(tbdd, policyUsed));
    assertEquals(avoidInv.getBDDCopy(), match_100_1.id().not());

    Invariant bothInv = new Invariant(tbdd, both.build(tbdd, policyUsed));
    assertEquals(bothInv.getBDDCopy(), match_100_2.id().and(match_100_1.id().not()));

    Invariant eitherInv =
        Invariant.builder().addClause(match).addClause(avoid).build(tbdd, policyUsed);
    assertEquals(eitherInv.getBDDCopy(), match_100_2.id().or(match_100_1.id().not()));
  }

  @Test
  public void prefixInvariantToBDDTest() {
    BDDRoute base = new BDDRoute(this.tbdd.getFactory(), new ConfigAtomicPredicates(configAPs));
    RoutingPolicy policyUsed = exports.get(ALPHANODE);

    PrefixSpace checkedP = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));
    PrefixSpace matchesP = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.24.0/24")));

    Invariant.ClauseBuilder checked = Invariant.createClause(checkedP, null, null, null, null);
    Invariant.ClauseBuilder matches = Invariant.createClause(matchesP, null, null, null, null);
    Invariant.ClauseBuilder sub = Invariant.createClause(checkedP, matchesP, null, null, null);
    Invariant.ClauseBuilder excluded = Invariant.createClause(checkedP, matchesP, null, null, null);
    Invariant.ClauseBuilder avoided = Invariant.createClause(null, checkedP, null, null, null);

    BDD checkedBDD = prefixSpaceToBDD(checkedP, base, true);
    BDD avoidCheckedBDD = prefixSpaceToBDD(checkedP, base, false);
    BDD matchesBDD = prefixSpaceToBDD(matchesP, base, true);
    BDD intersectionBDD = prefixSpaceToBDD(matchesP, base, false).and(checkedBDD);

    Invariant checkedInv = new Invariant(tbdd, checked.build(tbdd, policyUsed));
    assertEquals(checkedBDD, checkedInv.getBDDCopy());

    Invariant avoidInv = new Invariant(tbdd, avoided.build(tbdd, policyUsed));
    assertEquals(avoidCheckedBDD, avoidInv.getBDDCopy());

    Invariant matchesInv = new Invariant(tbdd, matches.build(tbdd, policyUsed));
    assertEquals(matchesBDD, matchesInv.getBDDCopy());

    Invariant subInv = new Invariant(tbdd, sub.build(tbdd, policyUsed));
    assertEquals(checkedBDD.diff(matchesBDD), subInv.getBDDCopy());

    Invariant excludedInv = new Invariant(tbdd, excluded.build(tbdd, policyUsed));
    assertEquals(intersectionBDD, excludedInv.getBDDCopy());

    // TODO - This implication fails because I think it has to do with overfitting
    // assertTrue(prefixSpaceToBDD(checkedP, base, true)
    // .imp(prefixSpaceToBDD(matchesP, base, true)).isOne());
  }

  @Test
  public void weakestPreconditionExactTest() {
    Invariant.ClauseBuilder clauseP =
        Invariant.clauseBuilder()
            .matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("13.25.0.0/16"))));
    Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
    Invariant.ClauseBuilder match_100_1 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
    Invariant.ClauseBuilder match_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));
    Invariant.ClauseBuilder avoid_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:2"))));

    // [1] P \/ 100:2 in Comm = WP(Export_alpha,P)
    Invariant P = Invariant.builder().addClause(clauseP).build(tbdd, exports.get(GAMMANODE));
    Invariant wp1 = P.weakestPrecondition(exports.get(GAMMANODE));
    Invariant expected1 =
        Invariant.builder()
            .addClause(clauseP)
            .addClause(match_100_2)
            .build(tbdd, exports.get(GAMMANODE));
    assertEquals(wp1.getBDDCopy(), expected1.getBDDCopy());

    // [2] False = WP(Export_alpha,prefix /\ 100:1 not in Comm)
    BDD avoid_100_1_match_prefix =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:1"))))
            .matchPrefix(PREFIX)
            .build(tbdd, exports.get(ALPHANODE));
    Invariant Q = new Invariant(tbdd, avoid_100_1_match_prefix);
    Invariant wp2 = Q.weakestPrecondition(exports.get(ALPHANODE));
    assertTrue(wp2.isFalse());

    // [3] 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,100:2 in Comm)
    Invariant R = Invariant.builder().addClause(match_100_2).build(tbdd, exports.get(BETANODE));
    Invariant wp3 = R.weakestPrecondition(exports.get(BETANODE));
    Invariant expected3 =
        Invariant.builder()
            .addClause(match_100_1)
            .addClause(match_100_2)
            .build(tbdd, exports.get(BETANODE));
    assertEquals(wp3.getBDDCopy(), expected3.getBDDCopy());

    // [4] not_prefix \/ 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,not_prefix \/ 100:2 in
    // Comm)
    Invariant S =
        Invariant.builder()
            .addClause(avoidPrefix)
            .addClause(match_100_2)
            .build(tbdd, exports.get(BETANODE));
    Invariant wp4 = S.weakestPrecondition(exports.get(BETANODE));
    Invariant expected4 =
        Invariant.builder()
            .addClause(avoidPrefix)
            .addClause(match_100_1)
            .addClause(match_100_2)
            .build(tbdd, exports.get(BETANODE));
    assertEquals(wp4.getBDDCopy(), expected4.getBDDCopy());

    // [5] 100:2 in Comm = WP(Export_gamma,100:2 in Comm)
    Invariant T = Invariant.builder().addClause(match_100_2).build(tbdd, exports.get(GAMMANODE));
    Invariant wp5 = T.weakestPrecondition(exports.get(GAMMANODE));
    Invariant expected5 =
        Invariant.builder().addClause(match_100_2).build(tbdd, exports.get(GAMMANODE));
    assertEquals(wp5.getBDDCopy(), expected5.getBDDCopy());

    // [6] True (well-formed) = WP(Export_gamma,100:2 not in Comm)
    Invariant U = Invariant.builder().addClause(avoid_100_2).build(tbdd, exports.get(GAMMANODE));
    Invariant wp6 = U.weakestPrecondition(exports.get(GAMMANODE));
    assertTrue(wp6.isTrue());

    // [7] 100:2 in Comm \/ not_prefix = WP(Export_gamma,not_prefix)
    Invariant W = Invariant.builder().addClause(avoidPrefix).build(tbdd, exports.get(GAMMANODE));
    Invariant wp7 = W.weakestPrecondition(exports.get(GAMMANODE));
    Invariant expected7 =
        Invariant.builder()
            .addClause(match_100_2)
            .addClause(avoidPrefix)
            .build(tbdd, exports.get(GAMMANODE));
    assertEquals(wp7.getBDDCopy(), expected7.getBDDCopy());
  }

  @Test
  public void weakestPreconditionValidTest() {
    Invariant.ClauseBuilder clauseP =
        Invariant.clauseBuilder()
            .matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("13.25.0.0/16"))));
    Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
    Invariant.ClauseBuilder match_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));
    Invariant.ClauseBuilder avoid_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:2"))));

    // [1] P \/ 100:2 in Comm = WP(Export_alpha,P)
    Invariant P = Invariant.builder().addClause(clauseP).build(tbdd, exports.get(GAMMANODE));
    assertTrue(
        P.validPrecondition(P.weakestPrecondition(exports.get(GAMMANODE)), exports.get(GAMMANODE)));

    // [2] False = WP(Export_alpha,prefix /\ 100:1 not in Comm)
    BDD avoid_100_1_match_prefix =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:1"))))
            .matchPrefix(PREFIX)
            .build(tbdd, exports.get(ALPHANODE));
    Invariant Q = new Invariant(tbdd, avoid_100_1_match_prefix);
    assertTrue(
        Q.validPrecondition(Q.weakestPrecondition(exports.get(ALPHANODE)), exports.get(ALPHANODE)));

    // [3] 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,100:2 in Comm)
    Invariant R = Invariant.builder().addClause(match_100_2).build(tbdd, exports.get(BETANODE));
    assertTrue(
        R.validPrecondition(R.weakestPrecondition(exports.get(BETANODE)), exports.get(BETANODE)));

    // [4] not_prefix \/ 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,not_prefix \/ 100:2 in
    // Comm)
    Invariant S =
        Invariant.builder()
            .addClause(avoidPrefix)
            .addClause(match_100_2)
            .build(tbdd, exports.get(BETANODE));
    assertTrue(
        S.validPrecondition(S.weakestPrecondition(exports.get(BETANODE)), exports.get(BETANODE)));

    // [5] 100:2 in Comm = WP(Export_gamma,100:2 in Comm)
    Invariant T = Invariant.builder().addClause(match_100_2).build(tbdd, exports.get(GAMMANODE));
    assertTrue(
        T.validPrecondition(T.weakestPrecondition(exports.get(GAMMANODE)), exports.get(GAMMANODE)));

    // [6] True (well-formed) = WP(Export_gamma,100:2 not in Comm)
    Invariant U = Invariant.builder().addClause(avoid_100_2).build(tbdd, exports.get(GAMMANODE));
    assertTrue(
        U.validPrecondition(U.weakestPrecondition(exports.get(GAMMANODE)), exports.get(GAMMANODE)));

    // [7] 100:2 in Comm \/ not_prefix = WP(Export_gamma,not_prefix)
    Invariant W = Invariant.builder().addClause(avoidPrefix).build(tbdd, exports.get(GAMMANODE));
    assertTrue(
        W.validPrecondition(W.weakestPrecondition(exports.get(GAMMANODE)), exports.get(GAMMANODE)));
  }

  @Test
  public void weakestPreconditionsMatchExampleTest() {
    Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
    Invariant.ClauseBuilder match_100_1 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
    Invariant.ClauseBuilder match_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));

    Invariant.Builder not_prefix = Invariant.builder().addClause(avoidPrefix);
    Invariant.Builder prefix_implies_100_2 =
        Invariant.builder().addClause(avoidPrefix).addClause(match_100_2);
    Invariant.Builder prefix_implies_100_1_2 =
        Invariant.builder().addClause(avoidPrefix).addClause(match_100_2).addClause(match_100_1);

    // Node Invariants
    Invariant alphaNode = new Invariant(tbdd);
    Invariant betaNode = prefix_implies_100_1_2.build(tbdd, imports.get(BETANODE));
    Invariant gammaNode = prefix_implies_100_2.build(tbdd, imports.get(GAMMANODE));
    Invariant deltaNode = not_prefix.build(tbdd, imports.get(DELTANODE));

    // Edge Invariants
    Invariant alpha_beta = prefix_implies_100_1_2.build(tbdd, exports.get(ALPHANODE));
    Invariant beta_alpha = new Invariant(tbdd);
    Invariant beta_gamma = prefix_implies_100_2.build(tbdd, exports.get(BETANODE));
    Invariant gamma_beta = prefix_implies_100_1_2.build(tbdd, exports.get(GAMMANODE));
    Invariant gamma_delta = not_prefix.build(tbdd, exports.get(GAMMANODE));
    Invariant delta_gamma = prefix_implies_100_2.build(tbdd, exports.get(DELTANODE));

    // Node Checks
    Invariant wp_alpha_node = alpha_beta.weakestPrecondition(exports.get(ALPHANODE));
    assertTrue(wp_alpha_node.isTrue());

    Invariant wp_beta_node = beta_gamma.weakestPrecondition(exports.get(BETANODE));
    assertEquals(wp_beta_node, betaNode);
    Invariant wp_beta_node_ = beta_alpha.weakestPrecondition(exports.get(BETANODE));
    assertTrue(wp_beta_node_.impliedBy(betaNode));

    Invariant wp_gamma_node = gamma_delta.weakestPrecondition(exports.get(GAMMANODE));
    assertEquals(wp_gamma_node, gammaNode);
    Invariant wp_gamma_node_ = gamma_beta.weakestPrecondition(exports.get(GAMMANODE));
    assertTrue(wp_gamma_node_.impliedBy(gammaNode));
    assertEquals(wp_gamma_node_, (prefix_implies_100_1_2.build(tbdd, exports.get(GAMMANODE))));

    Invariant wp_delta_node = delta_gamma.weakestPrecondition(exports.get(DELTANODE));
    assertTrue(wp_delta_node.impliedBy(deltaNode));
    assertEquals(wp_delta_node, (prefix_implies_100_2.build(tbdd, exports.get(DELTANODE))));

    // Edge Checks
    Invariant wp_gamma_delta = deltaNode.weakestPrecondition(imports.get(DELTANODE));
    assertEquals(wp_gamma_delta, gamma_delta);

    Invariant wp_delta_gamma = gammaNode.weakestPrecondition(imports.get(GAMMANODE));
    assertEquals(wp_delta_gamma, delta_gamma);
    Invariant wp_beta_gamma = gammaNode.weakestPrecondition(imports.get(GAMMANODE));
    assertEquals(wp_beta_gamma, beta_gamma);

    Invariant wp_alpha_beta = betaNode.weakestPrecondition(imports.get(BETANODE));
    assertEquals(wp_alpha_beta, alpha_beta);
    Invariant wp_gamma_beta = betaNode.weakestPrecondition(imports.get(BETANODE));
    assertEquals(wp_gamma_beta, gamma_beta);

    Invariant wp_beta_alpha = alphaNode.weakestPrecondition(imports.get(ALPHANODE));
    assertTrue(wp_beta_alpha.isTrue());
    assertEquals(wp_beta_alpha, beta_alpha);
  }

  @Test
  public void strongestPostconditionExactTest() {
    Invariant.ClauseBuilder clauseP = Invariant.clauseBuilder().matchPrefix(PREFIX);
    Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
    Invariant.ClauseBuilder match_100_1 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
    Invariant.ClauseBuilder avoid_100_1 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:1"))));
    Invariant.ClauseBuilder match_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));
    Invariant.ClauseBuilder avoid_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:2"))));

    // [1] P /\ 100:1 /\ no other community (specifically 100:2 and match any) = SP(Export_alpha,P)
    Invariant P = Invariant.builder().addClause(clauseP).build(tbdd, exports.get(ALPHANODE));
    Invariant sp1 = P.strongestPostcondition(exports.get(ALPHANODE));
    Invariant expected1 =
        new Invariant(
            tbdd,
            Invariant.clauseBuilder()
                .setCommunities(
                    new RegexConstraints(
                        List.of(RegexConstraint.parse("100:1"), RegexConstraint.parse("!100:2"))))
                .matchPrefix(PREFIX)
                .build(tbdd, exports.get(ALPHANODE))
                .and(tbdd.getFactory().ithVar(0).not()));
    assertEquals(sp1.getBDDCopy(), expected1.getBDDCopy());

    // [2] not P \/  (P /\ 100:1 /\ no other community (specifically 100:2 and match any)) =
    // SP(Export_alpha,True)
    Invariant T = new Invariant(tbdd);
    Invariant sp2 = T.strongestPostcondition(exports.get(ALPHANODE));
    BDD expected2 = avoidPrefix.build(tbdd, exports.get(ALPHANODE)).or(expected1.getBDDCopy());
    assertEquals(sp2.getBDDCopy(), expected2);

    // [3] False = SP(Export_gamma,has comm 100:2)
    Invariant Q = Invariant.builder().addClause(match_100_2).build(tbdd, exports.get(GAMMANODE));
    Invariant sp3 = Q.strongestPostcondition(exports.get(GAMMANODE));
    assertTrue(sp3.isFalse());

    // [4] does not have comm 100:2 = SP(Export_gamma,does not have comm 100:2)
    Invariant R = Invariant.builder().addClause(avoid_100_2).build(tbdd, exports.get(GAMMANODE));
    Invariant sp4 = R.strongestPostcondition(exports.get(GAMMANODE));
    assertEquals(sp4.getBDDCopy(), R.getBDDCopy());

    // [5] does not have comm 100:2 = SP(Export_gamma,True)
    Invariant sp5 = T.strongestPostcondition(exports.get(GAMMANODE));
    assertEquals(sp5.getBDDCopy(), R.getBDDCopy());

    // [6] does not have comm 100:1 = SP(Export_beta,does not have comm 100:1)
    Invariant W = Invariant.builder().addClause(avoid_100_1).build(tbdd, exports.get(BETANODE));
    Invariant sp6 = W.strongestPostcondition(exports.get(BETANODE));
    assertEquals(sp6.getBDDCopy(), W.getBDDCopy());

    // [7] does not have comm 100:1 \/ (has 100:2 and no others) = SP(Export_beta,True)
    Invariant sp7 = T.strongestPostcondition(exports.get(BETANODE));
    Invariant noneBut1002 =
        new Invariant(
            tbdd,
            Invariant.clauseBuilder()
                .setCommunities(
                    new RegexConstraints(
                        List.of(RegexConstraint.parse("!100:1"), RegexConstraint.parse("100:2"))))
                .build(tbdd, exports.get(BETANODE))
                .and(tbdd.getFactory().ithVar(0).not()));
    BDD expected7 = avoid_100_1.build(tbdd, exports.get(BETANODE)).or(noneBut1002.getBDDCopy());
    assertEquals(sp7.getBDDCopy(), expected7);

    // [8] has 100:2 and no others = SP(Export_beta,has comm 100:1)
    Invariant V = Invariant.builder().addClause(match_100_1).build(tbdd, exports.get(BETANODE));
    Invariant sp8 = V.strongestPostcondition(exports.get(BETANODE));
    assertEquals(sp8.getBDDCopy(), noneBut1002.getBDDCopy());
  }

  @Test
  public void interpolationExactTest() {
    // NOTE each test has a comment describing the test of the following form: P => {interpolant: I}
    // => Q
    // where P,Q are the arguments passed to the interpolant function and I is the expected
    // interpolant

    Invariant.ClauseBuilder clauseP = Invariant.clauseBuilder().matchPrefix(PREFIX);
    Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
    Invariant.ClauseBuilder match_100_1 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
    Invariant.ClauseBuilder match_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));

    // [1] prefix(PREFIX) /\ comm(100:1) /\ comm(!100:2) => {interpolant: prefix(PREFIX)} =>
    // prefix(PREFIX)
    Invariant Q = Invariant.builder().addClause(clauseP).build(tbdd, exports.get(ALPHANODE));
    Invariant P =
        new Invariant(
            tbdd,
            Invariant.clauseBuilder()
                .setCommunities(
                    new RegexConstraints(
                        List.of(RegexConstraint.parse("100:1"), RegexConstraint.parse("!100:2"))))
                .matchPrefix(PREFIX)
                .build(tbdd, exports.get(ALPHANODE)));
    Invariant interp =
        new Invariant(
            tbdd, TransferBDDUtils.interpolate(tbdd, P.getBDDCopy(), Q.getBDDCopy(), 64).get());
    assertEquals(interp.getBDDCopy(), Q.getBDDCopy());

    // [2] prefix(PREFIX) /\ (comm(100:1) \/ comm(100:2)) => {interpolant: comm(100:1) \/
    // comm(100:2))}
    //                                  => comm(100:1) \/ comm(100:2) \/ !prefix(PREFIX)
    Invariant PorQ_and_R =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))))
                    .matchPrefix(PREFIX))
            .addClause(
                Invariant.clauseBuilder()
                    .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))))
                    .matchPrefix(PREFIX))
            .build(tbdd, exports.get(BETANODE));
    Invariant SorPorQ =
        Invariant.builder()
            .addClause(match_100_1)
            .addClause(match_100_2)
            .addClause(avoidPrefix)
            .build(tbdd, exports.get(BETANODE));
    Invariant expected2 =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1")))))
            .addClause(
                Invariant.clauseBuilder()
                    .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2")))))
            .build(tbdd, exports.get(BETANODE));
    assertTrue(PorQ_and_R.implies(SorPorQ));
    BDD interpolant =
        TransferBDDUtils.interpolate(tbdd, PorQ_and_R.getBDDCopy(), SorPorQ.getBDDCopy(), 64).get();
    Invariant i = new Invariant(tbdd, interpolant);
    assertEquals(expected2.getBDDCopy(), i.getBDDCopy());

    // [3] prefix(2.4.8.0/24) => {interpolant: prefix(2.4.8.0/24)} => prefix(2.4.8.0/24) \/
    // prefix(100.200.0.0/16)
    Invariant A =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .matchPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("2.4.8.0/24")))))
            .build(tbdd, exports.get(ALPHANODE));
    Invariant B =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .matchPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("2.4.8.0/24")))))
            .addClause(
                Invariant.clauseBuilder()
                    .matchPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("100.200.0.0/16")))))
            .build(tbdd, exports.get(ALPHANODE));
    Invariant AB_interpolant =
        new Invariant(
            tbdd, TransferBDDUtils.interpolate(tbdd, A.getBDDCopy(), B.getBDDCopy(), 64).get());
    Invariant AB_expected =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .matchPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("2.4.8.0/24")))))
            .build(tbdd, exports.get(ALPHANODE));
    assertEquals(AB_expected.getBDDCopy(), AB_interpolant.getBDDCopy());

    // [4] !prefix(2.4.8.0/24) /\ !prefix(100.200.0.0/16) => {interpolant: !prefix(2.4.8.0/24)} =>
    // !prefix(2.4.8.0/24)
    Invariant C =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .avoidPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("2.4.8.0/24"))))
                    .avoidPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("100.200.0.0/16")))))
            .build(tbdd, exports.get(ALPHANODE));
    Invariant D =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .avoidPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("2.4.8.0/24")))))
            .build(tbdd, exports.get(ALPHANODE));
    Invariant CD_interpolant =
        new Invariant(
            tbdd, TransferBDDUtils.interpolate(tbdd, C.getBDDCopy(), D.getBDDCopy(), 64).get());
    Invariant CD_expected =
        Invariant.builder()
            .addClause(
                Invariant.clauseBuilder()
                    .avoidPrefix(
                        new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("2.4.8.0/24")))))
            .build(tbdd, exports.get(ALPHANODE));
    assertEquals(CD_expected.getBDDCopy(), CD_interpolant.getBDDCopy());
  }
}
