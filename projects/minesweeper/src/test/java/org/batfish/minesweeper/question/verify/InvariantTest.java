package org.batfish.minesweeper.question.verify;

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
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class InvariantTest {
    private static final NetworkFactory nf = new NetworkFactory();
    private static final Node ALPHANODE = new Node("10.0.0.1","alphaNode");
    private static final Node BETANODE = new Node("10.0.0.2","betaNode");
    private static final Node GAMMANODE = new Node("10.0.0.3","gammaNode");
    private static final Node DELTANODE = new Node("10.0.0.4","deltaNode");
    private static final Map<Node, Configuration> configs = new HashMap<>();
    private static final Map<Node, RoutingPolicy> imports = new HashMap<>();
    private static final Map<Node, RoutingPolicy> exports = new HashMap<>();
    private TransferBDD tbdd;
    private ConfigAtomicPredicates configAPs;

    private static final String IMPORT_POLICY_NAME = "from_entering";
    private static final String EXPORT_POLICY_NAME = "to_leaving";
    private static final String PREFIX_MATCH = "prefixMatch";
    private static final String NEXT_DOOR = "nextDoor";
    private static final PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

    private static ConfigAtomicPredicates getConfigAtomicPredicates(Collection<Configuration> configs, Set<RegexConstraint> communityRegexes) {
        return new ConfigAtomicPredicates(
                configs.stream().map(config -> {
                    Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                    Map.Entry<Configuration, Collection<RoutingPolicy>> entry = new AbstractMap.SimpleImmutableEntry<>(config, policies);
                    return entry; // need to create variables to adhere to types
                } ).toList(),
                communityRegexes.stream().flatMap(rc -> {
                    String regex = rc.getRegex();
                    return switch (rc.getRegexType()) {
                        case REGEX -> ImmutableList.of(CommunityVar.from(regex)).stream();
                        case STRUCTURE_NAME -> Stream.empty();
                    };}).collect(ImmutableSet.toImmutableSet()),
                new HashSet<>()); // for AS path stuff
    }

    private BgpProcess getBgpProcess (Node node) {
        Vrf vrf = nf.vrfBuilder().setOwner(configs.get(node)).setName(Configuration.DEFAULT_VRF_NAME).build();
        return nf.bgpProcessBuilder().setRouterId(node.getIp())
                .setEbgpAdminCost(0).setIbgpAdminCost(0).setLocalAdminCost(0)
                .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
                .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setVrf(vrf).build();
    }

    @Before
    public void setup() throws IOException {
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,null,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,null,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,null,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,null,EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,null,null)));

        BooleanExpr check_comm_100_1 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1"))));
        BooleanExpr check_comm_100_2 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))));
        BooleanExpr checkPrefixMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_MATCH));

        List<Statement> add_100_1 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:1")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_100_2 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:2")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> permit = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue));
        List<Statement> deny = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));

        RoutingPolicy alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2,deny,permit))).build();

        imports.put(ALPHANODE,new RoutingPolicy("BLANK",configs.get(ALPHANODE)));
        imports.put(BETANODE,new RoutingPolicy("BLANK",configs.get(BETANODE)));
        imports.put(GAMMANODE,new RoutingPolicy("BLANK",configs.get(GAMMANODE)));
        imports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2")).build();
        configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        tbdd = new TransferBDD(configAPs);
    }

    private BDD commBDDString(String regex) {
        BDDRoute route = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        return tbdd.getFactory().orAll(tbdd.getConfigAtomicPredicates()
                .getStandardCommunityAtomicPredicates()
                .getRegexAtomicPredicates()
                .get(CommunityVar.from(StandardCommunity.parse(regex)))
                .stream().map(i -> route.getCommunityAtomicPredicates()[i])
                .collect(ImmutableSet.toImmutableSet()));
    }

    private static BDD prefixSpaceToBDD(PrefixSpace space, BDDRoute r, boolean positive) {
        BDDFactory factory = r.getPrefix().getFactory();
        if (space.isEmpty()) {
            return factory.one();
        } else {
            BDD result = factory.zero();
            for (PrefixRange range : space.getPrefixRanges()) {
                BDD rangeBDD = isRelevantForDestination(r,range);
                result = result.or(rangeBDD);
            }
            if (!positive){
                result = result.not();
            }
            return result;
        }
    }

    private BDD wellFormed(TransferBDD tbdd, BDD input) {
        BDDRoute route = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        return route.wellFormednessConstraints(true).and(input);
    }

    @Test
    public void communityInvariantToBDDTest() {
        RoutingPolicy policyUsed = exports.get(BETANODE);

        RegexConstraint comm_100_2 = RegexConstraint.parse("100:2");
        RegexConstraint not_comm_100_1 = RegexConstraint.parse("!100:1");
        Invariant.ClauseBuilder match = Invariant.createClause(null,null,new RegexConstraints(List.of(comm_100_2)));
        Invariant.ClauseBuilder avoid = Invariant.createClause(null,null,new RegexConstraints(List.of(not_comm_100_1)));
        Invariant.ClauseBuilder both = Invariant.createClause(null,null,new RegexConstraints(List.of(comm_100_2,not_comm_100_1)));

        BDD match_100_1 = commBDDString("100:1");
        BDD match_100_2 = commBDDString("100:2");

        Invariant matchInv = new Invariant(tbdd,match.build(tbdd,policyUsed));
        assertEquals(matchInv.wellFormedBDD(), wellFormed(tbdd,match_100_2.id()));

        Invariant avoidInv = new Invariant(tbdd,avoid.build(tbdd,policyUsed));
        assertEquals(avoidInv.wellFormedBDD(), wellFormed(tbdd,match_100_1.id().not()));

        Invariant bothInv = new Invariant(tbdd,both.build(tbdd,policyUsed));
        assertEquals(bothInv.wellFormedBDD(), wellFormed(tbdd,match_100_2.id().and(match_100_1.id().not())));

        Invariant eitherInv = Invariant.builder().addClause(match).addClause(avoid).build(tbdd,policyUsed);
        assertEquals(eitherInv.wellFormedBDD(), wellFormed(tbdd,match_100_2.id().or(match_100_1.id().not())));
    }

    @Test
    public void prefixInvariantToBDDTest() {
        BDDRoute base = new BDDRoute(this.tbdd.getFactory(),new ConfigAtomicPredicates(configAPs));
        RoutingPolicy policyUsed = exports.get(ALPHANODE);

        PrefixSpace checkedP = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));
        PrefixSpace matchesP = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.24.0/24")));
        PrefixSpace greaterP = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.0.0.0/16")));

        Invariant.ClauseBuilder checked = Invariant.createClause(checkedP,null,null);
        Invariant.ClauseBuilder matches = Invariant.createClause(matchesP,null,null);
        Invariant.ClauseBuilder sub = Invariant.createClause(checkedP,matchesP,null);
        Invariant.ClauseBuilder excluded = Invariant.createClause(greaterP,checkedP,null);
        Invariant.ClauseBuilder avoided = Invariant.createClause(null,checkedP,null);

        BDD checkedBDD = wellFormed(tbdd,prefixSpaceToBDD(checkedP, base, true));
        BDD avoidCheckedBDD = wellFormed(tbdd,prefixSpaceToBDD(checkedP, base, false));
        BDD matchesBDD = wellFormed(tbdd,prefixSpaceToBDD(matchesP, base, true));
        BDD greaterBDD = wellFormed(tbdd,prefixSpaceToBDD(greaterP, base, true));

        Invariant checkedInv = new Invariant(tbdd,checked.build(tbdd,policyUsed));
        assertEquals(checkedBDD,checkedInv.wellFormedBDD());

        Invariant avoidInv = new Invariant(tbdd,avoided.build(tbdd,policyUsed));
        assertEquals(avoidCheckedBDD,avoidInv.wellFormedBDD());

        Invariant matchesInv = new Invariant(tbdd,matches.build(tbdd,policyUsed));
        assertEquals(matchesBDD,matchesInv.wellFormedBDD());

        Invariant subInv = new Invariant(tbdd,sub.build(tbdd,policyUsed));
        assertEquals(checkedBDD.diff(matchesBDD),subInv.wellFormedBDD());

        Invariant excludedInv = new Invariant(tbdd,excluded.build(tbdd,policyUsed));
        assertEquals(greaterBDD.diff(checkedBDD),excludedInv.wellFormedBDD());
    }

    @Test
    public void weakestPreconditionExactTest() {
        Invariant.ClauseBuilder clauseP = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("13.25.0.0/16"))));
        Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
        Invariant.ClauseBuilder match_100_1 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
        Invariant.ClauseBuilder match_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));
        Invariant.ClauseBuilder avoid_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:2"))));

        // [1] P \/ 100:2 in Comm = WP(Export_alpha,P)
        Invariant P = Invariant.builder().addClause(clauseP).build(tbdd,exports.get(GAMMANODE));
        Invariant wp1 = P.weakestPrecondition(exports.get(GAMMANODE));
        Invariant expected1 = Invariant.builder().addClause(clauseP).addClause(match_100_2).build(tbdd,exports.get(GAMMANODE));
        assertEquals(wp1.wellFormedBDD(),expected1.wellFormedBDD());

        // [2] False = WP(Export_alpha,prefix /\ 100:1 not in Comm)
        BDD avoid_100_1_match_prefix = Invariant.clauseBuilder()
                .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:1"))))
                .matchPrefix(PREFIX).build(tbdd,exports.get(ALPHANODE));
        Invariant Q = new Invariant(tbdd,avoid_100_1_match_prefix);
        Invariant wp2 = Q.weakestPrecondition(exports.get(ALPHANODE));
        assertTrue(wp2.isFalse());

        // [3] 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,100:2 in Comm)
        Invariant R = Invariant.builder().addClause(match_100_2).build(tbdd,exports.get(BETANODE));
        Invariant wp3 = R.weakestPrecondition(exports.get(BETANODE));
        Invariant expected3 = Invariant.builder().addClause(match_100_1).addClause(match_100_2).build(tbdd,exports.get(BETANODE));
        assertEquals(wp3.wellFormedBDD(),expected3.wellFormedBDD());

        // [4] not_prefix \/ 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,not_prefix \/ 100:2 in Comm)
        Invariant S = Invariant.builder().addClause(avoidPrefix).addClause(match_100_2).build(tbdd,exports.get(BETANODE));
        Invariant wp4 = S.weakestPrecondition(exports.get(BETANODE));
        Invariant expected4 = Invariant.builder().addClause(avoidPrefix).addClause(match_100_1).addClause(match_100_2).build(tbdd,exports.get(BETANODE));
        assertEquals(wp4.wellFormedBDD(),expected4.wellFormedBDD());

        // [5] 100:2 in Comm = WP(Export_gamma,100:2 in Comm)
        Invariant T = Invariant.builder().addClause(match_100_2).build(tbdd,exports.get(GAMMANODE));
        Invariant wp5 = T.weakestPrecondition(exports.get(GAMMANODE));
        Invariant expected5 = Invariant.builder().addClause(match_100_2).build(tbdd,exports.get(GAMMANODE));
        assertEquals(wp5.wellFormedBDD(),expected5.wellFormedBDD());

        // [6] True (well-formed) = WP(Export_gamma,100:2 not in Comm)
        Invariant U = Invariant.builder().addClause(avoid_100_2).build(tbdd,exports.get(GAMMANODE));
        Invariant wp6 = U.weakestPrecondition(exports.get(GAMMANODE));
        assertTrue(wp6.isTrue());

        // [7] 100:2 in Comm \/ not_prefix = WP(Export_gamma,not_prefix)
        Invariant W = Invariant.builder().addClause(avoidPrefix).build(tbdd,exports.get(GAMMANODE));
        Invariant wp7 = W.weakestPrecondition(exports.get(GAMMANODE));
        Invariant expected7 = Invariant.builder().addClause(match_100_2).addClause(avoidPrefix).build(tbdd,exports.get(GAMMANODE));
        assertEquals(wp7.wellFormedBDD(),expected7.wellFormedBDD());
    }

    @Test
    public void weakestPreconditionValidTest() {
        Invariant.ClauseBuilder clauseP = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("13.25.0.0/16"))));
        Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
        Invariant.ClauseBuilder match_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));
        Invariant.ClauseBuilder avoid_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:2"))));

        // [1] P \/ 100:2 in Comm = WP(Export_alpha,P)
        Invariant P = Invariant.builder().addClause(clauseP).build(tbdd,exports.get(GAMMANODE));
        assertTrue(P.validPrecondition(P.weakestPrecondition(exports.get(GAMMANODE)),exports.get(GAMMANODE)));

        // [2] False = WP(Export_alpha,prefix /\ 100:1 not in Comm)
        BDD avoid_100_1_match_prefix = Invariant.clauseBuilder()
                .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!100:1"))))
                .matchPrefix(PREFIX).build(tbdd,exports.get(ALPHANODE));
        Invariant Q = new Invariant(tbdd,avoid_100_1_match_prefix);
        assertTrue(Q.validPrecondition(Q.weakestPrecondition(exports.get(ALPHANODE)),exports.get(ALPHANODE)));

        // [3] 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,100:2 in Comm)
        Invariant R = Invariant.builder().addClause(match_100_2).build(tbdd,exports.get(BETANODE));
        assertTrue(R.validPrecondition(R.weakestPrecondition(exports.get(BETANODE)),exports.get(BETANODE)));

        // [4] not_prefix \/ 100:2 in Comm \/ 100:1 in Comm = WP(Export_beta,not_prefix \/ 100:2 in Comm)
        Invariant S = Invariant.builder().addClause(avoidPrefix).addClause(match_100_2).build(tbdd,exports.get(BETANODE));
        assertTrue(S.validPrecondition(S.weakestPrecondition(exports.get(BETANODE)),exports.get(BETANODE)));

        // [5] 100:2 in Comm = WP(Export_gamma,100:2 in Comm)
        Invariant T = Invariant.builder().addClause(match_100_2).build(tbdd,exports.get(GAMMANODE));
        assertTrue(T.validPrecondition(T.weakestPrecondition(exports.get(GAMMANODE)),exports.get(GAMMANODE)));

        // [6] True (well-formed) = WP(Export_gamma,100:2 not in Comm)
        Invariant U = Invariant.builder().addClause(avoid_100_2).build(tbdd,exports.get(GAMMANODE));
        assertTrue(U.validPrecondition(U.weakestPrecondition(exports.get(GAMMANODE)),exports.get(GAMMANODE)));

        // [7] 100:2 in Comm \/ not_prefix = WP(Export_gamma,not_prefix)
        Invariant W = Invariant.builder().addClause(avoidPrefix).build(tbdd,exports.get(GAMMANODE));
        assertTrue(W.validPrecondition(W.weakestPrecondition(exports.get(GAMMANODE)),exports.get(GAMMANODE)));
    }

    @Test
    public void weakestPreconditionsMatchExampleTest() {
        Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
        Invariant.ClauseBuilder match_100_1 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
        Invariant.ClauseBuilder match_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));

        Invariant.Builder not_prefix = Invariant.builder().addClause(avoidPrefix);
        Invariant.Builder prefix_implies_100_2 = Invariant.builder().addClause(avoidPrefix).addClause(match_100_2);
        Invariant.Builder prefix_implies_100_1_2 = Invariant.builder().addClause(avoidPrefix).addClause(match_100_2).addClause(match_100_1);

        // Node Invariants
        Invariant alphaNode = new Invariant(tbdd);
        Invariant betaNode = prefix_implies_100_1_2.build(tbdd,imports.get(BETANODE));
        Invariant gammaNode = prefix_implies_100_2.build(tbdd,imports.get(GAMMANODE));
        Invariant deltaNode = not_prefix.build(tbdd,imports.get(DELTANODE));

        // Edge Invariants
        Invariant alpha_beta = prefix_implies_100_1_2.build(tbdd,exports.get(ALPHANODE));
        Invariant beta_alpha = new Invariant(tbdd);
        Invariant beta_gamma = prefix_implies_100_2.build(tbdd,exports.get(BETANODE));
        Invariant gamma_beta = prefix_implies_100_1_2.build(tbdd,exports.get(GAMMANODE));
        Invariant gamma_delta = not_prefix.build(tbdd,exports.get(GAMMANODE));
        Invariant delta_gamma = prefix_implies_100_2.build(tbdd,exports.get(DELTANODE));

        // Node Checks
        Invariant wp_alpha_node = alpha_beta.weakestPrecondition(exports.get(ALPHANODE));
        assertTrue(wp_alpha_node.isTrue());

        Invariant wp_beta_node = beta_gamma.weakestPrecondition(exports.get(BETANODE));
        assertEquals(wp_beta_node,betaNode);
        Invariant wp_beta_node_ = beta_alpha.weakestPrecondition(exports.get(BETANODE));
        assertTrue(wp_beta_node_.impliedBy(betaNode));

        Invariant wp_gamma_node = gamma_delta.weakestPrecondition(exports.get(GAMMANODE));
        assertEquals(wp_gamma_node,gammaNode);
        Invariant wp_gamma_node_ = gamma_beta.weakestPrecondition(exports.get(GAMMANODE));
        assertTrue(wp_gamma_node_.impliedBy(gammaNode));
        assertEquals(wp_gamma_node_,(prefix_implies_100_1_2.build(tbdd,exports.get(GAMMANODE))));

        Invariant wp_delta_node = delta_gamma.weakestPrecondition(exports.get(DELTANODE));
        assertTrue(wp_delta_node.impliedBy(deltaNode));
        assertEquals(wp_delta_node,(prefix_implies_100_2.build(tbdd,exports.get(DELTANODE))));

        // Edge Checks
        Invariant wp_gamma_delta = deltaNode.weakestPrecondition(imports.get(DELTANODE));
        assertEquals(wp_gamma_delta,gamma_delta);

        Invariant wp_delta_gamma = gammaNode.weakestPrecondition(imports.get(GAMMANODE));
        assertEquals(wp_delta_gamma,delta_gamma);
        Invariant wp_beta_gamma = gammaNode.weakestPrecondition(imports.get(GAMMANODE));
        assertEquals(wp_beta_gamma,beta_gamma);

        Invariant wp_alpha_beta = betaNode.weakestPrecondition(imports.get(BETANODE));
        assertEquals(wp_alpha_beta,alpha_beta);
        Invariant wp_gamma_beta = betaNode.weakestPrecondition(imports.get(BETANODE));
        assertEquals(wp_gamma_beta,gamma_beta);

        Invariant wp_beta_alpha = alphaNode.weakestPrecondition(imports.get(ALPHANODE));
        assertTrue(wp_beta_alpha.isTrue());
        assertEquals(wp_beta_alpha,beta_alpha);
    }
}
