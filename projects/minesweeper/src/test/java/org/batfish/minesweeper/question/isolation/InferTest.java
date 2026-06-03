package org.batfish.minesweeper.question.isolation;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.RouteFilterLine;
import org.batfish.datamodel.RouteFilterList;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils;
import org.junit.Test;

import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.replaceCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class InferTest {
  private static final NetworkFactory nf = new NetworkFactory();

  private static final String IMPORT_POLICY_NAME = "from_entering";
  private static final String EXPORT_POLICY_NAME = "to_leaving";
  private static final String NEXT_DOOR = "nextDoor";

  private static final String PREFIX_MATCH = "prefixMatch";
  private static final String prefixStr = "25.13.0.0/16";
  private static final PrefixSpace PREFIX =
      new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefixStr)));

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

  private BgpProcess getBgpProcess(Configuration config, NodeRecord node) {
    Vrf vrf = nf.vrfBuilder().setOwner(config).setName(Configuration.DEFAULT_VRF_NAME).build();
    return nf.bgpProcessBuilder()
        .setRouterId(node.getIp())
        .setEbgpAdminCost(0)
        .setIbgpAdminCost(0)
        .setLocalAdminCost(0)
        .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
        .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setVrf(vrf)
        .build();
  }

  private void setUpConfigs(Map<NodeRecord, Configuration> configs, NodeRecord... nodes) {
    for (NodeRecord node : nodes) {
      Configuration.Builder configBuilder = nf.configurationBuilder().setHostname(node.name());
      configs.put(
          node,
          configBuilder
              .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
              .setDefaultInboundAction(PERMIT)
              .build());
    }
  }

  private Map<NodeRecord, BgpProcess> getBgpProcesses(
      Map<NodeRecord, Configuration> configs, NodeRecord... nodes) {
    Map<NodeRecord, BgpProcess> processes = new HashMap<>();
    for (NodeRecord node : nodes) {
      processes.put(node, getBgpProcess(configs.get(node), node));
    }
    return processes;
  }

  private RoutingPolicy makePolicy(Configuration owner, String name, List<Statement> body) {
    return nf.routingPolicyBuilder().setOwner(owner).setName(name).setStatements(body).build();
  }

  private TestConfigConstructionUtils.Network originalExample(
      NodeRecord ALPHANODE, NodeRecord BETANODE, NodeRecord GAMMANODE, NodeRecord DELTANODE) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> imports = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> exports = new HashMap<>();

    String plain_comm_1 = "100:1";
    String plain_comm_2 = "100:2";
    String regex_comm_100_1 = "^" + plain_comm_1 + "$";
    String regex_comm_100_2 = "^" + plain_comm_2 + "$";

    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_MATCH,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixStr)))));

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE);

    includeCommunities(configs.get(ALPHANODE), regex_comm_100_1);
    configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));
    includeCommunities(configs.get(BETANODE), regex_comm_100_1, regex_comm_100_2);
    includeCommunities(configs.get(GAMMANODE), regex_comm_100_2);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                DELTANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(DELTANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    // Create the policies
    RoutingPolicy alphaImport =
        makePolicy(configs.get(ALPHANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy alphaExport =
        makePolicy(
            configs.get(ALPHANODE),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForPrefixListMatch(PREFIX_MATCH),
                replaceCommunities(plain_comm_1),
                permitRoute(true)));

    RoutingPolicy betaImport =
        makePolicy(configs.get(BETANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy betaExport =
        makePolicy(
            configs.get(BETANODE),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_1),
                replaceCommunities(plain_comm_2),
                permitRoute(true)));

    RoutingPolicy gammaImport =
        makePolicy(configs.get(GAMMANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy gammaExport =
        makePolicy(
            configs.get(GAMMANODE),
            EXPORT_POLICY_NAME,
            ifStatement(checkForCommunity(plain_comm_2), permitRoute(false), permitRoute(true)));

    RoutingPolicy deltaImport =
        makePolicy(configs.get(DELTANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy deltaExport =
        makePolicy(configs.get(DELTANODE), EXPORT_POLICY_NAME, permitRoute(true));

    // Store the policies
    imports.put(ALPHANODE, alphaImport);
    imports.put(BETANODE, betaImport);
    imports.put(GAMMANODE, gammaImport);
    imports.put(DELTANODE, deltaImport);

    exports.put(ALPHANODE, alphaExport);
    exports.put(BETANODE, betaExport);
    exports.put(GAMMANODE, gammaExport);
    exports.put(DELTANODE, deltaExport);

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(plain_comm_1))
            .add(RegexConstraint.parse(plain_comm_2))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(configs.values(), communityRegexes);
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Network(tbdd, configs, imports, exports);
  }

  @Test
  public void originalExampleTest() {
    NodeRecord ALPHANODE_rec = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_rec = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_rec = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTANODE_rec = new NodeRecord("10.0.0.4", "deltaNode");

    TestConfigConstructionUtils.Network net =
        originalExample(ALPHANODE_rec, BETANODE_rec, GAMMANODE_rec, DELTANODE_rec);

    NetworkInfo info_1 = net.getInfo();

    Node ALPHANODE = ALPHANODE_rec.instantiate(info_1);
    Node BETANODE = BETANODE_rec.instantiate(info_1);
    Node GAMMANODE = GAMMANODE_rec.instantiate(info_1);
    Node DELTANODE = DELTANODE_rec.instantiate(info_1);

    info_1.anyRouteAllowedAt(ALPHANODE);
    Infer verifier_1 = info_1.toInfer();
    Invariant property_1 =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net.tbdd(), net.imports().get(DELTANODE_rec)));
    verifier_1.addProperty(DELTANODE, property_1);
    Infer.Result result_1 = verifier_1.run();
    assertTrue(result_1.verified);

    NetworkInfo info_2 = net.getInfo();
    info_2.anyRouteAllowedAt(new Edge(ALPHANODE, BETANODE));
    Infer verifier_2 = info_2.toInfer();
    Invariant property_2 =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net.tbdd(), net.imports().get(DELTANODE_rec)));
    verifier_2.addProperty(DELTANODE, property_2);
    Infer.Result result_2 = verifier_2.run();
    assertFalse(result_2.verified);

    NetworkInfo info_3 = net.getInfo();
    info_3.anyRouteAllowedAt(ALPHANODE);
    Infer verifier_3 = info_3.toInfer();
    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("100:2")));
    Invariant property_3 =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .setCommunities(comm)
                .build(net.tbdd(), net.imports().get(DELTANODE_rec)));
    verifier_3.addProperty(DELTANODE, property_3);
    Infer.Result result_3 = verifier_3.run();
    assertFalse(result_3.verified);

    NetworkInfo info_4 = net.getInfo();
    info_4.anyRouteAllowedAt(ALPHANODE);
    Infer verifier_4 = info_4.toInfer();
    RegexConstraints comm_ =
        new RegexConstraints(
            List.of(RegexConstraint.parse("100:1"), RegexConstraint.parse("!100:2")));
    Invariant property_4 =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .setCommunities(comm_)
                .build(net.tbdd(), net.imports().get(DELTANODE_rec)));
    verifier_4.addProperty(DELTANODE, property_4);
    Infer.Result result_4 = verifier_4.run();
    assertFalse(result_4.verified);

    NetworkInfo info_5 = net.getInfo();
    info_5.anyRouteAllowedAt(ALPHANODE);
    Infer verifier_5 = info_5.toInfer();
    RegexConstraints comm__ =
        new RegexConstraints(
            List.of(RegexConstraint.parse("100:1"), RegexConstraint.parse("!100:2")));
    Invariant property_5 =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .setCommunities(comm__)
                .build(net.tbdd(), net.imports().get(GAMMANODE_rec)));
    verifier_5.addProperty(GAMMANODE, property_5);
    Infer.Result result_5 = verifier_5.run();
    assertFalse(result_5.verified);
  }

  @Test
  public void originalExampleInvariantsAsExpectedTest() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.10", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.20", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.30", "gammaNode");
    NodeRecord DELTANODE_R = new NodeRecord("10.0.0.40", "deltaNode");
    TestConfigConstructionUtils.Network net =
        originalExample(ALPHANODE_R, BETANODE_R, GAMMANODE_R, DELTANODE_R);

    NetworkInfo info = net.getInfo();

    Node ALPHANODE = ALPHANODE_R.instantiate(info);
    Node BETANODE = BETANODE_R.instantiate(info);
    Node GAMMANODE = GAMMANODE_R.instantiate(info);
    Node DELTANODE = DELTANODE_R.instantiate(info);

    info.anyRouteAllowedAt(ALPHANODE);
    Infer verifier = info.toInfer();
    Invariant property =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net.tbdd(), net.imports().get(DELTANODE_R)));
    verifier.addProperty(DELTANODE, property);
    Infer.Result result = verifier.run();
    Map<Location, Invariant> inferred = result.invariants;

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
    Invariant betaNode = prefix_implies_100_1_2.build(net.tbdd(), net.imports().get(BETANODE_R));
    Invariant gammaNode = prefix_implies_100_2.build(net.tbdd(), net.imports().get(GAMMANODE_R));
    Invariant deltaNode = not_prefix.build(net.tbdd(), net.imports().get(DELTANODE_R));

    // Edge Invariants
    Invariant alpha_beta = prefix_implies_100_1_2.build(net.tbdd(), net.exports().get(ALPHANODE_R));
    Invariant beta_gamma = prefix_implies_100_2.build(net.tbdd(), net.exports().get(BETANODE_R));
    Invariant gamma_beta = prefix_implies_100_1_2.build(net.tbdd(), net.exports().get(GAMMANODE_R));
    Invariant gamma_delta = not_prefix.build(net.tbdd(), net.exports().get(GAMMANODE_R));
    Invariant delta_gamma = prefix_implies_100_2.build(net.tbdd(), net.exports().get(DELTANODE_R));

    assertEquals(10, inferred.size());

    // Node Checks -- all off by one?
    assertTrue(inferred.get(ALPHANODE).isTrue());
    assertEquals(inferred.get(BETANODE), betaNode);
    assertEquals(inferred.get(GAMMANODE), gammaNode);
    assertEquals(inferred.get(DELTANODE), deltaNode);

    // Edge Checks
    assertEquals(inferred.get(new Edge(GAMMANODE, DELTANODE)), gamma_delta);
    assertEquals(inferred.get(new Edge(DELTANODE, GAMMANODE)), delta_gamma);
    assertEquals(inferred.get(new Edge(BETANODE, GAMMANODE)), beta_gamma);
    assertEquals(inferred.get(new Edge(ALPHANODE, BETANODE)), alpha_beta);
    assertEquals(inferred.get(new Edge(GAMMANODE, BETANODE)), gamma_beta);
    assertTrue(inferred.get(new Edge(BETANODE, ALPHANODE)).isTrue());
  }

  private TestConfigConstructionUtils.Network faultyOriginalExample(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      NodeRecord DELTANODE,
      int faulty) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> imports = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> exports = new HashMap<>();

    String plain_comm_1 = "100:1";
    String plain_comm_2 = "100:2";
    String plain_comm_3 = "100:3";
    String regex_comm_100_1 = "^" + plain_comm_1 + "$";
    String regex_comm_100_2 = "^" + plain_comm_2 + "$";
    String regex_comm_100_3 = "^" + plain_comm_3 + "$";

    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_MATCH,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixStr)))));

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE);

    includeCommunities(configs.get(ALPHANODE), faulty == 4 ? regex_comm_100_3 : regex_comm_100_1);
    configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));
    includeCommunities(
        configs.get(BETANODE), regex_comm_100_1, faulty == 5 ? regex_comm_100_3 : regex_comm_100_2);
    includeCommunities(configs.get(GAMMANODE), faulty == 3 ? regex_comm_100_3 : regex_comm_100_2);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                DELTANODE.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(DELTANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    // Create the policies
    RoutingPolicy alphaImport =
        makePolicy(configs.get(ALPHANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy alphaExport =
        makePolicy(
            configs.get(ALPHANODE),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForPrefixListMatch(PREFIX_MATCH),
                replaceCommunities(faulty == 4 ? plain_comm_3 : plain_comm_1),
                permitRoute(true)));

    RoutingPolicy betaImport =
        makePolicy(configs.get(BETANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy betaExport;
    if (faulty == 2) {
      betaExport = makePolicy(configs.get(BETANODE), EXPORT_POLICY_NAME, permitRoute(true));
    } else {
      betaExport =
          makePolicy(
              configs.get(BETANODE),
              EXPORT_POLICY_NAME,
              ifStatement(
                  checkForCommunity(plain_comm_1),
                  replaceCommunities(faulty == 5 ? plain_comm_3 : plain_comm_2),
                  permitRoute(true)));
    }

    RoutingPolicy gammaImport =
        makePolicy(configs.get(GAMMANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy gammaExport;
    if (faulty == 3) {
      gammaExport =
          makePolicy(
              configs.get(GAMMANODE),
              EXPORT_POLICY_NAME,
              ifStatement(checkForCommunity(plain_comm_3), permitRoute(false), permitRoute(true)));
    } else {
      gammaExport =
          makePolicy(
              configs.get(GAMMANODE),
              EXPORT_POLICY_NAME,
              ifStatement(
                  checkForCommunity(plain_comm_2),
                  permitRoute(faulty == 1),
                  permitRoute(faulty != 1)));
    }

    RoutingPolicy deltaImport =
        makePolicy(configs.get(DELTANODE), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy deltaExport =
        makePolicy(configs.get(DELTANODE), EXPORT_POLICY_NAME, permitRoute(true));

    // Store the policies
    imports.put(ALPHANODE, alphaImport);
    imports.put(BETANODE, betaImport);
    imports.put(GAMMANODE, gammaImport);
    imports.put(DELTANODE, deltaImport);

    exports.put(ALPHANODE, alphaExport);
    exports.put(BETANODE, betaExport);
    exports.put(GAMMANODE, gammaExport);
    exports.put(DELTANODE, deltaExport);

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(plain_comm_1))
            .add(RegexConstraint.parse(plain_comm_2))
            .add(RegexConstraint.parse(plain_comm_3))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(configs.values(), communityRegexes);
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Network(tbdd, configs, imports, exports);
  }

  @Test
  public void faultyOriginalExampleTest() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.11", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.22", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.33", "gammaNode");
    NodeRecord DELTANODE_R = new NodeRecord("10.0.0.44", "deltaNode");
    Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);

    for (int i = 1; i <= 5; i++) {
      TestConfigConstructionUtils.Network net =
          faultyOriginalExample(ALPHANODE_R, BETANODE_R, GAMMANODE_R, DELTANODE_R, i);
      Invariant property =
          new Invariant(
              net.tbdd(),
              Invariant.clauseBuilder()
                  .avoidPrefix(PREFIX)
                  .build(net.tbdd(), net.imports().get(DELTANODE_R)));
      Invariant not_prefix =
          Invariant.builder()
              .addClause(avoidPrefix)
              .build(net.tbdd(), net.imports().get(ALPHANODE_R));

      NetworkInfo info = net.getInfo();

      Node ALPHANODE = ALPHANODE_R.instantiate(info);
      Node DELTANODE = DELTANODE_R.instantiate(info);

      info.anyRouteAllowedAt(ALPHANODE);
      Infer verifier = info.toInfer();
      verifier.addProperty(DELTANODE, property);
      Infer.Result result = verifier.run();
      assertFalse(result.verified);
      assertEquals(result.invariants.get(DELTANODE), not_prefix);
    }
  }

  private TestConfigConstructionUtils.Network meshNetworkExample(
      NodeRecord A1,
      NodeRecord B1,
      NodeRecord G1,
      NodeRecord D1,
      NodeRecord A2,
      NodeRecord B2,
      NodeRecord G2,
      NodeRecord D2,
      int faulty) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> imports = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> exports = new HashMap<>();

    String plain_comm_1 = "100:1";
    String plain_comm_2 = "100:2";
    String plain_comm_3 = "100:3";
    String regex_comm_100_1 = "^" + plain_comm_1 + "$";
    String regex_comm_100_2 = "^" + plain_comm_2 + "$";
    String regex_comm_100_3 = "^" + plain_comm_3 + "$";

    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_MATCH,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixStr)))));

    // Set up the configs and add what features they know about
    setUpConfigs(configs, A1, B1, G1, D1, A2, B2, G2, D2);

    includeCommunities(configs.get(A1), regex_comm_100_1);
    configs.get(A1).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));
    includeCommunities(configs.get(B1), regex_comm_100_1, regex_comm_100_2);
    includeCommunities(configs.get(G1), regex_comm_100_2);

    includeCommunities(configs.get(A2), faulty == 3 ? regex_comm_100_3 : regex_comm_100_1);
    configs.get(A2).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));
    includeCommunities(
        configs.get(B2), regex_comm_100_1, faulty == 2 ? regex_comm_100_3 : regex_comm_100_2);
    includeCommunities(configs.get(G2), faulty == 3 ? regex_comm_100_1 : regex_comm_100_2);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, A1, B1, G1, D1, A2, B2, G2, D2);

    processes
        .get(A1)
        .setNeighbors(
            ImmutableSortedMap.of(
                B1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                B2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(A2)
        .setNeighbors(
            ImmutableSortedMap.of(
                B1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                B2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(B1)
        .setNeighbors(
            ImmutableSortedMap.of(
                A1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                A2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                G1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                G2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(B2)
        .setNeighbors(
            ImmutableSortedMap.of(
                A1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                A2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                G1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                G2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(G1)
        .setNeighbors(
            ImmutableSortedMap.of(
                B1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                B2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                D1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                D2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(G2)
        .setNeighbors(
            ImmutableSortedMap.of(
                B1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                B2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                D1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                D2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(D1)
        .setNeighbors(
            ImmutableSortedMap.of(
                G1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                G2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(D2)
        .setNeighbors(
            ImmutableSortedMap.of(
                G1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                G2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    // Create the policies
    RoutingPolicy a1_Import = makePolicy(configs.get(A1), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy a1_Export =
        makePolicy(
            configs.get(A1),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForPrefixListMatch(PREFIX_MATCH),
                replaceCommunities(plain_comm_1),
                permitRoute(true)));

    RoutingPolicy a2_Import = makePolicy(configs.get(A2), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy a2_Export =
        makePolicy(
            configs.get(A2),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForPrefixListMatch(PREFIX_MATCH),
                replaceCommunities(faulty == 3 ? plain_comm_3 : plain_comm_1),
                permitRoute(true)));

    RoutingPolicy b1_Import = makePolicy(configs.get(B1), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy b1_Export =
        makePolicy(
            configs.get(B1),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_1),
                replaceCommunities(plain_comm_2),
                permitRoute(true)));

    RoutingPolicy b2_Import = makePolicy(configs.get(B2), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy b2_Export =
        makePolicy(
            configs.get(B2),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_1),
                replaceCommunities(faulty == 2 ? plain_comm_3 : plain_comm_2),
                permitRoute(true)));

    RoutingPolicy g1_Import = makePolicy(configs.get(G1), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy g1_Export =
        makePolicy(
            configs.get(G1),
            EXPORT_POLICY_NAME,
            ifStatement(checkForCommunity(plain_comm_2), permitRoute(false), permitRoute(true)));

    RoutingPolicy g2_Import = makePolicy(configs.get(G2), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy g2_Export =
        makePolicy(
            configs.get(G2),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(faulty == 3 ? plain_comm_1 : plain_comm_2),
                permitRoute(false),
                permitRoute(true)));

    RoutingPolicy d1_Import = makePolicy(configs.get(D1), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy d1_Export = makePolicy(configs.get(D1), EXPORT_POLICY_NAME, permitRoute(true));

    RoutingPolicy d2_Import = makePolicy(configs.get(D2), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy d2_Export = makePolicy(configs.get(D2), EXPORT_POLICY_NAME, permitRoute(true));

    // Store the policies
    imports.put(A1, a1_Import);
    imports.put(A2, a2_Import);
    imports.put(B1, b1_Import);
    imports.put(B2, b2_Import);
    imports.put(G1, g1_Import);
    imports.put(G2, g2_Import);
    imports.put(D1, d1_Import);
    imports.put(D2, d2_Import);

    exports.put(A1, a1_Export);
    exports.put(A2, a2_Export);
    exports.put(B1, b1_Export);
    exports.put(B2, b2_Export);
    exports.put(G1, g1_Export);
    exports.put(G2, g2_Export);
    exports.put(D1, d1_Export);
    exports.put(D2, d2_Export);

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(plain_comm_1))
            .add(RegexConstraint.parse(plain_comm_2))
            .add(RegexConstraint.parse(plain_comm_3))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(configs.values(), communityRegexes);
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Network(tbdd, configs, imports, exports);
  }

  @Test
  public void meshNetworkTest() {
    NodeRecord A1_R = new NodeRecord("100.0.0.11", "a1Node");
    NodeRecord B1_R = new NodeRecord("100.0.0.22", "b1Node");
    NodeRecord G1_R = new NodeRecord("100.0.0.33", "g1Node");
    NodeRecord D1_R = new NodeRecord("100.0.0.44", "d1Node");
    NodeRecord A2_R = new NodeRecord("101.0.0.11", "a2Node");
    NodeRecord B2_R = new NodeRecord("101.0.0.22", "b2Node");
    NodeRecord G2_R = new NodeRecord("101.0.0.33", "g2Node");
    NodeRecord D2_R = new NodeRecord("101.0.0.44", "d2Node");
    Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
    Invariant.ClauseBuilder match_100_1 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
    Invariant.ClauseBuilder match_100_2 =
        Invariant.clauseBuilder()
            .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));

    TestConfigConstructionUtils.Network net_0 =
        meshNetworkExample(A1_R, B1_R, G1_R, D1_R, A2_R, B2_R, G2_R, D2_R, 0);
    Invariant property_0 =
        new Invariant(
            net_0.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net_0.tbdd(), net_0.imports().get(D1_R)));

    NetworkInfo info_0 = net_0.getInfo();

    Node A1 = A1_R.instantiate(info_0);
    Node D1 = D1_R.instantiate(info_0);
    Node A2 = A2_R.instantiate(info_0);
    Node D2 = D2_R.instantiate(info_0);

    info_0.anyRouteAllowedAt(A1).anyRouteAllowedAt(A2);
    Infer verifier_0 = info_0.toInfer();
    verifier_0.addProperty(D1, property_0).addProperty(D2, property_0);
    Infer.Result result_0 = verifier_0.run();
    assertTrue(result_0.verified);

    TestConfigConstructionUtils.Network net_1 =
        meshNetworkExample(A1_R, B1_R, G1_R, D1_R, A2_R, B2_R, G2_R, D2_R, 1);
    Invariant property_1 =
        new Invariant(
            net_1.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net_1.tbdd(), net_1.imports().get(D1_R)));

    NetworkInfo info_1 = net_1.getInfo();

    A1 = A1_R.instantiate(info_1);
    D1 = D1_R.instantiate(info_1);
    A2 = A2_R.instantiate(info_1);

    info_1.anyRouteAllowedAt(A1).anyRouteAllowedAt(A2);
    Infer verifier_1 = info_1.toInfer();
    verifier_1.addProperty(D1, property_1);
    Infer.Result result_1 = verifier_1.run();
    assertTrue(result_1.verified);

    TestConfigConstructionUtils.Network net_2 =
        meshNetworkExample(A1_R, B1_R, G1_R, D1_R, A2_R, B2_R, G2_R, D2_R, 2);
    Invariant property_2 =
        new Invariant(
            net_2.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net_2.tbdd(), net_2.imports().get(D1_R)));
    Invariant not_prefix_2 =
        Invariant.builder().addClause(avoidPrefix).build(net_2.tbdd(), net_2.imports().get(A1_R));
    NetworkInfo info_2 = net_2.getInfo();

    A1 = A1_R.instantiate(info_2);
    D1 = D1_R.instantiate(info_2);
    A2 = A2_R.instantiate(info_2);
    D2 = D2_R.instantiate(info_2);

    info_2.anyRouteAllowedAt(A1).anyRouteAllowedAt(A2);
    Infer verifier_2 = info_2.toInfer();
    verifier_2.addProperty(D1, property_2).addProperty(D2, property_2);
    Infer.Result result_2 = verifier_2.run();
    assertFalse(result_2.verified);
    assertEquals(result_2.invariants.get(A1), not_prefix_2);
    assertEquals(result_2.invariants.get(A2), not_prefix_2);

    TestConfigConstructionUtils.Network net_3 =
        meshNetworkExample(A1_R, B1_R, G1_R, D1_R, A2_R, B2_R, G2_R, D2_R, 3);
    Invariant property_3 =
        new Invariant(
            net_3.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net_3.tbdd(), net_3.imports().get(D1_R)));
    Invariant not_prefix_3 =
        Invariant.builder().addClause(avoidPrefix).build(net_3.tbdd(), net_3.imports().get(A1_R));
    NetworkInfo info_3 = net_3.getInfo();

    A1 = A1_R.instantiate(info_3);
    D1 = D1_R.instantiate(info_3);
    A2 = A2_R.instantiate(info_3);
    D2 = D2_R.instantiate(info_3);

    info_3.anyRouteAllowedAt(A1).anyRouteAllowedAt(A2);
    Infer verifier_3 = info_3.toInfer();
    verifier_3.addProperty(D1, property_3).addProperty(D2, property_3);
    Infer.Result result_3 = verifier_3.run();
    assertFalse(result_3.verified);
    assertEquals(result_3.invariants.get(A1), not_prefix_3);
    assertEquals(result_3.invariants.get(A2), not_prefix_3);

    TestConfigConstructionUtils.Network net_4 =
        meshNetworkExample(A1_R, B1_R, G1_R, D1_R, A2_R, B2_R, G2_R, D2_R, 0);
    Invariant property_4 =
        new Invariant(
            net_4.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net_4.tbdd(), net_4.imports().get(D1_R)));
    Invariant property_alt =
        new Invariant(
            net_4.tbdd(),
            Invariant.clauseBuilder()
                .matchPrefix(PREFIX)
                .build(net_4.tbdd(), net_4.imports().get(D1_R)));
    Invariant expected =
        Invariant.builder()
            .addClause(Invariant.clauseBuilder().matchPrefix(PREFIX))
            .addClause(match_100_1)
            .addClause(match_100_2)
            .build(net_4.tbdd(), net_4.imports().get(A1_R));
    NetworkInfo info_4 = net_4.getInfo();

    A1 = A1_R.instantiate(info_4);
    D1 = D1_R.instantiate(info_4);
    A2 = A2_R.instantiate(info_4);
    D2 = D2_R.instantiate(info_4);

    info_4.anyRouteAllowedAt(A1).anyRouteAllowedAt(A2);
    Infer verifier_4 = info_4.toInfer();
    verifier_4.addProperty(D1, property_4).addProperty(D2, property_alt);
    Infer.Result result_4 = verifier_4.run();
    assertFalse(result_4.verified);
    assertEquals(result_4.invariants.get(A1), expected);
    assertEquals(result_4.invariants.get(A2), expected);
  }

  private TestConfigConstructionUtils.Network threeProngedNetwork(
      NodeRecord a0,
      NodeRecord b0,
      NodeRecord c0,
      NodeRecord node1,
      NodeRecord node2,
      NodeRecord node3,
      NodeRecord node4,
      int faulty) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> imports = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> exports = new HashMap<>();

    String plain_comm_1_10 = "1:10";
    String plain_comm_1_20 = "1:20";
    String plain_comm_1_30 = "1:30";
    String plain_comm_10_10 = "10:10";
    String plain_comm_10_20 = "10:20";
    String plain_comm_10_30 = "10:30";
    String plain_comm_20_10 = "20:10";
    String plain_comm_20_20 = "20:20";
    String plain_comm_20_30 = "20:30";
    String regex_comm_1_10 = "^" + plain_comm_1_10 + "$";
    String regex_comm_1_20 = "^" + plain_comm_1_20 + "$";
    String regex_comm_1_30 = "^" + plain_comm_1_30 + "$";
    String regex_comm_10_10 = "^" + plain_comm_10_10 + "$";
    String regex_comm_10_20 = "^" + plain_comm_10_20 + "$";
    String regex_comm_10_30 = "^" + plain_comm_10_30 + "$";
    String regex_comm_20_10 = "^" + plain_comm_20_10 + "$";
    String regex_comm_20_20 = "^" + plain_comm_20_20 + "$";
    String regex_comm_20_30 = "^" + plain_comm_20_30 + "$";

    setUpConfigs(configs, a0, b0, c0, node1, node2, node3, node4);

    includeCommunities(configs.get(a0), regex_comm_1_10);
    includeCommunities(configs.get(b0), regex_comm_1_20);
    includeCommunities(configs.get(c0), regex_comm_1_30);

    includeCommunities(
        configs.get(node1),
        regex_comm_1_10,
        regex_comm_1_20,
        regex_comm_1_30,
        regex_comm_10_10,
        regex_comm_10_20,
        regex_comm_10_30);
    includeCommunities(
        configs.get(node2),
        regex_comm_1_10,
        regex_comm_1_20,
        regex_comm_1_30,
        regex_comm_20_10,
        regex_comm_20_20,
        regex_comm_20_30);

    includeCommunities(
        configs.get(node3), regex_comm_10_10, regex_comm_10_30, regex_comm_20_10, regex_comm_20_30);

    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, a0, b0, c0, node1, node2, node3, node4);

    processes
        .get(a0)
        .setNeighbors(
            ImmutableSortedMap.of(
                node1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                node2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(b0)
        .setNeighbors(
            ImmutableSortedMap.of(
                node1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                node2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(c0)
        .setNeighbors(
            ImmutableSortedMap.of(
                node1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                node2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(node1)
        .setNeighbors(
            ImmutableSortedMap.of(
                a0.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                b0.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                c0.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                node3.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(node2)
        .setNeighbors(
            ImmutableSortedMap.of(
                a0.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                b0.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                c0.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                node3.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(node3)
        .setNeighbors(
            ImmutableSortedMap.of(
                node1.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                node2.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                node4.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(node4)
        .setNeighbors(
            ImmutableSortedMap.of(
                node3.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    RoutingPolicy a0_Import = makePolicy(configs.get(a0), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy a0_Export =
        makePolicy(configs.get(a0), EXPORT_POLICY_NAME, replaceCommunities(plain_comm_1_10));
    RoutingPolicy b0_Import = makePolicy(configs.get(b0), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy b0_Export =
        makePolicy(configs.get(b0), EXPORT_POLICY_NAME, replaceCommunities(plain_comm_1_20));
    RoutingPolicy c0_Import = makePolicy(configs.get(c0), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy c0_Export =
        makePolicy(configs.get(c0), EXPORT_POLICY_NAME, replaceCommunities(plain_comm_1_30));

    RoutingPolicy node1_Import =
        makePolicy(
            configs.get(node1),
            IMPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_1_10),
                addToCommunities(plain_comm_10_10),
                ifStatement(
                    checkForCommunity(plain_comm_1_20),
                    addToCommunities(plain_comm_10_20),
                    faulty == 2
                        ? permitRoute(true)
                        : ifStatement(
                            checkForCommunity(plain_comm_1_30),
                            addToCommunities(plain_comm_10_30),
                            permitRoute(true)))));
    RoutingPolicy node1_Export =
        makePolicy(configs.get(node1), EXPORT_POLICY_NAME, permitRoute(true));

    RoutingPolicy node2_Import =
        makePolicy(
            configs.get(node2),
            IMPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_1_10),
                addToCommunities(plain_comm_20_10),
                ifStatement(
                    checkForCommunity(plain_comm_1_20),
                    addToCommunities(plain_comm_20_20),
                    ifStatement(
                        checkForCommunity(plain_comm_1_30),
                        addToCommunities(plain_comm_20_30),
                        permitRoute(true)))));
    RoutingPolicy node2_Export =
        makePolicy(
            configs.get(node2),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_20_10),
                permitRoute(true),
                ifStatement(
                    checkForCommunity(plain_comm_20_30), permitRoute(true), permitRoute(false))));

    RoutingPolicy node3_Import =
        makePolicy(configs.get(node3), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node3_Export =
        makePolicy(
            configs.get(node3),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_10_10),
                permitRoute(false),
                ifStatement(
                    checkForCommunity(plain_comm_10_30),
                    permitRoute(faulty == 1),
                    ifStatement(
                        checkForCommunity(plain_comm_20_10),
                        permitRoute(false),
                        ifStatement(
                            checkForCommunity(plain_comm_20_30),
                            permitRoute(false),
                            permitRoute(true))))));

    RoutingPolicy node4_Import =
        makePolicy(configs.get(node4), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node4_Export =
        makePolicy(configs.get(node4), EXPORT_POLICY_NAME, permitRoute(true));

    imports.put(a0, a0_Import);
    imports.put(b0, b0_Import);
    imports.put(c0, c0_Import);
    imports.put(node1, node1_Import);
    imports.put(node2, node2_Import);
    imports.put(node3, node3_Import);
    imports.put(node4, node4_Import);

    exports.put(a0, a0_Export);
    exports.put(b0, b0_Export);
    exports.put(c0, c0_Export);
    exports.put(node1, node1_Export);
    exports.put(node2, node2_Export);
    exports.put(node3, node3_Export);
    exports.put(node4, node4_Export);

    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(plain_comm_1_10))
            .add(RegexConstraint.parse(plain_comm_1_20))
            .add(RegexConstraint.parse(plain_comm_1_30))
            .add(RegexConstraint.parse(plain_comm_10_10))
            .add(RegexConstraint.parse(plain_comm_10_20))
            .add(RegexConstraint.parse(plain_comm_10_30))
            .add(RegexConstraint.parse(plain_comm_20_10))
            .add(RegexConstraint.parse(plain_comm_20_20))
            .add(RegexConstraint.parse(plain_comm_20_30))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(configs.values(), communityRegexes);
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Network(tbdd, configs, imports, exports);
  }

  @Test
  public void threeProngedNetworkTest() {
    NodeRecord A0_R = new NodeRecord("100.0.1.11", "entryA");
    NodeRecord B0_R = new NodeRecord("100.0.1.22", "entryB");
    NodeRecord C0_R = new NodeRecord("100.0.1.33", "entryC");
    NodeRecord NODE1_R = new NodeRecord("100.0.1.44", "node_1");
    NodeRecord NODE2_R = new NodeRecord("101.0.1.11", "node_2");
    NodeRecord NODE3_R = new NodeRecord("101.0.1.22", "node_3");
    NodeRecord NODE4_R = new NodeRecord("101.0.1.33", "node_4");

    Invariant.ClauseBuilder avoidBoth =
        Invariant.clauseBuilder()
            .setCommunities(
                new RegexConstraints(
                    List.of(RegexConstraint.parse("!1:10"), RegexConstraint.parse("!1:30"))));

    TestConfigConstructionUtils.Network net_0 =
        threeProngedNetwork(A0_R, B0_R, C0_R, NODE1_R, NODE2_R, NODE3_R, NODE4_R, 0);
    Invariant property_0 =
        Invariant.builder().addClause(avoidBoth).build(net_0.tbdd(), net_0.imports().get(NODE4_R));
    NetworkInfo info_0 = net_0.getInfo();

    Node NODE4 = NODE4_R.instantiate(info_0);

    Infer verifier_0 = info_0.toInfer();
    verifier_0.addProperty(NODE4, property_0);
    Infer.Result result_0 = verifier_0.run();
    assertTrue(result_0.verified);

    TestConfigConstructionUtils.Network net_1 =
        threeProngedNetwork(A0_R, B0_R, C0_R, NODE1_R, NODE2_R, NODE3_R, NODE4_R, 1);
    Invariant property_1 =
        Invariant.builder().addClause(avoidBoth).build(net_1.tbdd(), net_1.imports().get(NODE4_R));
    NetworkInfo info_1 = net_1.getInfo();

    Node A0 = A0_R.instantiate(info_1);
    Node B0 = B0_R.instantiate(info_1);
    Node C0 = C0_R.instantiate(info_1);
    NODE4 = NODE4_R.instantiate(info_1);

    info_1.anyRouteAllowedAt(A0).anyRouteAllowedAt(B0).anyRouteAllowedAt(C0);
    Infer verifier_1 = info_1.toInfer();
    verifier_1.addProperty(NODE4, property_1);
    Infer.Result result_1 = verifier_1.run();
    assertFalse(result_1.verified);
    assertTrue(result_1.invariants.get(C0).isFalse());
    assertTrue(result_1.counter.isPresent());

    TestConfigConstructionUtils.Network net_2 =
        threeProngedNetwork(A0_R, B0_R, C0_R, NODE1_R, NODE2_R, NODE3_R, NODE4_R, 2);
    Invariant property_2 =
        Invariant.builder().addClause(avoidBoth).build(net_2.tbdd(), net_2.imports().get(NODE4_R));
    NetworkInfo info_2 = net_2.getInfo();

    A0 = A0_R.instantiate(info_2);
    B0 = B0_R.instantiate(info_2);
    C0 = C0_R.instantiate(info_2);
    NODE4 = NODE4_R.instantiate(info_2);

    info_2.anyRouteAllowedAt(A0).anyRouteAllowedAt(B0).anyRouteAllowedAt(C0);
    Infer verifier_2 = info_2.toInfer();
    verifier_2.addProperty(NODE4, property_2);
    Infer.Result result_2 = verifier_2.run();
    assertFalse(result_2.verified);
    assertTrue(result_2.invariants.get(C0).isFalse());
    assertTrue(result_2.counter.isPresent());
  }

  private TestConfigConstructionUtils.Network twoPathNetwork(
      NodeRecord NODE_1A,
      NodeRecord NODE_1B,
      NodeRecord NODE_2A,
      NodeRecord NODE_2B,
      NodeRecord NODE_3,
      NodeRecord NODE_4,
      int faulty) {
    // Initialize constants
    Map<NodeRecord, Configuration> configs = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> imports = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> exports = new HashMap<>();

    String plain_comm_1 = "100:1";
    String plain_comm_2 = "100:2";
    String plain_comm_3 = "100:3";

    String regex_comm_100_1 = "^" + plain_comm_1 + "$";
    String regex_comm_100_2 = "^" + plain_comm_2 + "$";
    String regex_comm_100_3 = "^" + plain_comm_3 + "$";

    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_MATCH,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));

    // Create configs
    setUpConfigs(configs, NODE_1A, NODE_1B, NODE_2A, NODE_2B, NODE_3, NODE_4);

    includeCommunities(configs.get(NODE_1A), regex_comm_100_1);
    configs.get(NODE_1A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));

    includeCommunities(configs.get(NODE_1B), regex_comm_100_1);
    configs.get(NODE_1B).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));

    includeCommunities(configs.get(NODE_2A), regex_comm_100_1, regex_comm_100_2);

    if (faulty == 1 || faulty == 2) {
      includeCommunities(configs.get(NODE_2B), regex_comm_100_1, regex_comm_100_3);
    } else {
      includeCommunities(configs.get(NODE_2B), regex_comm_100_1, regex_comm_100_2);
    }

    if (faulty == 2) {
      includeCommunities(configs.get(NODE_3), regex_comm_100_2, regex_comm_100_3);
    } else {
      includeCommunities(configs.get(NODE_3), regex_comm_100_2);
    }

    // Create BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, NODE_1A, NODE_1B, NODE_2A, NODE_2B, NODE_3, NODE_4);

    processes
        .get(NODE_1A)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_2A.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(NODE_2A)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_1A.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                NODE_3.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(NODE_1B)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_2B.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
    processes
        .get(NODE_2B)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_1B.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                NODE_3.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(NODE_3)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_4.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                NODE_2A.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                NODE_2B.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(NODE_4)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_3.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    // Create policies
    RoutingPolicy node_1A_import =
        makePolicy(configs.get(NODE_1A), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node_1A_export =
        makePolicy(
            configs.get(NODE_1A),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForPrefixListMatch(PREFIX_MATCH),
                replaceCommunities(plain_comm_1),
                permitRoute(true)));

    RoutingPolicy node_1B_import =
        makePolicy(configs.get(NODE_1B), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node_1B_export =
        makePolicy(
            configs.get(NODE_1B),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForPrefixListMatch(PREFIX_MATCH),
                replaceCommunities(plain_comm_1),
                permitRoute(true)));

    RoutingPolicy node_2A_import =
        makePolicy(configs.get(NODE_2A), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node_2A_export =
        makePolicy(
            configs.get(NODE_2A),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_1),
                replaceCommunities(plain_comm_2),
                permitRoute(true)));

    RoutingPolicy node_2B_import =
        makePolicy(configs.get(NODE_2B), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node_2B_export =
        makePolicy(
            configs.get(NODE_2B),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_1),
                replaceCommunities(faulty == 1 || faulty == 2 ? plain_comm_3 : plain_comm_2),
                permitRoute(true)));

    RoutingPolicy node_3_import =
        makePolicy(configs.get(NODE_3), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node_3_export =
        makePolicy(
            configs.get(NODE_3),
            EXPORT_POLICY_NAME,
            ifStatement(
                checkForCommunity(plain_comm_2),
                permitRoute(false),
                faulty == 2
                    ? ifStatement(
                        checkForCommunity(plain_comm_3), permitRoute(false), permitRoute(true))
                    : permitRoute(true)));

    RoutingPolicy node_4_import =
        makePolicy(configs.get(NODE_4), IMPORT_POLICY_NAME, permitRoute(true));
    RoutingPolicy node_4_export =
        makePolicy(configs.get(NODE_4), EXPORT_POLICY_NAME, permitRoute(true));

    // Store the policies
    imports.put(NODE_1A, node_1A_import);
    imports.put(NODE_1B, node_1B_import);
    imports.put(NODE_2A, node_2A_import);
    imports.put(NODE_2B, node_2B_import);
    imports.put(NODE_3, node_3_import);
    imports.put(NODE_4, node_4_import);

    exports.put(NODE_1A, node_1A_export);
    exports.put(NODE_1B, node_1B_export);
    exports.put(NODE_2A, node_2A_export);
    exports.put(NODE_2B, node_2B_export);
    exports.put(NODE_3, node_3_export);
    exports.put(NODE_4, node_4_export);

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(plain_comm_1))
            .add(RegexConstraint.parse(plain_comm_2))
            .add(RegexConstraint.parse(plain_comm_3))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(configs.values(), communityRegexes);
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Network(tbdd, configs, imports, exports);
  }

  @Test
  public void originalTwoPathNetworkTest() {
    String prefix = "25.13.0.0/16";
    PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefix)));

    NodeRecord NODE_1A_R = new NodeRecord("10.0.1.1", "node_1_a");
    NodeRecord NODE_1B_R = new NodeRecord("10.0.1.2", "node_1_b");
    NodeRecord NODE_2A_R = new NodeRecord("10.0.2.1", "node_2_a");
    NodeRecord NODE_2B_R = new NodeRecord("10.0.2.2", "node_2_b");
    NodeRecord NODE_3_R = new NodeRecord("10.0.3.0", "node_3_");
    NodeRecord NODE_4_R = new NodeRecord("10.0.4.0", "node_4_");

    TestConfigConstructionUtils.Network net =
        twoPathNetwork(NODE_1A_R, NODE_1B_R, NODE_2A_R, NODE_2B_R, NODE_3_R, NODE_4_R, 0);
    NetworkInfo info = net.getInfo();

    Node NODE_1A = NODE_1A_R.instantiate(info);
    Node NODE_1B = NODE_1B_R.instantiate(info);
    Node NODE_4 = NODE_4_R.instantiate(info);

    info.anyRouteAllowedAt(NODE_1A).anyRouteAllowedAt(NODE_1B);
    Infer verifier = info.toInfer();
    Invariant property =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net.tbdd(), net.imports().get(NODE_4_R)));
    verifier.addProperty(NODE_4, property);
    Infer.Result result = verifier.run();
    assertTrue(result.verified);
    assertTrue(result.inferredTrue());
    assertTrue(result.counter.isEmpty());

    TestConfigConstructionUtils.Network net_1 =
        twoPathNetwork(NODE_1A_R, NODE_1B_R, NODE_2A_R, NODE_2B_R, NODE_3_R, NODE_4_R, 1);
    NetworkInfo info_1 = net_1.getInfo();

    NODE_1A = NODE_1A_R.instantiate(info_1);
    NODE_1B = NODE_1B_R.instantiate(info_1);
    NODE_4 = NODE_4_R.instantiate(info_1);

    info_1.anyRouteAllowedAt(NODE_1A).anyRouteAllowedAt(NODE_1B);
    Infer verifier_1 = info_1.toInfer();
    Invariant property_1 =
        new Invariant(
            net_1.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net_1.tbdd(), net_1.imports().get(NODE_4_R)));
    verifier_1.addProperty(NODE_4, property_1);
    Infer.Result result_1 = verifier_1.run();
    assertFalse(result_1.verified);
    assertTrue(result_1.inferredTrue());
    assertTrue(result_1.counter.isEmpty());

    TestConfigConstructionUtils.Network net_2 =
        twoPathNetwork(NODE_1A_R, NODE_1B_R, NODE_2A_R, NODE_2B_R, NODE_3_R, NODE_4_R, 2);
    NetworkInfo info_2 = net_2.getInfo();

    NODE_1A = NODE_1A_R.instantiate(info_2);
    NODE_1B = NODE_1B_R.instantiate(info_2);
    NODE_4 = NODE_4_R.instantiate(info_2);

    info_2.anyRouteAllowedAt(NODE_1A).anyRouteAllowedAt(NODE_1B);
    Infer verifier_2 = info_2.toInfer();
    Invariant property_2 =
        new Invariant(
            net_2.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net_2.tbdd(), net_2.imports().get(NODE_4_R)));
    verifier_2.addProperty(NODE_4, property_2);
    Infer.Result result_2 = verifier_2.run();
    assertTrue(result_2.verified);
    assertTrue(result_2.inferredTrue());
    assertTrue(result_2.counter.isEmpty());
  }

  private TestConfigConstructionUtils.Network simpleNetwork(
      Ip entry, Ip exit, NodeRecord NODE_A, NodeRecord NODE_B, NodeRecord NODE_C, int faulty) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> imports = new HashMap<>();
    Map<NodeRecord, RoutingPolicy> exports = new HashMap<>();

    String plain_comm_1 = "100:1";
    String plain_comm_2 = "100:2";

    String regex_comm_100_1 = "^" + plain_comm_1 + "$";
    String regex_comm_100_2 = "^" + plain_comm_2 + "$";

    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_MATCH,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));

    // Create configs
    setUpConfigs(configs, NODE_A, NODE_B, NODE_C);

    if (faulty == 2) {
      includeCommunities(configs.get(NODE_A), regex_comm_100_2);
    } else if (faulty != 1) {
      includeCommunities(configs.get(NODE_A), regex_comm_100_1);
    }
    configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));

    includeCommunities(configs.get(NODE_C), regex_comm_100_1);
    if (faulty == 5) {
      includeCommunities(configs.get(NODE_A), regex_comm_100_2);
    } else if (faulty != 6) {
      includeCommunities(configs.get(NODE_A), regex_comm_100_1);
    }

    // Create BGP processes
    Map<NodeRecord, BgpProcess> processes = getBgpProcesses(configs, NODE_A, NODE_B, NODE_C);

    processes
        .get(NODE_A)
        .setNeighbors(
            ImmutableSortedMap.of(
                entry,
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                NODE_B.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(NODE_B)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_A.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                NODE_C.getIp(),
                    getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    processes
        .get(NODE_C)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_B.getIp(),
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                exit,
                getBgpActivePeerConfig(NEXT_DOOR, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));

    // Creating routing policy
    RoutingPolicy node_A_import;
    RoutingPolicy node_A_export;
    RoutingPolicy node_B_import;
    RoutingPolicy node_B_export;
    RoutingPolicy node_C_import;
    RoutingPolicy node_C_export;

    node_A_import =
        faulty == 1
            ? makePolicy(configs.get(NODE_A), IMPORT_POLICY_NAME, permitRoute(true))
            : makePolicy(
                configs.get(NODE_A),
                IMPORT_POLICY_NAME,
                ifStatement(
                    checkForPrefixListMatch(PREFIX_MATCH),
                    faulty == 7
                        ? addToCommunities(plain_comm_2)
                        : replaceCommunities(faulty == 2 ? plain_comm_2 : plain_comm_1),
                    permitRoute(true)));
    node_A_export = makePolicy(configs.get(NODE_A), EXPORT_POLICY_NAME, permitRoute(true));

    node_B_import = makePolicy(configs.get(NODE_B), IMPORT_POLICY_NAME, permitRoute(true));
    // if faulty == 3, this export should clear communities
    node_B_export = makePolicy(configs.get(NODE_B), EXPORT_POLICY_NAME, permitRoute(true));

    if (faulty == 5) {
      node_C_import =
          makePolicy(
              configs.get(NODE_C),
              IMPORT_POLICY_NAME,
              ifStatement(checkForCommunity(plain_comm_2), permitRoute(false), permitRoute(true)));
    } else if (faulty == 6 || faulty == 8) {
      node_C_import = makePolicy(configs.get(NODE_C), IMPORT_POLICY_NAME, permitRoute(true));
    } else {
      node_C_import =
          makePolicy(
              configs.get(NODE_C),
              IMPORT_POLICY_NAME,
              ifStatement(
                  checkForCommunity(plain_comm_1),
                  permitRoute(faulty == 4),
                  permitRoute(faulty != 4)));
    }
    if (faulty == 8) {
      node_C_export =
          makePolicy(
              configs.get(NODE_C),
              EXPORT_POLICY_NAME,
              ifStatement(checkForCommunity(plain_comm_1), permitRoute(false), permitRoute(true)));
    } else {
      node_C_export = makePolicy(configs.get(NODE_C), EXPORT_POLICY_NAME, permitRoute(true));
    }

    // Store the policies
    imports.put(NODE_A, node_A_import);
    imports.put(NODE_B, node_B_import);
    imports.put(NODE_C, node_C_import);

    exports.put(NODE_A, node_A_export);
    exports.put(NODE_B, node_B_export);
    exports.put(NODE_C, node_C_export);

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(plain_comm_1))
            .add(RegexConstraint.parse(plain_comm_2))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(configs.values(), communityRegexes);
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Network(tbdd, configs, imports, exports);
  }

  @Test
  public void simpleNetworkTest() {
    String prefix = "25.13.0.0/16";
    PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefix)));

    Ip entry = Ip.parse("10.10.0.0");
    Ip exit = Ip.parse("10.10.10.0");
    NodeRecord NODE_A_R = new NodeRecord("10.10.0.1", "node_A");
    NodeRecord NODE_B_R = new NodeRecord("10.10.0.2", "node_B");
    NodeRecord NODE_C_R = new NodeRecord("10.10.0.3", "node_C");

    TestConfigConstructionUtils.Network net =
        simpleNetwork(entry, exit, NODE_A_R, NODE_B_R, NODE_C_R, 0);
    NetworkInfo info = net.getInfo();

    Node NODE_C = NODE_C_R.instantiate(info);

    info.addAssumption(
        info.checkForEdgeViaIps(exit, NODE_C.getSingleIp()).get(), Invariant.getFalse(net.tbdd()));
    Infer verifier = info.toInfer();
    Invariant property =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .avoidPrefix(PREFIX)
                .build(net.tbdd(), net.imports().get(NODE_C_R)));
    Location.Builder edgeBuilder =
        new Location.Builder(NODE_C_R.getIp().toString(), exit.toString(), null);

    Optional<Location> target = edgeBuilder.instantiate(info).stream().findFirst();
    // assert target.isPresent();

    verifier.addProperty(target.get(), property);
    Infer.Result result = verifier.run();

    assertTrue(result.verified);
    assertTrue(result.inferredTrue());
    assertTrue(result.counter.isEmpty());
  }
}
