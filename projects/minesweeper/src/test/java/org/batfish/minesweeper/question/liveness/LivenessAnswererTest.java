package org.batfish.minesweeper.question.liveness;

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
import org.batfish.datamodel.routing_policy.expr.LiteralLong;
import org.batfish.datamodel.routing_policy.statement.SetLocalPreference;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.replaceCommunities;
import static org.junit.Assert.assertTrue;

public class LivenessAnswererTest {
  private static final NetworkFactory nf = new NetworkFactory();
  private static final String prefixStr = "10.0.0.0/8";

  @Before
  public void setup() throws IOException {}

  private BgpProcess getBgpProcess(Configuration config, Node node) {
    Vrf vrf = nf.vrfBuilder().setOwner(config).setName(Configuration.DEFAULT_VRF_NAME).build();
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

  private void setUpConfigs(Map<Node, Configuration> configs, Node... nodes) {
    for (Node node : nodes) {
      Configuration.Builder configBuilder = nf.configurationBuilder().setHostname(node.getName());
      configs.put(
          node,
          configBuilder
              .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
              .setDefaultInboundAction(PERMIT)
              .build());
    }
  }

  private Map<Node, BgpProcess> getBgpProcesses(Map<Node, Configuration> configs, Node... nodes) {
    Map<Node, BgpProcess> processes = new HashMap<>();
    for (Node node : nodes) {
      processes.put(node, getBgpProcess(configs.get(node), node));
    }
    return processes;
  }

  private RoutingPolicy makePolicy(Configuration owner, String name, List<Statement> body) {
    return nf.routingPolicyBuilder().setOwner(owner).setName(name).setStatements(body).build();
  }

  private TestConfigConstructionUtils.Networkv2 initialExample(
      Node ALPHANODE,
      Node BETANODE,
      Node GAMMANODE,
      Node DELTANODE,
      Ip alphaIncoming,
      int variation) {
    Map<Node, Configuration> configs = new HashMap<>();

    String community = "2:2";
    String regex_community = "^" + community + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String externalImport = "incomingFromOutside";
    String exportBETA2GAMMA = "exportB2C";
    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE);

    includeCommunities(configs.get(ALPHANODE), regex_community);
    if (variation == 1) {
      includeCommunities(configs.get(BETANODE), regex_community);
    }

    // Create the BGP processes
    Map<Node, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalImport, exportDefault),
                BETANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getSingleIp(),
                    getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMANODE.getSingleIp(),
                    getBgpActivePeerConfig(
                        INTERNAL,
                        importDefault,
                        variation == 1 ? exportBETA2GAMMA : exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getSingleIp(),
                    getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTANODE.getSingleIp(),
                    getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(DELTANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getSingleIp(),
                    getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMANODE.getSingleIp(),
                    getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));

    // Create the policies
    makePolicy(configs.get(ALPHANODE), externalImport, addToCommunities(community));
    RoutingPolicy alphaDefaultImport =
        makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(BETANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));
    if (variation == 1) {
      makePolicy(configs.get(BETANODE), exportBETA2GAMMA, clearCommunities());
    }

    makePolicy(configs.get(GAMMANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(DELTANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(DELTANODE), exportDefault, permitRoute(true));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(community)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaDefaultImport, List.of());
  }

  @Test
  public void initialExampleTest() {
    Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
    Node BETANODE = new Node("10.0.0.2", "betaNode");
    Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
    Node DELTANODE = new Node("10.0.0.4", "deltaNode");
    Ip incoming = Ip.parse("100.0.0.10");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        initialExample(ALPHANODE, BETANODE, GAMMANODE, DELTANODE, incoming, 0);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("2:2")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));
    LivenessAnswerer.Result result = LivenessAnswerer.run(info, BASIC_PREFIX, GAMMANODE, target);

    assertTrue(result.goodPath().isPresent());
    assertTrue(result.potentialInterferences().isEmpty());
  }

  @Test
  public void initialExampleV1Test() {
    Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
    Node BETANODE = new Node("10.0.0.2", "betaNode");
    Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
    Node DELTANODE = new Node("10.0.0.4", "deltaNode");
    Ip incoming = Ip.parse("100.0.0.10");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        initialExample(ALPHANODE, BETANODE, GAMMANODE, DELTANODE, incoming, 1);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("2:2")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));
    LivenessAnswerer.Result result = LivenessAnswerer.run(info, BASIC_PREFIX, GAMMANODE, target);

    assertTrue(result.goodPath().isPresent());
    assertTrue(result.potentialInterferences().isPresent());
  }

  private TestConfigConstructionUtils.Networkv2 pathWithInterferenceExample(
      Node ALPHANODE,
      Node BETANODE,
      Node GAMMANODE,
      Ip alphaIncoming,
      Ip betaIncoming,
      String prefixString) {
    Map<Node, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";
    String community2 = "2:2";
    String regex_community2 = "^" + community2 + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String externalAlphaImport = "incomingFromOutsideAlpha";
    String externalBetaImport = "incomingFromOutsideBeta";
    String importALPHA2BETA = "importA2B";
    String importBETA2GAMMA = "importB2C";
    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    String PREFIX_LABEL = "prefixMatch";
    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_LABEL,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixString)))));

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE);

    includeCommunities(configs.get(ALPHANODE), regex_community1);
    configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(BETANODE), regex_community1, regex_community2);
    configs.get(BETANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(GAMMANODE), regex_community2);

    // Create the BGP processes
    Map<Node, BgpProcess> processes = getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalAlphaImport, exportDefault),
                BETANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importALPHA2BETA, exportDefault),
                GAMMANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                betaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalBetaImport, exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importBETA2GAMMA, exportDefault)));

    // Create the policies
    makePolicy(
        configs.get(ALPHANODE),
        externalAlphaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community1),
            clearCommunities()));
    makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));

    RoutingPolicy alphaBetaImport =
        makePolicy(
            configs.get(BETANODE),
            importALPHA2BETA,
            ifStatement(
                checkForCommunity(community1), addToCommunities(community2), permitRoute(true)));
    makePolicy(
        configs.get(BETANODE),
        externalBetaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community2),
            clearCommunities()));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));

    makePolicy(
        configs.get(GAMMANODE),
        importBETA2GAMMA,
        ifStatement(checkForCommunity(community2), permitRoute(true), permitRoute(false)));
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(community1))
            .add(RegexConstraint.parse(community2))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaBetaImport, List.of());
  }

  @Test
  public void pathWithInterferenceExampleTest() {
    Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
    Node BETANODE = new Node("10.0.0.2", "betaNode");
    Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    Ip incomingBeta = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithInterferenceExample(
            ALPHANODE, BETANODE, GAMMANODE, incomingAlpha, incomingBeta, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));
    LivenessAnswerer.Result result = LivenessAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target);

    assertTrue(result.goodPath().isPresent());
    assertTrue(result.potentialInterferences().isPresent());
  }

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceExample(
      Node ALPHANODE,
      Node BETANODE,
      Node GAMMANODE,
      Ip alphaIncoming,
      Ip betaIncoming,
      String prefixString) {
    Map<Node, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";
    String community2 = "2:2";
    String regex_community2 = "^" + community2 + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String externalAlphaImport = "incomingFromOutsideAlpha";
    String externalBetaImport = "incomingFromOutsideBeta";
    String importALPHA2BETA = "importA2B";
    String importBETA2GAMMA = "importB2C";
    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    String PREFIX_LABEL = "prefixMatch";
    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_LABEL,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixString)))));

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE);

    includeCommunities(configs.get(ALPHANODE), regex_community1);
    configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(BETANODE), regex_community1, regex_community2);
    configs.get(BETANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(GAMMANODE), regex_community2);

    // Create the BGP processes
    Map<Node, BgpProcess> processes = getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalAlphaImport, exportDefault),
                BETANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importALPHA2BETA, exportDefault),
                GAMMANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                betaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalBetaImport, exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getSingleIp(),
                getBgpActivePeerConfig(INTERNAL, importBETA2GAMMA, exportDefault)));

    // Create the policies
    makePolicy(
        configs.get(ALPHANODE),
        externalAlphaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community1),
            clearCommunities()));
    makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));

    // Import from ALPHA to BETA with HIGH local preference
    List<Statement> alphaBetaImportStatements =
        new java.util.ArrayList<>(
            TestConfigConstructionUtils.ifStatement(
                checkForCommunity(community1), addToCommunities(community2), permitRoute(true)));
    alphaBetaImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    RoutingPolicy alphaBetaImport =
        makePolicy(configs.get(BETANODE), importALPHA2BETA, alphaBetaImportStatements);

    // Import from external with default local preference of 100 (interfering route)
    makePolicy(
        configs.get(BETANODE),
        externalBetaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community2),
            clearCommunities()));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));

    makePolicy(
        configs.get(GAMMANODE),
        importBETA2GAMMA,
        ifStatement(checkForCommunity(community2), permitRoute(true), permitRoute(false)));
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(community1))
            .add(RegexConstraint.parse(community2))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaBetaImport, List.of());
  }

  @Test
  public void pathWithLocalPreferenceNoInterferenceTest() {
    Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
    Node BETANODE = new Node("10.0.0.2", "betaNode");
    Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    Ip incomingBeta = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceExample(
            ALPHANODE, BETANODE, GAMMANODE, incomingAlpha, incomingBeta, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));
    LivenessAnswerer.Result result = LivenessAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target);

    assertTrue(result.goodPath().isPresent());
    assertTrue(result.potentialInterferences().isEmpty());
  }
}
