package org.batfish.minesweeper.question.reachability;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.apache.commons.lang3.tuple.Pair;
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
import org.batfish.datamodel.routing_policy.statement.Statements;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
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
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ReachabilityAnswererTest {
  private static final NetworkFactory nf = new NetworkFactory();
  private static final String prefixStr = "10.0.0.0/8";

  @Before
  public void setup() throws IOException {}

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

  private Pair<Boolean, Boolean> processResultRows(List<Row> rows) {
    boolean goodPath = false;
    boolean interference = false;
    for (Row row : rows) {
      if (row.getString("Result_Label").equals("Good Path")) {
        goodPath = true;
      } else if (row.getString("Result_Label").startsWith("Potential Interference")) {
        interference = true;
      }
    }
    return Pair.of(goodPath, interference);
  }

  private TestConfigConstructionUtils.Networkv2 initialExample(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      NodeRecord DELTANODE,
      Ip alphaIncoming,
      int variation) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

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
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalImport, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(), getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMANODE.getIp(),
                    getBgpActivePeerConfig(
                        INTERNAL,
                        importDefault,
                        variation == 1 ? exportBETA2GAMMA : exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(), getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTANODE.getIp(), getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(DELTANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(), getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMANODE.getIp(), getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));

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
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTANODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    Ip incoming = Ip.parse("100.0.0.10");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        initialExample(ALPHANODE_R, BETANODE_R, GAMMANODE_R, DELTANODE_R, incoming, 0);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("2:2")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, BASIC_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertFalse(checks.getRight());
  }

  @Test
  public void initialExampleV1Test() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTANODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    Ip incoming = Ip.parse("100.0.0.10");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        initialExample(ALPHANODE_R, BETANODE_R, GAMMANODE_R, DELTANODE_R, incoming, 1);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("2:2")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, BASIC_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    // only good path is not the shortest path
    assertFalse(checks.getLeft());
    // assertTrue(checks.getLeft());
    // assertTrue(checks.getRight());
  }

  private TestConfigConstructionUtils.Networkv2 pathWithInterferenceExample(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      Ip alphaIncoming,
      Ip betaIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

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
    long betaAs = 65002L;
    long externalBetaAs = 65102L;

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
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalAlphaImport, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importALPHA2BETA, exportDefault),
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                betaIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(betaAs)
                    .setRemoteAs(externalBetaAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(externalBetaImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build()));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
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
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    Ip incomingBeta = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithInterferenceExample(
            ALPHANODE_R, BETANODE_R, GAMMANODE_R, incomingAlpha, incomingBeta, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceSingleNodeExample(
      NodeRecord TARGETNODE,
      Ip highPreferenceIncoming,
      Ip defaultPreferenceIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";

    String EXTERNAL = "externalNeighbor";

    String highPreferenceImport = "incomingHighLocalPref";
    String defaultPreferenceImport = "incomingDefaultLocalPref";
    String exportDefault = "defaultExportPolicy";
    long targetAs = 65003L;
    long highPreferenceSourceAs = 65101L;
    long defaultPreferenceSourceAs = 65102L;

    String PREFIX_LABEL = "prefixMatch";
    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_LABEL,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixString)))));

    setUpConfigs(configs, TARGETNODE);
    includeCommunities(configs.get(TARGETNODE), regex_community1);
    configs.get(TARGETNODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));

    Map<NodeRecord, BgpProcess> processes = getBgpProcesses(configs, TARGETNODE);
    processes
        .get(TARGETNODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                highPreferenceIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(targetAs)
                    .setRemoteAs(highPreferenceSourceAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(highPreferenceImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build(),
                defaultPreferenceIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(targetAs)
                    .setRemoteAs(defaultPreferenceSourceAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(defaultPreferenceImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build()));

    List<Statement> highPreferenceImportStatements =
        new java.util.ArrayList<>(
            ifStatement(
                checkForPrefixListMatch(PREFIX_LABEL),
                addToCommunities(community1),
                permitRoute(true)));
    highPreferenceImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    RoutingPolicy targetDefaultImport =
        makePolicy(configs.get(TARGETNODE), highPreferenceImport, highPreferenceImportStatements);
    makePolicy(configs.get(TARGETNODE), defaultPreferenceImport, permitRoute(true));
    makePolicy(configs.get(TARGETNODE), exportDefault, permitRoute(true));

    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(community1)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(
        tbdd, configs, targetDefaultImport, List.of());
  }

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceSingleNodeEqualExample(
      NodeRecord TARGETNODE,
      Ip highPreferenceIncoming,
      Ip defaultPreferenceIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";

    String EXTERNAL = "externalNeighbor";

    String highPreferenceImport = "incomingHighLocalPref";
    String equalPreferenceImport = "incomingEqualLocalPref";
    String exportDefault = "defaultExportPolicy";
    long targetAs = 65003L;
    long highPreferenceSourceAs = 65101L;
    long equalPreferenceSourceAs = 65102L;

    String PREFIX_LABEL = "prefixMatch";
    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_LABEL,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixString)))));

    setUpConfigs(configs, TARGETNODE);
    includeCommunities(configs.get(TARGETNODE), regex_community1);
    configs.get(TARGETNODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));

    Map<NodeRecord, BgpProcess> processes = getBgpProcesses(configs, TARGETNODE);
    processes
        .get(TARGETNODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                highPreferenceIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(targetAs)
                    .setRemoteAs(highPreferenceSourceAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(highPreferenceImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build(),
                defaultPreferenceIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(targetAs)
                    .setRemoteAs(equalPreferenceSourceAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(equalPreferenceImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build()));

    List<Statement> highPreferenceImportStatements =
        new java.util.ArrayList<>(
            ifStatement(
                checkForPrefixListMatch(PREFIX_LABEL),
                addToCommunities(community1),
                permitRoute(true)));
    highPreferenceImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    RoutingPolicy targetDefaultImport =
        makePolicy(configs.get(TARGETNODE), highPreferenceImport, highPreferenceImportStatements);

    List<Statement> equalPreferenceImportStatements =
        new java.util.ArrayList<>(permitRoute(true));
    equalPreferenceImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    makePolicy(configs.get(TARGETNODE), equalPreferenceImport, equalPreferenceImportStatements);
    makePolicy(configs.get(TARGETNODE), exportDefault, permitRoute(true));

    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(community1)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(
        tbdd, configs, targetDefaultImport, List.of());
  }

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceSingleNodeIbgpExample(
      NodeRecord TARGETNODE,
      Ip highPreferenceIncoming,
      Ip ibgpIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";

    String EXTERNAL = "externalNeighbor";

    String highPreferenceImport = "incomingHighLocalPref";
    String ibgpImport = "incomingIbgp";
    String exportDefault = "defaultExportPolicy";
    long targetAs = 65003L;
    long highPreferenceSourceAs = 65101L;
    long ibgpSourceAs = targetAs;

    String PREFIX_LABEL = "prefixMatch";
    RouteFilterList prefixMatch =
        new RouteFilterList(
            PREFIX_LABEL,
            ImmutableList.of(
                new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixString)))));

    setUpConfigs(configs, TARGETNODE);
    includeCommunities(configs.get(TARGETNODE), regex_community1);
    configs.get(TARGETNODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));

    Map<NodeRecord, BgpProcess> processes = getBgpProcesses(configs, TARGETNODE);
    processes
        .get(TARGETNODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                highPreferenceIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(targetAs)
                    .setRemoteAs(highPreferenceSourceAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(highPreferenceImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build(),
                ibgpIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(targetAs)
                    .setRemoteAs(ibgpSourceAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(ibgpImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build()));

    List<Statement> highPreferenceImportStatements =
        new java.util.ArrayList<>(
            ifStatement(
                checkForPrefixListMatch(PREFIX_LABEL),
                addToCommunities(community1),
                permitRoute(true)));
    highPreferenceImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    RoutingPolicy targetDefaultImport =
        makePolicy(configs.get(TARGETNODE), highPreferenceImport, highPreferenceImportStatements);
    makePolicy(configs.get(TARGETNODE), ibgpImport, permitRoute(true));
    makePolicy(configs.get(TARGETNODE), exportDefault, permitRoute(true));

    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(community1)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(
        tbdd, configs, targetDefaultImport, List.of());
  }

  private static org.batfish.datamodel.BgpActivePeerConfig getPeerConfigWithAs(
      String groupName, String importPolicy, String exportPolicy, long localAs, long remoteAs) {
    return org.batfish.datamodel.BgpActivePeerConfig.builder()
        .setGroup(groupName)
        .setLocalAs(localAs)
        .setRemoteAs(remoteAs)
        .setIpv4UnicastAddressFamily(
            org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                .setImportPolicy(importPolicy)
                .setExportPolicy(exportPolicy)
                .build())
        .build();
  }

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceExample(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      Ip alphaIncoming,
      Ip betaIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

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
    String importGAMMA2BETA = "importG2B";
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
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    long internalAs = 65003L;
    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getPeerConfigWithAs(
                    EXTERNAL, externalAlphaImport, exportDefault, internalAs, 65101L),
                BETANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importDefault, exportDefault, internalAs, internalAs)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importALPHA2BETA, exportDefault, internalAs, internalAs),
                GAMMANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importGAMMA2BETA, exportDefault, internalAs, internalAs),
                betaIncoming,
                getPeerConfigWithAs(
                    EXTERNAL, externalBetaImport, exportDefault, internalAs, 65102L)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importBETA2GAMMA, exportDefault, internalAs, internalAs)));

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
    makePolicy(configs.get(BETANODE), importGAMMA2BETA, permitRoute(true));
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

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceEqualExample(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      Ip alphaIncoming,
      Ip betaIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

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

    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE);

    includeCommunities(configs.get(ALPHANODE), regex_community1);
    configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(BETANODE), regex_community1, regex_community2);
    configs.get(BETANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(GAMMANODE), regex_community2);
    configs.get(GAMMANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));

    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalAlphaImport, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importALPHA2BETA, exportDefault),
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                betaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalBetaImport, exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importBETA2GAMMA, exportDefault)));

    makePolicy(
        configs.get(ALPHANODE),
        externalAlphaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community1),
            clearCommunities()));
    makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));

    List<Statement> alphaBetaImportStatements =
        new java.util.ArrayList<>(
            TestConfigConstructionUtils.ifStatement(
                checkForCommunity(community1), addToCommunities(community2), permitRoute(true)));
    alphaBetaImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    RoutingPolicy alphaBetaImport =
        makePolicy(configs.get(BETANODE), importALPHA2BETA, alphaBetaImportStatements);

    List<Statement> externalBetaImportStatements =
        new java.util.ArrayList<>(
            ifStatement(
                checkForPrefixListMatch(PREFIX_LABEL),
                replaceCommunities(community2),
                clearCommunities()));
    externalBetaImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    makePolicy(configs.get(BETANODE), externalBetaImport, externalBetaImportStatements);
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));

    makePolicy(
        configs.get(GAMMANODE),
        importBETA2GAMMA,
        ifStatement(checkForCommunity(community2), permitRoute(true), permitRoute(false)));
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

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

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceExample2(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      Ip alphaIncoming,
      Ip gammaIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";
    String community2 = "2:2";
    String regex_community2 = "^" + community2 + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String externalAlphaImport = "incomingFromOutsideAlpha";
    String externalGammaImport = "incomingFromOutsideGamma";
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
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    long internalAs = 65003L;
    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getPeerConfigWithAs(
                    EXTERNAL, externalAlphaImport, exportDefault, internalAs, 65101L),
                BETANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importDefault, exportDefault, internalAs, internalAs)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importALPHA2BETA, exportDefault, internalAs, internalAs),
                GAMMANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importDefault, exportDefault, internalAs, internalAs)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getPeerConfigWithAs(
                    INTERNAL, importBETA2GAMMA, exportDefault, internalAs, internalAs),
                gammaIncoming,
                getPeerConfigWithAs(
                    EXTERNAL, externalGammaImport, exportDefault, internalAs, 65102L)));

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

    List<Statement> alphaBetaImportStatements =
        new java.util.ArrayList<>(
            TestConfigConstructionUtils.ifStatement(
                checkForCommunity(community1), addToCommunities(community2), permitRoute(true)));
    RoutingPolicy alphaBetaImport =
        makePolicy(configs.get(BETANODE), importALPHA2BETA, alphaBetaImportStatements);

    makePolicy(configs.get(BETANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));

    // import from beta to gamma with high local preference
    List<Statement> betaGammaImportStatements =
        ifStatement(
            checkForCommunity(community2),
            ImmutableList.of(
                new SetLocalPreference(new LiteralLong(200L)),
                new Statements.StaticStatement(Statements.ExitAccept)),
            permitRoute(false));

    makePolicy(configs.get(GAMMANODE), importBETA2GAMMA, betaGammaImportStatements);
    makePolicy(
        configs.get(BETANODE),
        externalGammaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community2),
            clearCommunities()));
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

  private TestConfigConstructionUtils.Networkv2 pathWithLocalPreferenceEqualExample2(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      Ip alphaIncoming,
      Ip gammaIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";
    String community2 = "2:2";
    String regex_community2 = "^" + community2 + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String externalAlphaImport = "incomingFromOutsideAlpha";
    String externalGammaImport = "incomingFromOutsideGamma";
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

    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE);

    includeCommunities(configs.get(ALPHANODE), regex_community1);
    configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(BETANODE), regex_community1, regex_community2);
    configs.get(BETANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(GAMMANODE), regex_community2);

    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalAlphaImport, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importALPHA2BETA, exportDefault),
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importBETA2GAMMA, exportDefault),
                gammaIncoming,
                getBgpActivePeerConfig(EXTERNAL, externalGammaImport, exportDefault)));

    makePolicy(
        configs.get(ALPHANODE),
        externalAlphaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community1),
            clearCommunities()));
    makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));

    List<Statement> alphaBetaImportStatements =
        new java.util.ArrayList<>(
            TestConfigConstructionUtils.ifStatement(
                checkForCommunity(community1), addToCommunities(community2), permitRoute(true)));
    RoutingPolicy alphaBetaImport =
        makePolicy(configs.get(BETANODE), importALPHA2BETA, alphaBetaImportStatements);

    makePolicy(configs.get(BETANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));

    List<Statement> betaGammaImportStatements =
        ifStatement(
            checkForCommunity(community2),
            ImmutableList.of(
                new SetLocalPreference(new LiteralLong(200L)),
                new Statements.StaticStatement(Statements.ExitAccept)),
            permitRoute(false));
    makePolicy(configs.get(GAMMANODE), importBETA2GAMMA, betaGammaImportStatements);

    List<Statement> externalGammaImportStatements =
        new java.util.ArrayList<>(replaceCommunities(community2));
    externalGammaImportStatements.add(0, new SetLocalPreference(new LiteralLong(200L)));
    makePolicy(configs.get(GAMMANODE), externalGammaImport, externalGammaImportStatements);
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

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

  private TestConfigConstructionUtils.Networkv2 pathWithAsPathLengthExample(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      Ip alphaIncoming,
      String prefixString) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String externalAlphaImport = "incomingFromOutsideAlpha";
    String importALPHA2BETA = "importA2B";
    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    long alphaAs = 65001L;
    long betaAs = 65002L;
    long gammaAs = 65003L;
    long externalAs = 65100L;

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
    includeCommunities(configs.get(BETANODE), regex_community1);
    configs.get(BETANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_LABEL, prefixMatch));
    includeCommunities(configs.get(GAMMANODE), regex_community1);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(EXTERNAL)
                    .setLocalAs(alphaAs)
                    .setRemoteAs(externalAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(externalAlphaImport)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build(),
                BETANODE.getIp(),
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(INTERNAL)
                    .setLocalAs(alphaAs)
                    .setRemoteAs(betaAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(importDefault)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build(),
                GAMMANODE.getIp(),
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(INTERNAL)
                    .setLocalAs(alphaAs)
                    .setRemoteAs(gammaAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(importDefault)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build()));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(INTERNAL)
                    .setLocalAs(betaAs)
                    .setRemoteAs(alphaAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(importALPHA2BETA)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build(),
                GAMMANODE.getIp(),
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(INTERNAL)
                    .setLocalAs(betaAs)
                    .setRemoteAs(gammaAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(importDefault)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build()));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(INTERNAL)
                    .setLocalAs(gammaAs)
                    .setRemoteAs(betaAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(importDefault)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build(),
                ALPHANODE.getIp(),
                org.batfish.datamodel.BgpActivePeerConfig.builder()
                    .setGroup(INTERNAL)
                    .setLocalAs(gammaAs)
                    .setRemoteAs(alphaAs)
                    .setIpv4UnicastAddressFamily(
                        org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily.builder()
                            .setImportPolicy(importDefault)
                            .setExportPolicy(exportDefault)
                            .build())
                    .build()));

    // Create the policies
    makePolicy(
        configs.get(ALPHANODE),
        externalAlphaImport,
        ifStatement(
            checkForPrefixListMatch(PREFIX_LABEL),
            replaceCommunities(community1),
            clearCommunities()));
    RoutingPolicy alphaDefaultImport =
        makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));

    List<Statement> betaImportFromAlphaStatements =
        ImmutableList.of(
            new org.batfish.datamodel.routing_policy.communities.SetCommunities(
                new org.batfish.datamodel.routing_policy.communities.CommunitySetDifference(
                    org.batfish.datamodel.routing_policy.communities.InputCommunities.instance(),
                    new org.batfish.datamodel.routing_policy.communities.CommunityIs(
                        org.batfish.datamodel.bgp.community.StandardCommunity.parse(community1)))),
            new org.batfish.datamodel.routing_policy.statement.Statements.StaticStatement(
                Statements.ExitAccept));
    makePolicy(configs.get(BETANODE), importALPHA2BETA, betaImportFromAlphaStatements);
    makePolicy(configs.get(BETANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(GAMMANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(community1)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaDefaultImport, List.of());
  }

  @Test
  public void pathWithLocalPreferenceNoInterferenceTest() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    Ip incomingBeta = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceExample(
            ALPHANODE_R, BETANODE_R, GAMMANODE_R, incomingAlpha, incomingBeta, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    // the interfering route has a lower local preference, so it can never be selected
    assertFalse(checks.getRight());
  }

  @Test
  public void pathWithLocalPreferenceSingleNodeNoInterferenceTest() {
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingWithHighLocalPref = Ip.parse("100.0.0.10");
    Ip incomingWithDefaultLocalPref = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceSingleNodeExample(
            GAMMANODE_R, incomingWithHighLocalPref, incomingWithDefaultLocalPref, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertFalse(checks.getRight());
  }

  @Test
  public void pathWithLocalPreferenceSingleNodeEqualPreferenceInterferenceTest() {
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingWithHighLocalPref = Ip.parse("100.0.0.10");
    Ip incomingWithEqualLocalPref = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceSingleNodeEqualExample(
            GAMMANODE_R, incomingWithHighLocalPref, incomingWithEqualLocalPref, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  @Test
  public void pathWithLocalPreferenceSingleNodeIbgpInterferenceTest() {
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingWithHighLocalPref = Ip.parse("100.0.0.10");
    Ip incomingIbgp = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceSingleNodeIbgpExample(
            GAMMANODE_R, incomingWithHighLocalPref, incomingIbgp, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  @Test
  public void pathWithLocalPreferenceSingleNodeIbgpAssumedLowLocalPrefNoInterferenceTest() {
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingWithHighLocalPref = Ip.parse("100.0.0.10");
    Ip incomingIbgp = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceSingleNodeIbgpExample(
            GAMMANODE_R, incomingWithHighLocalPref, incomingIbgp, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    Location loc = info.checkForEdgeViaIps(incomingIbgp, GAMMANODE.getSingleIp()).get();
    Invariant incomingIbgpAssumption =
        new Invariant(net.tbdd(), net.tbdd().getOriginalRoute().getLocalPref().value(50L));
    info.addAssumption(loc, incomingIbgpAssumption);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertFalse(checks.getRight());
  }

  @Test
  public void pathWithLocalPreferenceEqualPreferenceInterferenceTest() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    Ip incomingBeta = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceEqualExample(
            ALPHANODE_R, BETANODE_R, GAMMANODE_R, incomingAlpha, incomingBeta, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  @Test
  public void pathWithLocalPreferenceNoInterferenceTest2() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    Ip incomingBeta = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceExample2(
            ALPHANODE_R, BETANODE_R, GAMMANODE_R, incomingAlpha, incomingBeta, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    // the interfering route has a lower local preference, so it can never be selected
    assertFalse(checks.getRight());
  }

  @Test
  public void pathWithLocalPreferenceEqualPreferenceInterferenceTest2() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    Ip incomingBeta = Ip.parse("100.0.0.20");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithLocalPreferenceEqualExample2(
            ALPHANODE_R, BETANODE_R, GAMMANODE_R, incomingAlpha, incomingBeta, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  @Test
  public void pathWithAsPathLengthNoInterferenceTest() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithAsPathLengthExample(ALPHANODE_R, BETANODE_R, GAMMANODE_R, incomingAlpha, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node ALPHANODE = ALPHANODE_R.instantiate(info);
    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    // the incoming traffic is assumed to all have AS-path length of 1;
    // this (or a similar assumption setting the AS-path length to some constant) is required for us
    // to determine that there is no interference
    Invariant incomingAtAlphaAssumption =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setAsPathLength(1).build(net.tbdd(), net.template()));
    Location loc = info.checkForEdgeViaIps(incomingAlpha, ALPHANODE.getSingleIp()).get();
    info.addAssumption(loc, incomingAtAlphaAssumption);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    // the interfering route travels one more EBGP hop, so its AS path is longer and it can
    // never be selected
    assertFalse(checks.getRight());
  }


  /**
   * Regression test: a target that constrains the AS-path length. The constraint has to be
   * decremented as it is pushed back across each EBGP session, since the sender prepends its own
   * ASN after its export policy runs. Without that, the constraint is unsatisfiable one hop back
   * and no good path is found at all.
   */
  @Test
  public void pathWithAsPathLengthTargetNoInterferenceTest() {
    NodeRecord ALPHANODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETANODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMANODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    Ip incomingAlpha = Ip.parse("100.0.0.10");
    String prefixStr = "2.4.8.0/24";

    PrefixSpace TARGET_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        pathWithAsPathLengthExample(ALPHANODE_R, BETANODE_R, GAMMANODE_R, incomingAlpha, prefixStr);
    NetworkInfo info = net.getInfo(TARGET_PREFIX);

    Node ALPHANODE = ALPHANODE_R.instantiate(info);
    Node GAMMANODE = GAMMANODE_R.instantiate(info);

    // an assumption on an edge constrains the route as the neighbor sent it, before that neighbor
    // prepends its own ASN, so the route arrives at alphaNode with an AS-path length of 2
    Invariant incomingAtAlphaAssumption =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setAsPathLength(1).build(net.tbdd(), net.template()));
    Location loc = info.checkForEdgeViaIps(incomingAlpha, ALPHANODE.getSingleIp()).get();
    info.addAssumption(loc, incomingAtAlphaAssumption);

    // a target at a node constrains the route as that node sees it after import; the good route
    // reaches gammaNode directly from alphaNode, which prepends one more ASN
    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .setCommunities(comm)
                .setAsPathLength(3)
                .build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, TARGET_PREFIX, GAMMANODE, target, Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    // the interfering route travels one more EBGP hop, so its AS path is longer and it can
    // never be selected
    assertFalse(checks.getRight());
  }

  private TestConfigConstructionUtils.Networkv2 weakerPathConstraints(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      NodeRecord DELTANODE,
      NodeRecord EPSILONNODE,
      Ip alphaIncoming,
      Ip deltaIncoming,
      int variation) {
    assert 0 <= variation && variation <= 2;
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community = "1:1";
    String regex_community = "^" + community + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String tagOnExport = "tagCommunityOnExport";
    String denyCommunity = "denyCommunity";
    String denyEverything = "denyAllTraffic";
    String removesAllCommunities = "clearCommunities";

    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE, EPSILONNODE);

    // include the communities on the necessary nodes
    includeCommunities(configs.get(BETANODE), regex_community);
    includeCommunities(configs.get(DELTANODE), regex_community);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE, EPSILONNODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, importDefault, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, removesAllCommunities),
                DELTANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(
                    // if the variation is not 0, we deny traffic with community going to gamma
                    INTERNAL, importDefault, 0 < variation ? denyCommunity : exportDefault),
                EPSILONNODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(), getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                EPSILONNODE.getIp(),
                    getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(DELTANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                deltaIncoming,
                getBgpActivePeerConfig(EXTERNAL, importDefault, exportDefault),
                ALPHANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, tagOnExport)));

    processes
        .get(EPSILONNODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(
                    INTERNAL, importDefault, variation == 2 ? denyEverything : exportDefault)));

    // Create the policies
    RoutingPolicy alphaDefaultImport =
        makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), removesAllCommunities, clearCommunities());

    makePolicy(configs.get(BETANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));
    makePolicy(
        configs.get(BETANODE),
        denyCommunity,
        ifStatement(checkForCommunity(community), permitRoute(false), permitRoute(true)));

    makePolicy(configs.get(GAMMANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(DELTANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(DELTANODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(DELTANODE), tagOnExport, addToCommunities(community));

    makePolicy(configs.get(EPSILONNODE), importDefault, permitRoute(true));
    makePolicy(configs.get(EPSILONNODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(EPSILONNODE), denyEverything, permitRoute(false));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(community)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaDefaultImport, List.of());
  }

  @Test
  public void weakerExampleBaseTest() {
    NodeRecord ALPHA_NODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETA_NODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMA_NODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTA_NODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    NodeRecord EPSILON_NODE_R = new NodeRecord("10.0.0.5", "epsilonNode");
    Ip alphaIncoming = Ip.parse("100.0.0.10");
    Ip deltaIncoming = Ip.parse("100.0.0.40");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        weakerPathConstraints(
            ALPHA_NODE_R,
            BETA_NODE_R,
            GAMMA_NODE_R,
            DELTA_NODE_R,
            EPSILON_NODE_R,
            alphaIncoming,
            deltaIncoming,
            0);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node GAMMANODE = GAMMA_NODE_R.instantiate(info);

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, BASIC_PREFIX, GAMMANODE, new Invariant(info.tbdd), Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertFalse(checks.getRight());
  }

  @Test
  public void weakerExampleInterferenceTest() {
    NodeRecord ALPHA_NODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETA_NODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMA_NODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTA_NODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    NodeRecord EPSILON_NODE_R = new NodeRecord("10.0.0.5", "epsilonNode");
    Ip alphaIncoming = Ip.parse("100.0.0.10");
    Ip deltaIncoming = Ip.parse("100.0.0.40");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        weakerPathConstraints(
            ALPHA_NODE_R,
            BETA_NODE_R,
            GAMMA_NODE_R,
            DELTA_NODE_R,
            EPSILON_NODE_R,
            alphaIncoming,
            deltaIncoming,
            2);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node GAMMANODE = GAMMA_NODE_R.instantiate(info);

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, BASIC_PREFIX, GAMMANODE, new Invariant(info.tbdd), Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  /// commented out because weakening path constraints commented out
  /* @Test
  public void weakerExampleNoInterferenceTest() {
    NodeRecord ALPHA_NODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETA_NODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMA_NODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTA_NODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    NodeRecord EPSILON_NODE_R = new NodeRecord("10.0.0.5", "epsilonNode");
    Ip alphaIncoming = Ip.parse("100.0.0.10");
    Ip deltaIncoming = Ip.parse("100.0.0.40");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        weakerPathConstraints(
            ALPHA_NODE_R,
            BETA_NODE_R,
            GAMMA_NODE_R,
            DELTA_NODE_R,
            EPSILON_NODE_R,
            alphaIncoming,
            deltaIncoming,
            1);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node GAMMANODE = GAMMA_NODE_R.instantiate(info);

    TableAnswerElement result =
        LivenessAnswerer.run(info, BASIC_PREFIX, GAMMANODE, new Invariant(info.tbdd), Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());

     assertTrue(checks.getLeft());
     assertFalse(checks.getRight());
  } */

  private TestConfigConstructionUtils.Networkv2 weakerPathConstraints2(
      NodeRecord ALPHANODE,
      NodeRecord BETANODE,
      NodeRecord GAMMANODE,
      NodeRecord DELTANODE,
      NodeRecord EPSILONNODE,
      Ip alphaIncoming,
      Ip deltaIncoming,
      int variation) {
    assert 0 <= variation && variation <= 5;
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community = "1:1";
    String regex_community = "^" + community + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String tagOnExport = "tagCommunityOnExport";
    String denyEverything = "denyAllTraffic";
    String removesAllCommunities = "clearCommunities";

    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE, EPSILONNODE);

    // include the communities on the necessary nodes
    includeCommunities(configs.get(ALPHANODE), regex_community);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHANODE, BETANODE, GAMMANODE, DELTANODE, EPSILONNODE);

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, importDefault, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(
                    INTERNAL, importDefault, 0 < variation ? tagOnExport : exportDefault),
                DELTANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, tagOnExport)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                EPSILONNODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                EPSILONNODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(DELTANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                deltaIncoming,
                getBgpActivePeerConfig(EXTERNAL, importDefault, exportDefault),
                ALPHANODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                BETANODE.getIp(),
                getBgpActivePeerConfig(
                    INTERNAL,
                    importDefault,
                    variation == 1 || variation == 3 || variation == 5
                        ? denyEverything
                        : exportDefault)));
    processes
        .get(EPSILONNODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                getBgpActivePeerConfig(
                    INTERNAL, variation == 5 ? denyEverything : importDefault, exportDefault),
                GAMMANODE.getIp(),
                getBgpActivePeerConfig(
                    INTERNAL,
                    variation == 5 ? denyEverything : importDefault,
                    3 <= variation ? removesAllCommunities : exportDefault)));

    // Create the policies
    RoutingPolicy alphaDefaultImport =
        makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(ALPHANODE), tagOnExport, addToCommunities(community));

    makePolicy(configs.get(BETANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(GAMMANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(DELTANODE), importDefault, permitRoute(true));
    makePolicy(configs.get(DELTANODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(DELTANODE), denyEverything, permitRoute(false));

    makePolicy(configs.get(EPSILONNODE), importDefault, permitRoute(true));
    makePolicy(configs.get(EPSILONNODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(EPSILONNODE), removesAllCommunities, clearCommunities());
    makePolicy(configs.get(EPSILONNODE), denyEverything, permitRoute(false));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(community)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaDefaultImport, List.of());
  }

  private Pair<Boolean, Boolean> runVersion(int v) {
    NodeRecord ALPHA_NODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETA_NODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMA_NODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTA_NODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    NodeRecord EPSILON_NODE_R = new NodeRecord("10.0.0.5", "epsilonNode");
    Ip alphaIncoming = Ip.parse("100.0.0.10");
    Ip deltaIncoming = Ip.parse("100.0.0.40");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        weakerPathConstraints2(
            ALPHA_NODE_R,
            BETA_NODE_R,
            GAMMA_NODE_R,
            DELTA_NODE_R,
            EPSILON_NODE_R,
            alphaIncoming,
            deltaIncoming,
            v);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node GAMMANODE = GAMMA_NODE_R.instantiate(info);

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(info, BASIC_PREFIX, GAMMANODE, target, Set.of());
    return processResultRows(result.getRowsList());
  }

  @Test
  public void weakerExample2BaseTest() {
    // expects no good path
    Pair<Boolean, Boolean> checks = runVersion(0);
    assertFalse(checks.getLeft());
  }

  @Test
  public void weakerExample2V1Test() {
    // expects good path and no interference
    Pair<Boolean, Boolean> checks = runVersion(1);
    assertTrue(checks.getLeft());
    assertFalse(checks.getRight());
  }

  @Test
  public void weakerExample2V2Test() {
    // expects good path but there is interference
    Pair<Boolean, Boolean> checks = runVersion(2);
    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  @Test
  public void weakerExample2V3Test() {
    // expects good path but there is interference
    Pair<Boolean, Boolean> checks = runVersion(3);
    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  @Test
  public void weakerExample2V4Test() {
    // expects good path but there is interference
    Pair<Boolean, Boolean> checks = runVersion(4);
    assertTrue(checks.getLeft());
    assertTrue(checks.getRight());
  }

  @Test
  public void weakerExample2V5Test() {
    // expects good path and no interference
    Pair<Boolean, Boolean> checks = runVersion(5);
    assertTrue(checks.getLeft());
    assertFalse(checks.getRight());
  }

  private TestConfigConstructionUtils.Networkv2 weakerPathConstraints3(
      NodeRecord ALPHA_NODE,
      NodeRecord BETA_NODE,
      NodeRecord GAMMA_NODE,
      NodeRecord DELTA_NODE,
      NodeRecord EPSILON_NODE,
      NodeRecord ZETA_NODE,
      Ip alphaIncoming,
      Ip deltaIncoming,
      int variation) {
    assert 0 <= variation && variation <= 3;
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community = "1:1";
    String regex_community = "^" + community + "$";
    String red_herring = "2:2";
    String regex_red_herring = "^" + red_herring + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String tagOnImport = "initialTag";
    String tagOnExport = "tagCommunityOnExport";
    String checkCommunities = "checksCommunities";
    String removesAllCommunities = "clearCommunities";
    String deniesAll = "denyAllTrafficWithCommunity";

    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHA_NODE, BETA_NODE, GAMMA_NODE, DELTA_NODE, EPSILON_NODE, ZETA_NODE);

    // include the communities on the necessary nodes
    includeCommunities(configs.get(ALPHA_NODE), regex_red_herring);
    includeCommunities(configs.get(BETA_NODE), regex_community, regex_red_herring);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(
            configs, ALPHA_NODE, BETA_NODE, GAMMA_NODE, DELTA_NODE, EPSILON_NODE, ZETA_NODE);

    processes
        .get(ALPHA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                getBgpActivePeerConfig(EXTERNAL, tagOnImport, exportDefault),
                BETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, tagOnExport)));
    processes
        .get(BETA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                EPSILON_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(GAMMA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                EPSILON_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                ZETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(DELTA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                deltaIncoming,
                getBgpActivePeerConfig(EXTERNAL, tagOnImport, exportDefault),
                BETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                ZETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(EPSILON_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, checkCommunities, exportDefault),
                GAMMA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, checkCommunities, exportDefault)));
    processes
        .get(ZETA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                DELTA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                GAMMA_NODE.getIp(),
                getBgpActivePeerConfig(
                    INTERNAL,
                    importDefault,
                    variation == 2
                        ? deniesAll
                        : (variation == 3 ? removesAllCommunities : exportDefault))));

    // Create the policies
    RoutingPolicy alphaDefaultImport =
        makePolicy(configs.get(ALPHA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHA_NODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(ALPHA_NODE), tagOnImport, addToCommunities(community));
    makePolicy(configs.get(ALPHA_NODE), tagOnExport, addToCommunities(red_herring));

    makePolicy(configs.get(BETA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETA_NODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(GAMMA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(GAMMA_NODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(DELTA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(DELTA_NODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(DELTA_NODE), tagOnImport, addToCommunities(community));

    makePolicy(configs.get(EPSILON_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(EPSILON_NODE), exportDefault, permitRoute(true));
    makePolicy(
        configs.get(EPSILON_NODE),
        checkCommunities,
        ifStatement(
            checkForCommunity(community),
            ifStatement(checkForCommunity(red_herring), permitRoute(true), permitRoute(false)),
            permitRoute(false)));

    makePolicy(configs.get(ZETA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ZETA_NODE), exportDefault, permitRoute(true));
    makePolicy(
        configs.get(ZETA_NODE),
        deniesAll,
        ifStatement(checkForCommunity(community), permitRoute(false), permitRoute(true)));
    makePolicy(configs.get(ZETA_NODE), removesAllCommunities, clearCommunities());

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(community))
            .add(RegexConstraint.parse(red_herring))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaDefaultImport, List.of());
  }

  private Pair<Boolean, Boolean> runVersion3(int v) {
    NodeRecord ALPHA_NODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETA_NODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMA_NODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTA_NODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    NodeRecord EPSILON_NODE_R = new NodeRecord("10.0.0.5", "epsilonNode");
    NodeRecord ZETA_NODE_R = new NodeRecord("10.0.0.6", "zetaNode");
    Ip alphaIncoming = Ip.parse("100.0.0.10");
    Ip deltaIncoming = Ip.parse("100.0.0.40");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        weakerPathConstraints3(
            ALPHA_NODE_R,
            BETA_NODE_R,
            GAMMA_NODE_R,
            DELTA_NODE_R,
            EPSILON_NODE_R,
            ZETA_NODE_R,
            alphaIncoming,
            deltaIncoming,
            v);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node GAMMANODE = GAMMA_NODE_R.instantiate(info);
    Edge ingress = new Edge(alphaIncoming, ALPHA_NODE_R.getIp());
    ingress.setDstNode(ALPHA_NODE_R.instantiate(info));

    RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("1:1")));
    Invariant target =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));

    TableAnswerElement result =
        ReachabilityAnswerer.run(
            info, BASIC_PREFIX, GAMMANODE, target, v == 0 ? Set.of(ingress) : Set.of());
    return processResultRows(result.getRowsList());
  }

  /// commented out because weakening path constraints commented out
  /*@Test
  public void weakerExample3IngressSetTest() {
    // expects good path and no interference when ingress node set
    Pair<Boolean, Boolean> checks = runVersion3(0);
    boolean goodPath = checks.getLeft();
    boolean hasInterference = checks.getRight();
    assertTrue(goodPath);
    assertFalse(hasInterference);
  }*/

  @Test
  public void weakerExample3BaseTest() {
    // expects good path and no interference
    Pair<Boolean, Boolean> checks = runVersion3(1);
    boolean goodPath = checks.getLeft();
    boolean hasInterference = checks.getRight();
    assertTrue(goodPath);
    assertFalse(hasInterference);
  }

  @Test
  public void weakerExample3InterferenceV1Test() {
    // expects good path and no interference
    Pair<Boolean, Boolean> checks = runVersion3(2);
    boolean goodPath = checks.getLeft();
    boolean hasInterference = checks.getRight();
    assertTrue(goodPath);
    assertTrue(hasInterference);
  }

  @Test
  public void weakerExample3InterferenceV2Test() {
    // expects good path and no interference
    Pair<Boolean, Boolean> checks = runVersion3(3);
    boolean goodPath = checks.getLeft();
    boolean hasInterference = checks.getRight();
    assertTrue(goodPath);
    assertTrue(hasInterference);
  }

  private TestConfigConstructionUtils.Networkv2 weakerPathConstraintsDiamond(
      NodeRecord ALPHA_NODE,
      NodeRecord BETA_NODE,
      NodeRecord GAMMA_NODE,
      NodeRecord DELTA_NODE,
      NodeRecord EPSILON_NODE,
      Ip alphaIncoming1,
      Ip alphaIncoming2,
      int variation) {
    assert variation == 0;
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String community1 = "1:1";
    String regex_community1 = "^" + community1 + "$";
    String community2 = "2:2";
    String regex_community2 = "^" + community2 + "$";

    String EXTERNAL = "externalNeighbor";
    String INTERNAL = "internalNeighbor";

    String tagOnImport1 = "initialTag1";
    String tagOnImport2 = "initialTag2";
    String deniesCommunity1 = "deniesCommunity1";
    String deniesCommunity2 = "deniesCommunity1";

    String importDefault = "defaultImportPolicy";
    String exportDefault = "defaultExportPolicy";

    // Set up the configs and add what features they know about
    setUpConfigs(configs, ALPHA_NODE, BETA_NODE, GAMMA_NODE, DELTA_NODE, EPSILON_NODE);

    // include the communities on the necessary nodes
    includeCommunities(configs.get(ALPHA_NODE), regex_community1, regex_community2);
    includeCommunities(configs.get(DELTA_NODE), regex_community1);
    includeCommunities(configs.get(GAMMA_NODE), regex_community2);

    // Create the BGP processes
    Map<NodeRecord, BgpProcess> processes =
        getBgpProcesses(configs, ALPHA_NODE, BETA_NODE, GAMMA_NODE, DELTA_NODE, EPSILON_NODE);

    processes
        .get(ALPHA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming1,
                getBgpActivePeerConfig(EXTERNAL, tagOnImport1, exportDefault),
                alphaIncoming2,
                getBgpActivePeerConfig(EXTERNAL, tagOnImport2, exportDefault),
                BETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(BETA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                EPSILON_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(GAMMA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, deniesCommunity1, exportDefault),
                EPSILON_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(DELTA_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, deniesCommunity2, exportDefault),
                EPSILON_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));
    processes
        .get(EPSILON_NODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                GAMMA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault),
                DELTA_NODE.getIp(),
                getBgpActivePeerConfig(INTERNAL, importDefault, exportDefault)));

    // Create the policies
    RoutingPolicy alphaDefaultImport =
        makePolicy(configs.get(ALPHA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(ALPHA_NODE), exportDefault, permitRoute(true));
    makePolicy(configs.get(ALPHA_NODE), tagOnImport1, replaceCommunities(community1));
    makePolicy(configs.get(ALPHA_NODE), tagOnImport2, replaceCommunities(community2));

    makePolicy(configs.get(BETA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(BETA_NODE), exportDefault, permitRoute(true));

    makePolicy(configs.get(GAMMA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(GAMMA_NODE), exportDefault, permitRoute(true));
    makePolicy(
        configs.get(GAMMA_NODE),
        deniesCommunity1,
        ifStatement(checkForCommunity(community1), permitRoute(false), permitRoute(true)));

    makePolicy(configs.get(DELTA_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(DELTA_NODE), exportDefault, permitRoute(true));
    makePolicy(
        configs.get(DELTA_NODE),
        deniesCommunity2,
        ifStatement(checkForCommunity(community2), permitRoute(false), permitRoute(true)));

    makePolicy(configs.get(EPSILON_NODE), importDefault, permitRoute(true));
    makePolicy(configs.get(EPSILON_NODE), exportDefault, permitRoute(true));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder()
            .add(RegexConstraint.parse(community1))
            .add(RegexConstraint.parse(community2))
            .build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, alphaDefaultImport, List.of());
  }

  private Pair<Boolean, Boolean> runDiamond(int v) {
    NodeRecord ALPHA_NODE_R = new NodeRecord("10.0.0.1", "alphaNode");
    NodeRecord BETA_NODE_R = new NodeRecord("10.0.0.2", "betaNode");
    NodeRecord GAMMA_NODE_R = new NodeRecord("10.0.0.3", "gammaNode");
    NodeRecord DELTA_NODE_R = new NodeRecord("10.0.0.4", "deltaNode");
    NodeRecord EPSILON_NODE_R = new NodeRecord("10.0.0.5", "epsilonNode");
    Ip alphaIncoming1 = Ip.parse("100.0.0.10");
    Ip alphaIncoming2 = Ip.parse("100.0.0.11");

    PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));

    TestConfigConstructionUtils.Networkv2 net =
        weakerPathConstraintsDiamond(
            ALPHA_NODE_R,
            BETA_NODE_R,
            GAMMA_NODE_R,
            DELTA_NODE_R,
            EPSILON_NODE_R,
            alphaIncoming1,
            alphaIncoming2,
            v);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);

    Node TARGET_NODE = EPSILON_NODE_R.instantiate(info);

    TableAnswerElement result =
        ReachabilityAnswerer.run(
            info, BASIC_PREFIX, TARGET_NODE, new Invariant(info.tbdd), Set.of());
    return processResultRows(result.getRowsList());
  }

  /// commented out because weakening path constraints commented out
  /*@Test
  public void weakerDiamondTest() {
    // expects good path and no interference
    Pair<Boolean, Boolean> checks = runDiamond(0);
    boolean goodPath = checks.getLeft();
    boolean hasInterference = checks.getRight();
    assertTrue(goodPath);
    assertFalse(hasInterference);
  }*/
}
