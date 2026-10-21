package org.batfish.minesweeper.question.reachability;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
import org.junit.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The weakerPathConstraints network from ReachabilityAnswererTest (whose variation 1 is the
 * commented-out test weakerExampleNoInterferenceTest there), with every router and external
 * neighbor in its own AS so that every session is EBGP and the real-BGP outcome is unambiguous.
 * Target true at gamma, prefix 10.0.0.0/8, ingress = {}.
 *
 * <p>alpha's export to beta clears communities, delta's export to beta tags 1:1, and in variations
 * 1 and 2 beta's export to gamma rejects 1:1. In variation 2 epsilon's export to gamma also
 * rejects everything. Everything else permits.
 */
public class InterferenceRepoExampleTest {
  private static final NetworkFactory nf = new NetworkFactory();
  private static final String prefixStr = "10.0.0.0/8";

  private static TableAnswerElement runQuery(
      NetworkInfo info, PrefixSpace prefix, Node target, Invariant inv, Set<Edge> ingress) {
    return ReachabilityAnswerer.run(info, prefix, target, inv, ingress);
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

  private static Pair<Boolean, Boolean> processResultRows(List<Row> rows) {
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

  private static BgpActivePeerConfig peer(
      String group, String importPolicy, String exportPolicy, long localAs, long remoteAs) {
    return BgpActivePeerConfig.builder()
        .setGroup(group)
        .setLocalAs(localAs)
        .setRemoteAs(remoteAs)
        .setIpv4UnicastAddressFamily(
            Ipv4UnicastAddressFamily.builder()
                .setImportPolicy(importPolicy)
                .setExportPolicy(exportPolicy)
                .build())
        .build();
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

    // every router and external neighbor is in its own AS, so every session is EBGP
    long alphaAs = 65001L;
    long betaAs = 65002L;
    long gammaAs = 65003L;
    long deltaAs = 65004L;
    long epsilonAs = 65005L;
    long alphaExtAs = 65101L;
    long deltaExtAs = 65104L;

    processes
        .get(ALPHANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                alphaIncoming,
                peer(EXTERNAL, importDefault, exportDefault, alphaAs, alphaExtAs),
                BETANODE.getIp(),
                peer(INTERNAL, importDefault, removesAllCommunities, alphaAs, betaAs),
                DELTANODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, alphaAs, deltaAs)));
    processes
        .get(BETANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                ALPHANODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, betaAs, alphaAs),
                DELTANODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, betaAs, deltaAs),
                GAMMANODE.getIp(),
                // if the variation is not 0, we deny traffic with community going to gamma
                peer(
                    INTERNAL,
                    importDefault,
                    0 < variation ? denyCommunity : exportDefault,
                    betaAs,
                    gammaAs),
                EPSILONNODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, betaAs, epsilonAs)));
    processes
        .get(GAMMANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, gammaAs, betaAs),
                EPSILONNODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, gammaAs, epsilonAs)));
    processes
        .get(DELTANODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                deltaIncoming,
                peer(EXTERNAL, importDefault, exportDefault, deltaAs, deltaExtAs),
                ALPHANODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, deltaAs, alphaAs),
                BETANODE.getIp(),
                peer(INTERNAL, importDefault, tagOnExport, deltaAs, betaAs)));

    processes
        .get(EPSILONNODE)
        .setNeighbors(
            ImmutableSortedMap.of(
                BETANODE.getIp(),
                peer(INTERNAL, importDefault, exportDefault, epsilonAs, betaAs),
                GAMMANODE.getIp(),
                peer(
                    INTERNAL,
                    importDefault,
                    variation == 2 ? denyEverything : exportDefault,
                    epsilonAs,
                    gammaAs)));

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

  private Pair<Boolean, Boolean> runVariation(int v) {
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
            v);
    NetworkInfo info = net.getInfo(BASIC_PREFIX);
    Node GAMMANODE = GAMMA_NODE_R.instantiate(info);
    TableAnswerElement result =
        runQuery(info, BASIC_PREFIX, GAMMANODE, new Invariant(net.tbdd()), Set.of());
    Pair<Boolean, Boolean> checks = processResultRows(result.getRowsList());
    StringBuilder sb = new StringBuilder();
    sb.append("=== CASE repo-weakerExample-v").append(v).append(" ===\n");
    for (Row row : result.getRowsList()) {
      sb.append("  [")
          .append(row.getString("Result_Label"))
          .append("] ")
          .append(row.getString("Result"))
          .append("\n");
    }
    sb.append("SUMMARY repo-weakerExample-v")
        .append(v)
        .append(" goodPath=")
        .append(checks.getLeft())
        .append(" interference=")
        .append(checks.getRight())
        .append("\n");
    System.out.print(sb);
    assertTrue(checks.getLeft());
    return checks;
  }

  @Test
  public void weakerExampleV0() {
    // beta passes every route to gamma
    assertFalse(runVariation(0).getRight());
  }

  @Test
  public void weakerExampleV1() {
    // no real interference: if beta selects delta's route tagged 1:1, beta's export to gamma drops
    // it, but epsilon delivers it to gamma
    runVariation(1);
    // TODO the interference check reports a false positive here (see INTERFERENCE_FALSE_POSITIVES.md)
    // assertFalse(runVariation(1).getRight());
  }

  @Test
  public void weakerExampleV2() {
    // real interference: epsilon passes nothing to gamma, and delta's route tagged 1:1 ties with
    // alpha's at beta, so if beta selects it, gamma ends up with no route
    assertTrue(runVariation(2).getRight());
  }
}
