package org.batfish.minesweeper.question.reachability;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.common.collect.ImmutableSortedMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.Networkv2;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
import org.junit.Before;
import org.junit.Test;

/// Tests that the interference check accounts for BGP loop prevention when the good route comes
/// back to a node on the good path. In each network, an external neighbor E sends the prefix to a,
/// which tags it 1:1 on import; the good path is a -> b -> t, and t requires 1:1. Any copy of the
/// good route that comes back to a has its communities stripped on the way, so if a could select
/// it, t would lose the route with 1:1. In real BGP the copy never gets back to a, so there is no
/// interference.
public class InterferenceLoopTest {
  private static final String PERMIT_ALL = "permitAll";
  private static final String TAG = "tag";
  private static final String CLEAR = "clearCommunities";
  private static final String COMM = "1:1";
  private static final String PREFIX = "2.4.8.0/24";
  private static final PrefixSpace PREFIX_SPACE =
      new PrefixSpace(PrefixRange.fromString(PREFIX));

  private final NetworkFactory nf = new NetworkFactory();
  private Map<NodeRecord, Configuration> configs;
  private Map<NodeRecord, Long> ases;
  private Map<NodeRecord, Map<Ip, PeerSpec>> neighbors;
  private Map<NodeRecord, Long> clusterIds;
  private Map<NodeRecord, Set<NodeRecord>> clients;
  private RoutingPolicy template;
  private int nextRouter;

  @Before
  public void setup() {
    configs = new LinkedHashMap<>();
    ases = new HashMap<>();
    neighbors = new HashMap<>();
    clusterIds = new HashMap<>();
    clients = new HashMap<>();
    nextRouter = 1;
  }

  /// A configured neighbor: its AS, and the import and export policies for it
  private record PeerSpec(long remoteAs, String importPolicy, String exportPolicy) {}

  private NodeRecord router(String name, long as) {
    NodeRecord node = new NodeRecord("10.0.0." + nextRouter++, name);
    Configuration config =
        nf.configurationBuilder()
            .setHostname(name)
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .setDefaultInboundAction(PERMIT)
            .build();
    includeCommunities(config, "^" + COMM + "$");
    template =
        nf.routingPolicyBuilder()
            .setOwner(config)
            .setName(PERMIT_ALL)
            .setStatements(permitRoute(true))
            .build();
    nf.routingPolicyBuilder()
        .setOwner(config)
        .setName(TAG)
        .setStatements(addToCommunities(COMM))
        .build();
    nf.routingPolicyBuilder()
        .setOwner(config)
        .setName(CLEAR)
        .setStatements(clearCommunities())
        .build();
    configs.put(node, config);
    ases.put(node, as);
    neighbors.put(node, new HashMap<>());
    return node;
  }

  /// A session between x and y that permits everything; iBGP if they are in the same AS
  private void session(NodeRecord x, NodeRecord y) {
    neighbors.get(x).put(y.getIp(), new PeerSpec(ases.get(y), PERMIT_ALL, PERMIT_ALL));
    neighbors.get(y).put(x.getIp(), new PeerSpec(ases.get(x), PERMIT_ALL, PERMIT_ALL));
  }

  /// A session from an external neighbor into node, with the given import policy
  private void external(NodeRecord node, String ip, long externalAs, String importPolicy) {
    neighbors.get(node).put(Ip.parse(ip), new PeerSpec(externalAs, importPolicy, PERMIT_ALL));
  }

  /// Makes the router a route reflector that uses the given cluster ID on all its sessions
  private void reflector(NodeRecord router, long clusterId) {
    clusterIds.put(router, clusterId);
  }

  /// Makes the client a route-reflector client of the reflector
  private void client(NodeRecord reflector, NodeRecord client) {
    clients.computeIfAbsent(reflector, k -> new HashSet<>()).add(client);
  }

  /// Makes sender strip all communities from the routes it sends receiver
  private void strips(NodeRecord sender, NodeRecord receiver) {
    neighbors
        .get(sender)
        .compute(
            receiver.getIp(),
            (ip, spec) -> new PeerSpec(spec.remoteAs(), spec.importPolicy(), CLEAR));
  }

  private Networkv2 build() {
    Map<Ip, NodeRecord> routerByIp = new HashMap<>();
    configs.keySet().forEach(node -> routerByIp.put(node.getIp(), node));
    for (NodeRecord node : configs.keySet()) {
      Vrf vrf =
          nf.vrfBuilder()
              .setOwner(configs.get(node))
              .setName(Configuration.DEFAULT_VRF_NAME)
              .build();
      Map<Ip, BgpActivePeerConfig> peers = new HashMap<>();
      neighbors
          .get(node)
          .forEach(
              (ip, spec) ->
                  peers.put(
                      ip,
                      BgpActivePeerConfig.builder()
                          .setLocalAs(ases.get(node))
                          .setRemoteAs(spec.remoteAs())
                          .setClusterId(clusterIds.get(node))
                          .setIpv4UnicastAddressFamily(
                              Ipv4UnicastAddressFamily.builder()
                                  .setRouteReflectorClient(
                                      routerByIp.containsKey(ip)
                                          && clients
                                              .getOrDefault(node, Set.of())
                                              .contains(routerByIp.get(ip)))
                                  .setImportPolicy(spec.importPolicy())
                                  .setExportPolicy(spec.exportPolicy())
                                  .build())
                          .build()));
      nf.bgpProcessBuilder()
          .setRouterId(node.getIp())
          .setEbgpAdminCost(0)
          .setIbgpAdminCost(0)
          .setLocalAdminCost(0)
          .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
          .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
          .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
          .setVrf(vrf)
          .build()
          .setNeighbors(ImmutableSortedMap.copyOf(peers));
    }
    TransferBDD tbdd =
        new TransferBDD(
            getConfigAtomicPredicates(
                Set.of(RegexConstraint.parse(COMM)), Set.of(), configs.values()));
    return new Networkv2(tbdd, configs, template, List.of());
  }

  /// Runs the reachability query for a route with 1:1 at the target; returns (good path,
  /// interference)
  private Pair<Boolean, Boolean> run(Networkv2 net, NodeRecord target) {
    NetworkInfo info = net.getInfo(PREFIX_SPACE);
    Invariant tagged =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse(COMM))))
                .build(net.tbdd(), net.template()));
    TableAnswerElement result =
        ReachabilityAnswerer.run(info, PREFIX_SPACE, target.instantiate(info), tagged, Set.of());
    boolean goodPath = false;
    boolean interference = false;
    for (Row row : result.getRowsList()) {
      String label = row.getString("Result_Label");
      goodPath |= label.equals("Good Path");
      interference |= label.startsWith("Potential Interference");
    }
    return Pair.of(goodPath, interference);
  }

  @Test
  public void directEcho() {
    // b sends the good route straight back to a, which drops it since its AS is in the path
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    NodeRecord t = router("t", 3);
    external(a, "100.0.0.1", 100, TAG);
    session(a, b);
    session(b, t);
    strips(b, a);
    Pair<Boolean, Boolean> res = run(build(), t);
    assertTrue(res.getLeft());
    assertFalse(res.getRight());
  }

  @Test
  public void indirectEcho() {
    // b sends the good route to x, which sends it back to a; a drops it since its AS is in the
    // path
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    NodeRecord t = router("t", 3);
    NodeRecord x = router("x", 4);
    external(a, "100.0.0.1", 100, TAG);
    session(a, b);
    session(b, t);
    session(b, x);
    session(x, a);
    strips(x, a);
    Pair<Boolean, Boolean> res = run(build(), t);
    assertTrue(res.getLeft());
    assertFalse(res.getRight());
  }

  @Test
  public void indirectRouteFromElsewhere() {
    // control: x also has its own external neighbor, so a can receive a route from x without 1:1
    // that never passed through a, select it, and send it to b
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    NodeRecord t = router("t", 3);
    NodeRecord x = router("x", 4);
    external(a, "100.0.0.1", 100, TAG);
    external(x, "100.0.0.2", 200, PERMIT_ALL);
    session(a, b);
    session(b, t);
    session(b, x);
    session(x, a);
    strips(x, a);
    Pair<Boolean, Boolean> res = run(build(), t);
    assertTrue(res.getLeft());
    assertTrue(res.getRight());
  }

  @Test
  public void indirectEchoAfterIbgp() {
    // a and b share AS 1 over iBGP; b sends the good route to x over eBGP, which adds AS 1 to its
    // path, so a drops the copy x sends back
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 1);
    NodeRecord t = router("t", 3);
    NodeRecord x = router("x", 4);
    external(a, "100.0.0.1", 100, TAG);
    session(a, b);
    session(b, t);
    session(b, x);
    session(x, a);
    strips(x, a);
    Pair<Boolean, Boolean> res = run(build(), t);
    assertTrue(res.getLeft());
    assertFalse(res.getRight());
  }

  @Test
  public void directEchoOverIbgp() {
    // a and b share AS 1 over iBGP; b does not send a's iBGP route back to its iBGP peer a
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 1);
    NodeRecord t = router("t", 3);
    external(a, "100.0.0.1", 100, TAG);
    session(a, b);
    session(b, t);
    strips(b, a);
    Pair<Boolean, Boolean> res = run(build(), t);
    assertTrue(res.getLeft());
    assertFalse(res.getRight());
  }

  @Test
  public void reflectorEchoToClient() {
    // a is a client of the route reflector rr in AS 1; rr reflects routes between its clients, but
    // not a's route back to a, which is its originator
    NodeRecord a = router("a", 1);
    NodeRecord rr = router("rr", 1);
    NodeRecord t = router("t", 3);
    external(a, "100.0.0.1", 100, TAG);
    session(a, rr);
    session(rr, t);
    strips(rr, a);
    reflector(rr, 1);
    client(rr, a);
    Pair<Boolean, Boolean> res = run(build(), t);
    assertTrue(res.getLeft());
    assertFalse(res.getRight());
  }
}
