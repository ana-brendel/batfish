package org.batfish.minesweeper.question.reachability;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import com.google.common.collect.ImmutableSortedMap;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.AddressFamilyCapabilities;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.Networkv2;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
import org.junit.Before;
import org.junit.Test;

/// Tests that path exploration only uses paths that BGP's loop prevention allows. Every router
/// accepts and advertises every route, and a route for the prefix enters at an external neighbor of
/// router a.
public class PathExplorationLoopTest {
  private static final String POLICY = "permitAll";
  private static final String DENY = "denyAll";
  private static final String PREFIX = "2.4.8.0/24";
  private static final PrefixSpace PREFIX_SPACE =
      new PrefixSpace(PrefixRange.fromString(PREFIX));

  private final NetworkFactory nf = new NetworkFactory();
  private Map<NodeRecord, Configuration> configs;
  private Map<NodeRecord, Long> ases;
  private Map<NodeRecord, Map<Ip, PeerSpec>> neighbors;
  private Map<NodeRecord, Long> clusterIds;
  private Map<NodeRecord, Set<NodeRecord>> clients;
  private Set<NodeRecord> noClientToClient;
  private RoutingPolicy template;
  private int nextRouter;

  @Before
  public void setup() {
    configs = new LinkedHashMap<>();
    ases = new HashMap<>();
    neighbors = new HashMap<>();
    clusterIds = new HashMap<>();
    clients = new HashMap<>();
    noClientToClient = new HashSet<>();
    nextRouter = 1;
  }

  /// A router in the given AS; a null AS leaves its sessions without AS numbers
  private NodeRecord router(String name, Long as) {
    NodeRecord node = new NodeRecord("10.0.0." + nextRouter++, name);
    Configuration config =
        nf.configurationBuilder()
            .setHostname(name)
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .setDefaultInboundAction(PERMIT)
            .build();
    template =
        nf.routingPolicyBuilder()
            .setOwner(config)
            .setName(POLICY)
            .setStatements(permitRoute(true))
            .build();
    nf.routingPolicyBuilder()
        .setOwner(config)
        .setName(DENY)
        .setStatements(permitRoute(false))
        .build();
    configs.put(node, config);
    ases.put(node, as);
    neighbors.put(node, new HashMap<>());
    return node;
  }

  /// A configured neighbor: a router, or an external neighbor (null) that is a route-reflector
  /// client if externalClient is true. A null remote AS is left unconfigured.
  private record PeerSpec(
      NodeRecord neighbor,
      Long remoteAs,
      boolean allowLocalAsIn,
      String importPolicy,
      boolean externalClient) {}

  /// A peer with the given settings; a null AS or cluster ID is left unconfigured
  private BgpActivePeerConfig peer(
      Long localAs,
      Long remoteAs,
      boolean allowLocalAsIn,
      String importPolicy,
      boolean client,
      Long clusterId) {
    BgpActivePeerConfig.Builder builder =
        BgpActivePeerConfig.builder().setLocalAs(localAs).setClusterId(clusterId);
    if (remoteAs != null) {
      builder.setRemoteAs(remoteAs);
    }
    return builder
        .setIpv4UnicastAddressFamily(
            Ipv4UnicastAddressFamily.builder()
                .setAddressFamilyCapabilities(
                    AddressFamilyCapabilities.builder().setAllowLocalAsIn(allowLocalAsIn).build())
                .setImportPolicy(importPolicy)
                .setExportPolicy(POLICY)
                .setRouteReflectorClient(client)
                .build())
        .build();
  }

  /// A BGP session between a and b; iBGP if they are in the same AS
  private void session(NodeRecord a, NodeRecord b, boolean bAllowsLocalAsIn) {
    neighbors.get(a).put(b.getIp(), new PeerSpec(b, ases.get(b), false, POLICY, false));
    neighbors
        .get(b)
        .put(a.getIp(), new PeerSpec(a, ases.get(a), bAllowsLocalAsIn, POLICY, false));
  }

  /// Makes the receiver's session with the sender reject every route
  private void denyImport(NodeRecord receiver, NodeRecord sender) {
    neighbors
        .get(receiver)
        .put(sender.getIp(), new PeerSpec(sender, ases.get(sender), false, DENY, false));
  }

  /// Makes the router a route reflector that uses the given cluster ID on all its sessions
  private void reflector(NodeRecord router, long clusterId) {
    clusterIds.put(router, clusterId);
  }

  /// Makes the client a route-reflector client of the reflector
  private void client(NodeRecord reflector, NodeRecord client) {
    clients.computeIfAbsent(reflector, k -> new HashSet<>()).add(client);
  }

  /// Turns off reflection between the router's route-reflector clients
  private void noClientToClient(NodeRecord router) {
    noClientToClient.add(router);
  }

  private void session(NodeRecord a, NodeRecord b) {
    session(a, b, false);
  }

  /// A session from an external neighbor (no config) into a, which a treats as a route-reflector
  /// client if client is true
  private void external(NodeRecord a, String ip, Long externalAs, boolean client) {
    neighbors.get(a).put(Ip.parse(ip), new PeerSpec(null, externalAs, false, POLICY, client));
  }

  private void external(NodeRecord a, String ip, Long externalAs) {
    external(a, ip, externalAs, false);
  }

  private Networkv2 build() {
    for (NodeRecord node : configs.keySet()) {
      Vrf vrf =
          nf.vrfBuilder()
              .setOwner(configs.get(node))
              .setName(Configuration.DEFAULT_VRF_NAME)
              .build();
      nf.bgpProcessBuilder()
          .setRouterId(node.getIp())
          .setEbgpAdminCost(0)
          .setIbgpAdminCost(0)
          .setLocalAdminCost(0)
          .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
          .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
          .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
          .setClientToClientReflection(!noClientToClient.contains(node))
          .setVrf(vrf)
          .build()
          .setNeighbors(ImmutableSortedMap.copyOf(peers(node)));
    }
    TransferBDD tbdd =
        new TransferBDD(getConfigAtomicPredicates(Set.of(), Set.of(), configs.values()));
    return new Networkv2(tbdd, configs, template, List.of());
  }

  private Map<Ip, BgpActivePeerConfig> peers(NodeRecord node) {
    Map<Ip, BgpActivePeerConfig> peers = new HashMap<>();
    neighbors
        .get(node)
        .forEach(
            (ip, spec) ->
                peers.put(
                    ip,
                    peer(
                        ases.get(node),
                        spec.remoteAs(),
                        spec.allowLocalAsIn(),
                        spec.importPolicy(),
                        spec.neighbor() == null
                            ? spec.externalClient()
                            : clients.getOrDefault(node, Set.of()).contains(spec.neighbor()),
                        clusterIds.get(node))));
    return peers;
  }

  /// Whether the answerer finds a good path for the prefix to the given router
  private boolean goodPathTo(Networkv2 net, NodeRecord target) {
    NetworkInfo info = net.getInfo(PREFIX_SPACE);
    TableAnswerElement result =
        ReachabilityAnswerer.run(
            info, PREFIX_SPACE, target.instantiate(info), new Invariant(net.tbdd()), Set.of());
    for (Row row : result.getRowsList()) {
      if (row.getString("Result_Label").equals("Good Path")) {
        return true;
      }
    }
    return false;
  }

  /// The good path path exploration finds to the given router, ordered from the target back
  private Location[] explore(Networkv2 net, NodeRecord target) {
    NetworkInfo info = net.getInfo(PREFIX_SPACE);
    Path path =
        info.toPathExploration(
                PREFIX_SPACE,
                target.instantiate(info),
                new Invariant(net.tbdd()),
                Set.of(),
                new HashMap<>())
            .run()
            .getKey();
    assertNotNull(path);
    return path.getLocations();
  }

  private static boolean visits(Location[] path, NodeRecord node) {
    return Arrays.stream(path)
        .anyMatch(l -> l instanceof Node n && n.getName().equalsIgnoreCase(node.name()));
  }

  @Test
  public void reenteringAnAsHasNoPath() {
    // the only path to c leaves AS 1 at a and re-enters it at c, which rejects the route
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 2L);
    NodeRecord c = router("c", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, c);
    assertFalse(goodPathTo(build(), c));
  }

  @Test
  public void reenteringAnAsWithAllowAsInHasPath() {
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 2L);
    NodeRecord c = router("c", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, c, true);
    assertTrue(goodPathTo(build(), c));
  }

  @Test
  public void twoIbgpHopsHasNoPath() {
    // without a full mesh or route reflection, b does not pass a's iBGP route on to c
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord c = router("c", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, c);
    assertFalse(goodPathTo(build(), c));
  }

  @Test
  public void unknownAsesHavePath() {
    // sessions without AS numbers are marked iBGP by NetworkInfo, but their type is unknown, so
    // the path is not ruled out
    NodeRecord a = router("a", null);
    NodeRecord b = router("b", null);
    NodeRecord c = router("c", null);
    external(a, "100.0.0.1", null);
    session(a, b);
    session(b, c);
    assertTrue(goodPathTo(build(), c));
  }

  @Test
  public void oneIbgpHopHasPath() {
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    assertTrue(goodPathTo(build(), b));
  }

  @Test
  public void longerPathAroundTwoIbgpHops() {
    // the shortest path to c, a -> b -> e -> c, takes two iBGP hops; the longer path through f, g,
    // and h is the one BGP allows
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord e = router("e", 1L);
    NodeRecord c = router("c", 3L);
    NodeRecord f = router("f", 4L);
    NodeRecord g = router("g", 5L);
    NodeRecord h = router("h", 6L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, e);
    session(e, c);
    session(a, f);
    session(f, g);
    session(g, h);
    session(h, c);
    Location[] path = explore(build(), c);
    assertTrue(new BgpPathValidity(Map.of(), Map.of()).isValid(path));
    assertTrue(visits(path, f));
  }

  @Test
  public void longerPathAroundAsReentry() {
    // the shortest path to c, a -> b -> e -> c, re-enters AS 1 at e; the longer path through f,
    // g, and h avoids it
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 2L);
    NodeRecord e = router("e", 1L);
    NodeRecord c = router("c", 3L);
    NodeRecord f = router("f", 4L);
    NodeRecord g = router("g", 5L);
    NodeRecord h = router("h", 6L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, e);
    session(e, c);
    session(a, f);
    session(f, g);
    session(g, h);
    session(h, c);
    Location[] path = explore(build(), c);
    assertTrue(new BgpPathValidity(Map.of(), Map.of()).isValid(path));
    assertTrue(visits(path, f));
  }

  @Test
  public void fullMeshUsesDirectSession() {
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord c = router("c", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, c);
    session(a, c);
    Networkv2 net = build();
    assertTrue(goodPathTo(net, c));
    Location[] path = explore(net, c);
    assertTrue(new BgpPathValidity(Map.of(), Map.of()).isValid(path));
    assertFalse(visits(path, b));
  }

  @Test
  public void fullMeshWithFilteredDirectSessionHasNoPath() {
    // c rejects the route from a, and b does not relay a's iBGP route to c
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord c = router("c", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, c);
    session(a, c);
    denyImport(c, a);
    assertFalse(goodPathTo(build(), c));
  }

  @Test
  public void transitThroughAs() {
    // the route crosses AS 1 over one iBGP hop and leaves over eBGP
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord c = router("c", 2L);
    external(a, "100.0.0.1", 100L);
    session(a, b);
    session(b, c);
    Networkv2 net = build();
    assertTrue(goodPathTo(net, c));
    assertTrue(visits(explore(net, c), b));
  }

  @Test
  public void ibgpNeighborWithoutConfigCannotBeRelayed() {
    // the route arrives at a from an iBGP neighbor we have no config for, so a does not pass it
    // to its iBGP peer b
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 1L);
    session(a, b);
    assertFalse(goodPathTo(build(), b));
  }

  @Test
  public void longerPathEnteringAsElsewhere() {
    // t is in AS 1; the shortest path, x -> a -> b -> t, enters AS 1 at a and then takes two iBGP
    // hops, while the longer path through y and z enters AS 1 at b, one iBGP hop from t
    NodeRecord x = router("x", 2L);
    NodeRecord a = router("a", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord t = router("t", 1L);
    NodeRecord y = router("y", 3L);
    NodeRecord z = router("z", 4L);
    external(x, "100.0.0.1", 100L);
    session(x, a);
    session(a, b);
    session(b, t);
    session(x, y);
    session(y, z);
    session(z, b);
    Location[] path = explore(build(), t);
    assertTrue(new BgpPathValidity(Map.of(), Map.of()).isValid(path));
    assertTrue(visits(path, y));
    assertFalse(visits(path, a));
  }

  // Route reflection. In each test, a, the reflectors, and b are in AS 1, and a route enters at a
  // from an external neighbor in AS 100.

  @Test
  public void reflectFromClientToNonClient() {
    NodeRecord a = router("a", 1L);
    NodeRecord rr = router("rr", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr);
    session(rr, b);
    reflector(rr, 1);
    client(rr, a);
    assertTrue(goodPathTo(build(), b));
  }

  @Test
  public void reflectFromNonClientToClient() {
    NodeRecord a = router("a", 1L);
    NodeRecord rr = router("rr", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr);
    session(rr, b);
    reflector(rr, 1);
    client(rr, b);
    assertTrue(goodPathTo(build(), b));
  }

  @Test
  public void noReflectionFromNonClientToNonClient() {
    NodeRecord a = router("a", 1L);
    NodeRecord rr = router("rr", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord c = router("c", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr);
    session(rr, b);
    session(rr, c);
    reflector(rr, 1);
    // rr has a client, but neither a nor b is one
    client(rr, c);
    assertFalse(goodPathTo(build(), b));
  }

  @Test
  public void reflectBetweenClients() {
    NodeRecord a = router("a", 1L);
    NodeRecord rr = router("rr", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr);
    session(rr, b);
    reflector(rr, 1);
    client(rr, a);
    client(rr, b);
    assertTrue(goodPathTo(build(), b));
  }

  @Test
  public void noReflectionBetweenClientsWithoutClientToClient() {
    NodeRecord a = router("a", 1L);
    NodeRecord rr = router("rr", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr);
    session(rr, b);
    reflector(rr, 1);
    client(rr, a);
    client(rr, b);
    noClientToClient(rr);
    assertFalse(goodPathTo(build(), b));
  }

  @Test
  public void reflectRouteFromUnconfiguredClient() {
    // the route arrives at rr from an iBGP neighbor we have no config for, which rr treats as a
    // client, so rr reflects it to its non-client b
    NodeRecord rr = router("rr", 1L);
    NodeRecord b = router("b", 1L);
    external(rr, "100.0.0.1", 1L, true);
    session(rr, b);
    reflector(rr, 1);
    assertTrue(goodPathTo(build(), b));
  }

  @Test
  public void reflectorHierarchyWithDifferentClusters() {
    // a is a client of rr1, which is a client of rr2, which reflects to its non-client b
    NodeRecord a = router("a", 1L);
    NodeRecord rr1 = router("rr1", 1L);
    NodeRecord rr2 = router("rr2", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr1);
    session(rr1, rr2);
    session(rr2, b);
    reflector(rr1, 1);
    reflector(rr2, 2);
    client(rr1, a);
    client(rr2, rr1);
    assertTrue(goodPathTo(build(), b));
  }

  @Test
  public void noReflectionThroughTwoReflectorsInOneCluster() {
    // as above, but rr1 and rr2 share a cluster, so rr2 rejects the route rr1 reflects to it
    NodeRecord a = router("a", 1L);
    NodeRecord rr1 = router("rr1", 1L);
    NodeRecord rr2 = router("rr2", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr1);
    session(rr1, rr2);
    session(rr2, b);
    reflector(rr1, 1);
    reflector(rr2, 1);
    client(rr1, a);
    client(rr2, rr1);
    assertFalse(goodPathTo(build(), b));
  }

  @Test
  public void redundantReflectorsInOneCluster() {
    // a and b are clients of both rr1 and rr2, which share a cluster; b gets the route through
    // either reflector alone, never through both
    NodeRecord a = router("a", 1L);
    NodeRecord rr1 = router("rr1", 1L);
    NodeRecord rr2 = router("rr2", 1L);
    NodeRecord b = router("b", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr1);
    session(a, rr2);
    session(rr1, b);
    session(rr2, b);
    session(rr1, rr2);
    reflector(rr1, 1);
    reflector(rr2, 1);
    client(rr1, a);
    client(rr1, b);
    client(rr2, a);
    client(rr2, b);
    Networkv2 net = build();
    assertTrue(goodPathTo(net, b));
    Location[] path = explore(net, b);
    assertFalse(visits(path, rr1) && visits(path, rr2));
  }

  @Test
  public void longerPathThroughReflectors() {
    // rr1 treats a and b as non-clients, so the shortest path a -> rr1 -> b is not allowed; the
    // longer path a -> rr2 -> rr3 -> b is, with a a client of rr2 and rr2 a client of rr3
    NodeRecord a = router("a", 1L);
    NodeRecord rr1 = router("rr1", 1L);
    NodeRecord rr2 = router("rr2", 1L);
    NodeRecord rr3 = router("rr3", 1L);
    NodeRecord b = router("b", 1L);
    NodeRecord c = router("c", 1L);
    external(a, "100.0.0.1", 100L);
    session(a, rr1);
    session(rr1, b);
    session(rr1, c);
    session(a, rr2);
    session(rr2, rr3);
    session(rr3, b);
    reflector(rr1, 1);
    reflector(rr2, 2);
    reflector(rr3, 3);
    client(rr1, c);
    client(rr2, a);
    client(rr3, rr2);
    Location[] path = explore(build(), b);
    assertTrue(visits(path, rr2));
    assertFalse(visits(path, rr1));
  }
}
