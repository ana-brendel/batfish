package org.batfish.minesweeper.question.verificationutilities;

import static org.batfish.datamodel.Configuration.DEFAULT_VRF_NAME;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import com.google.common.collect.ImmutableSortedMap;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.ConcreteInterfaceAddress;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.expr.MatchProtocol;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.main.Batfish;
import org.batfish.main.BatfishTestUtils;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.reachability.Path;
import org.batfish.minesweeper.question.reachability.ReachabilityAnswerer;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/// Tests how NetworkInfo builds its network from configs: by the constructor that reads the BGP
/// topology from a Batfish snapshot, with and without computing the data plane, which is how the
/// reachability and isolation questions build their network; and by ofConfigs, which most tests
/// use.
///
/// The network: an external neighbor (AS 100) -> r1 (AS 1) -> r2 (AS 2) -> r3 (AS 2), with eBGP
/// sessions into r1 and r2 and an iBGP session from r2 to r3. r3 also has iBGP sessions with r4
/// and r5 (AS 2). r3 is a route reflector with cluster ID 3.3.3.3 on all its sessions, and r4 is
/// its only client.
public class NetworkInfoTest {
  /// How the network is built
  private enum Source {
    CONFIGS,
    SNAPSHOT,
    SNAPSHOT_WITH_DATA_PLANE
  }

  @Rule public TemporaryFolder _folder = new TemporaryFolder();

  private static final String IMPORT = "permitAll";
  private static final String EXPORT = "exportBgp";

  private final NetworkFactory nf = new NetworkFactory();

  private static final ConcreteInterfaceAddress R1_EXT =
      ConcreteInterfaceAddress.parse("10.0.1.1/24");
  private static final Ip EXT = Ip.parse("10.0.1.2");
  private static final ConcreteInterfaceAddress R1_R2 =
      ConcreteInterfaceAddress.parse("10.0.12.1/24");
  private static final ConcreteInterfaceAddress R2_R1 =
      ConcreteInterfaceAddress.parse("10.0.12.2/24");
  private static final ConcreteInterfaceAddress R2_R3 =
      ConcreteInterfaceAddress.parse("10.0.23.2/24");
  private static final ConcreteInterfaceAddress R3_R2 =
      ConcreteInterfaceAddress.parse("10.0.23.3/24");
  private static final ConcreteInterfaceAddress R3_R4 =
      ConcreteInterfaceAddress.parse("10.0.34.3/24");
  private static final ConcreteInterfaceAddress R4_R3 =
      ConcreteInterfaceAddress.parse("10.0.34.4/24");
  private static final ConcreteInterfaceAddress R3_R5 =
      ConcreteInterfaceAddress.parse("10.0.35.3/24");
  private static final ConcreteInterfaceAddress R5_R3 =
      ConcreteInterfaceAddress.parse("10.0.35.5/24");
  private static final Long R3_CLUSTER = Ip.parse("3.3.3.3").asLong();

  private BgpProcess router(
      ImmutableSortedMap.Builder<String, Configuration> configs,
      String name,
      String routerId,
      ConcreteInterfaceAddress... addresses) {
    Configuration config =
        nf.configurationBuilder()
            .setHostname(name)
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .build();
    Vrf vrf = nf.vrfBuilder().setName(DEFAULT_VRF_NAME).setOwner(config).build();
    for (int i = 0; i < addresses.length; i++) {
      nf.interfaceBuilder()
          .setName("eth" + i)
          .setAddress(addresses[i])
          .setVrf(vrf)
          .setOwner(config)
          .build();
    }
    nf.routingPolicyBuilder()
        .setOwner(config)
        .setName(IMPORT)
        .setStatements(permitRoute(true))
        .build();
    // export only BGP routes: exporting a router's own connected and local routes would give its
    // peers BGP routes to its session addresses that cannot resolve, so the sessions would not
    // be established in the data plane
    nf.routingPolicyBuilder()
        .setOwner(config)
        .setName(EXPORT)
        .setStatements(
            ifStatement(
                new MatchProtocol(RoutingProtocol.BGP, RoutingProtocol.IBGP),
                permitRoute(true),
                permitRoute(false)))
        .build();
    configs.put(name, config);
    return nf.bgpProcessBuilder()
        .setRouterId(Ip.parse(routerId))
        .setEbgpAdminCost(20)
        .setIbgpAdminCost(200)
        .setLocalAdminCost(200)
        .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
        .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setVrf(vrf)
        .build();
  }

  /// A neighbor that is a route-reflector client if client is true, with the given cluster ID
  private void neighbor(
      BgpProcess process,
      ConcreteInterfaceAddress local,
      Ip peer,
      long localAs,
      long remoteAs,
      boolean client,
      Long clusterId) {
    nf.bgpNeighborBuilder()
        .setPeerAddress(peer)
        .setLocalIp(local.getIp())
        .setLocalAs(localAs)
        .setRemoteAs(remoteAs)
        .setClusterId(clusterId)
        .setBgpProcess(process)
        .setIpv4UnicastAddressFamily(
            Ipv4UnicastAddressFamily.builder()
                .setImportPolicy(IMPORT)
                .setExportPolicy(EXPORT)
                .setRouteReflectorClient(client)
                .build())
        .build();
  }

  private void neighbor(
      BgpProcess process, ConcreteInterfaceAddress local, Ip peer, long localAs, long remoteAs) {
    neighbor(process, local, peer, localAs, remoteAs, false, null);
  }

  private SortedMap<String, Configuration> configs() {
    ImmutableSortedMap.Builder<String, Configuration> builder = ImmutableSortedMap.naturalOrder();
    BgpProcess r1 = router(builder, "r1", "1.1.1.1", R1_EXT, R1_R2);
    BgpProcess r2 = router(builder, "r2", "2.2.2.2", R2_R1, R2_R3);
    BgpProcess r3 = router(builder, "r3", "3.3.3.3", R3_R2, R3_R4, R3_R5);
    BgpProcess r4 = router(builder, "r4", "4.4.4.4", R4_R3);
    BgpProcess r5 = router(builder, "r5", "5.5.5.5", R5_R3);
    neighbor(r1, R1_EXT, EXT, 1, 100);
    neighbor(r1, R1_R2, R2_R1.getIp(), 1, 2);
    neighbor(r2, R2_R1, R1_R2.getIp(), 2, 1);
    neighbor(r2, R2_R3, R3_R2.getIp(), 2, 2);
    neighbor(r3, R3_R2, R2_R3.getIp(), 2, 2, false, R3_CLUSTER);
    neighbor(r3, R3_R4, R4_R3.getIp(), 2, 2, true, R3_CLUSTER);
    neighbor(r3, R3_R5, R5_R3.getIp(), 2, 2, false, R3_CLUSTER);
    neighbor(r4, R4_R3, R3_R4.getIp(), 2, 2);
    neighbor(r5, R5_R3, R3_R5.getIp(), 2, 2);
    return builder.build();
  }

  private NetworkInfo info(Source source) throws IOException {
    SortedMap<String, Configuration> configs = configs();
    if (source == Source.CONFIGS) {
      TransferBDD tbdd =
          new TransferBDD(getConfigAtomicPredicates(Set.of(), Set.of(), configs.values()));
      return NetworkInfo.ofConfigs(tbdd, configs);
    }
    Batfish batfish = BatfishTestUtils.getBatfish(configs, _folder);
    return new NetworkInfo(
        batfish,
        batfish.getSnapshot(),
        Set.of(),
        Set.of(),
        null,
        false,
        source == Source.SNAPSHOT_WITH_DATA_PLANE);
  }

  private static Edge incoming(NetworkInfo info, String node, Ip from, Ip to) {
    Node n = info.getNodeByName(node).orElseThrow();
    return n.getIncoming(from, to).orElseThrow();
  }

  private void checkSessionInfo(Source source) throws IOException {
    NetworkInfo info = info(source);

    Edge extToR1 = incoming(info, "r1", EXT, R1_EXT.getIp());
    // an edge is linked to its source node only if the source has a config: from the BGP topology
    // when reading a snapshot, and from the configs' IPs in ofConfigs
    assertNull(extToR1.getSrcNode());
    assertTrue(extToR1.isEBGP());
    assertEquals(Long.valueOf(100L), extToR1.getSrcAs());
    assertEquals(Long.valueOf(1L), extToR1.getDstAs());

    Edge r1ToR2 = incoming(info, "r2", R1_R2.getIp(), R2_R1.getIp());
    assertEquals("r1", r1ToR2.getSrcNode().getName());
    assertTrue(r1ToR2.isEBGP());
    assertEquals(Long.valueOf(1L), r1ToR2.getSrcAs());
    assertEquals(Long.valueOf(2L), r1ToR2.getDstAs());

    Edge r2ToR3 = incoming(info, "r3", R2_R3.getIp(), R3_R2.getIp());
    assertEquals("r2", r2ToR3.getSrcNode().getName());
    assertFalse(r2ToR3.isEBGP());
    assertEquals(Long.valueOf(2L), r2ToR3.getSrcAs());
    assertEquals(Long.valueOf(2L), r2ToR3.getDstAs());

    // route reflection, as configured at each receiver
    assertFalse(r2ToR3.dstTreatsSrcAsClient());
    assertEquals(R3_CLUSTER, r2ToR3.getDstClusterId());
    Edge r4ToR3 = incoming(info, "r3", R4_R3.getIp(), R3_R4.getIp());
    assertTrue(r4ToR3.dstTreatsSrcAsClient());
    assertEquals(R3_CLUSTER, r4ToR3.getDstClusterId());
    Edge r3ToR4 = incoming(info, "r4", R3_R4.getIp(), R4_R3.getIp());
    assertFalse(r3ToR4.dstTreatsSrcAsClient());
    assertNull(r3ToR4.getDstClusterId());
    Node r3 = info.getNodeByName("r3").orElseThrow();
    assertTrue(r3.clientToClientReflection());
    assertEquals(Set.of(R3_CLUSTER), r3.getClusterIds());
    assertEquals(Set.of(), info.getNodeByName("r4").orElseThrow().getClusterIds());
  }

  @Test
  public void sessionInfoFromConfigs() throws IOException {
    checkSessionInfo(Source.CONFIGS);
  }

  @Test
  public void sessionInfoFromSnapshot() throws IOException {
    checkSessionInfo(Source.SNAPSHOT);
  }

  @Test
  public void sessionInfoFromSnapshotWithDataPlane() throws IOException {
    checkSessionInfo(Source.SNAPSHOT_WITH_DATA_PLANE);
  }

  private static final PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromString("2.4.8.0/24"));

  private static boolean goodPathTo(NetworkInfo info, String target) {
    TableAnswerElement result =
        ReachabilityAnswerer.run(
            info,
            PREFIX,
            info.getNodeByName(target).orElseThrow(),
            new Invariant(info.tbdd),
            Set.of());
    List<Row> rows = result.getRowsList();
    return rows.stream().anyMatch(row -> row.getString("Result_Label").equals("Good Path"));
  }

  /// The good path found to r3, ordered from r3 back to the origin
  private static Location[] pathToR3(NetworkInfo info) {
    Path path =
        info.toPathExploration(
                PREFIX,
                info.getNodeByName("r3").orElseThrow(),
                new Invariant(info.tbdd),
                Set.of(),
                new HashMap<>())
            .run()
            .getKey();
    assertNotNull(path);
    return path.getLocations();
  }

  private void checkReachability(Source source) throws IOException {
    NetworkInfo info = info(source);
    // the path from the external neighbor to r3 is eBGP, eBGP, then iBGP, which BGP allows
    assertTrue(goodPathTo(info, "r3"));
    Location[] path = pathToR3(info);
    assertEquals(EXT, ((Edge) path[path.length - 1]).getSrc());
    assertEquals("r1", ((Node) path[path.length - 2]).getName());
    // r3 does not reflect a route from its non-client r2 to its non-client r5
    assertFalse(goodPathTo(info, "r5"));
    // r3 reflects the route from its non-client r2 to its client r4
    assertTrue(goodPathTo(info, "r4"));
  }

  @Test
  public void reachabilityFromConfigs() throws IOException {
    checkReachability(Source.CONFIGS);
  }

  @Test
  public void reachabilityFromSnapshot() throws IOException {
    checkReachability(Source.SNAPSHOT);
  }

  @Test
  public void reachabilityFromSnapshotWithDataPlane() throws IOException {
    checkReachability(Source.SNAPSHOT_WITH_DATA_PLANE);
  }
}
