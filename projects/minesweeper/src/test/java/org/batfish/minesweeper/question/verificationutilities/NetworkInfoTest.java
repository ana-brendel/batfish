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
import org.batfish.datamodel.bgp.BgpConfederation;
import org.batfish.datamodel.bgp.BgpTopologyUtils.ConfedSessionType;
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
      Long clusterId,
      Long confederation) {
    nf.bgpNeighborBuilder()
        .setPeerAddress(peer)
        .setLocalIp(local.getIp())
        .setLocalAs(localAs)
        .setRemoteAs(remoteAs)
        .setClusterId(clusterId)
        .setConfederation(confederation)
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
    neighbor(process, local, peer, localAs, remoteAs, false, null, null);
  }

  private void neighbor(
      BgpProcess process,
      ConcreteInterfaceAddress local,
      Ip peer,
      long localAs,
      long remoteAs,
      boolean client,
      Long clusterId) {
    neighbor(process, local, peer, localAs, remoteAs, client, clusterId, null);
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
    return info(source, configs());
  }

  private NetworkInfo info(Source source, SortedMap<String, Configuration> configs)
      throws IOException {
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

  // A confederation with AS number 100: c1 is in member AS 65001, and c2 and c3 are in member AS
  // 65002. As FRR does, each router lists only its own member AS as a member, so only the configs
  // of both ends show that a session is within the confederation. e (AS 200) is outside the
  // confederation and peers with c1. c1 also has two neighbors without configs, x (AS 300) and y
  // (AS 65001). m is outside the confederation but in AS 100, its AS number, so its session with
  // c2 is iBGP although it crosses the border. g is in member AS 65009 of another confederation,
  // 200, and peers with c1.

  private static final long CONFED = 100;
  private static final ConcreteInterfaceAddress E_C1 =
      ConcreteInterfaceAddress.parse("10.1.1.1/24");
  private static final ConcreteInterfaceAddress C1_E =
      ConcreteInterfaceAddress.parse("10.1.1.2/24");
  private static final ConcreteInterfaceAddress C1_C2 =
      ConcreteInterfaceAddress.parse("10.1.12.1/24");
  private static final ConcreteInterfaceAddress C2_C1 =
      ConcreteInterfaceAddress.parse("10.1.12.2/24");
  private static final ConcreteInterfaceAddress C2_C3 =
      ConcreteInterfaceAddress.parse("10.1.23.2/24");
  private static final ConcreteInterfaceAddress C3_C2 =
      ConcreteInterfaceAddress.parse("10.1.23.3/24");
  private static final ConcreteInterfaceAddress C1_X =
      ConcreteInterfaceAddress.parse("10.1.8.1/24");
  private static final Ip X = Ip.parse("10.1.8.2");
  private static final ConcreteInterfaceAddress C1_Y =
      ConcreteInterfaceAddress.parse("10.1.9.1/24");
  private static final Ip Y = Ip.parse("10.1.9.2");
  private static final ConcreteInterfaceAddress C2_M =
      ConcreteInterfaceAddress.parse("10.1.24.2/24");
  private static final ConcreteInterfaceAddress M_C2 =
      ConcreteInterfaceAddress.parse("10.1.24.4/24");
  private static final ConcreteInterfaceAddress C1_G =
      ConcreteInterfaceAddress.parse("10.1.15.1/24");
  private static final ConcreteInterfaceAddress G_C1 =
      ConcreteInterfaceAddress.parse("10.1.15.5/24");

  private BgpProcess confedRouter(
      ImmutableSortedMap.Builder<String, Configuration> configs,
      String name,
      String routerId,
      long confederation,
      long memberAs,
      ConcreteInterfaceAddress... addresses) {
    BgpProcess process = router(configs, name, routerId, addresses);
    process.setConfederation(new BgpConfederation(confederation, Set.of(memberAs)));
    return process;
  }

  private SortedMap<String, Configuration> confedConfigs() {
    ImmutableSortedMap.Builder<String, Configuration> builder = ImmutableSortedMap.naturalOrder();
    BgpProcess e = router(builder, "e", "9.0.0.1", E_C1);
    BgpProcess c1 =
        confedRouter(builder, "c1", "9.0.0.2", CONFED, 65001, C1_E, C1_C2, C1_X, C1_Y, C1_G);
    BgpProcess c2 = confedRouter(builder, "c2", "9.0.0.3", CONFED, 65002, C2_C1, C2_C3, C2_M);
    BgpProcess c3 = confedRouter(builder, "c3", "9.0.0.4", CONFED, 65002, C3_C2);
    BgpProcess m = router(builder, "m", "9.0.0.5", M_C2);
    BgpProcess g = confedRouter(builder, "g", "9.0.0.6", 200, 65009, G_C1);
    neighbor(e, E_C1, C1_E.getIp(), 200, CONFED);
    neighbor(c1, C1_E, E_C1.getIp(), 65001, 200, false, null, CONFED);
    neighbor(c1, C1_C2, C2_C1.getIp(), 65001, 65002, false, null, CONFED);
    neighbor(c1, C1_X, X, 65001, 300, false, null, CONFED);
    neighbor(c1, C1_Y, Y, 65001, 65001, false, null, CONFED);
    neighbor(c2, C2_C1, C1_C2.getIp(), 65002, 65001, false, null, CONFED);
    neighbor(c2, C2_C3, C3_C2.getIp(), 65002, 65002, false, null, CONFED);
    neighbor(c3, C3_C2, C2_C3.getIp(), 65002, 65002, false, null, CONFED);
    neighbor(c2, C2_M, M_C2.getIp(), 65002, CONFED, false, null, CONFED);
    neighbor(m, M_C2, C2_M.getIp(), CONFED, CONFED);
    neighbor(c1, C1_G, G_C1.getIp(), 65001, 200, false, null, CONFED);
    neighbor(g, G_C1, C1_G.getIp(), 65009, CONFED, false, null, 200L);
    return builder.build();
  }

  private void checkConfederationInfo(Source source) throws IOException {
    NetworkInfo info = info(source, confedConfigs());

    // across the border, the confederation uses its own AS number
    Edge eToC1 = incoming(info, "c1", E_C1.getIp(), C1_E.getIp());
    assertTrue(eToC1.isEBGP());
    assertEquals(Long.valueOf(200L), eToC1.getSrcAs());
    assertEquals(Long.valueOf(CONFED), eToC1.getDstAs());
    assertEquals(ConfedSessionType.ACROSS_CONFED_BORDER, eToC1.getDstConfed().type());
    Edge c1ToE = incoming(info, "e", C1_E.getIp(), E_C1.getIp());
    assertEquals(Long.valueOf(CONFED), c1ToE.getSrcAs());
    assertEquals(Long.valueOf(200L), c1ToE.getDstAs());
    assertEquals(ConfedSessionType.NO_CONFED, c1ToE.getDstConfed().type());

    // within the confederation, members use their member ASes
    Edge c1ToC2 = incoming(info, "c2", C1_C2.getIp(), C2_C1.getIp());
    assertEquals("c1", c1ToC2.getSrcNode().getName());
    assertTrue(c1ToC2.isEBGP());
    assertEquals(Long.valueOf(65001L), c1ToC2.getSrcAs());
    assertEquals(Long.valueOf(65002L), c1ToC2.getDstAs());
    assertEquals(ConfedSessionType.WITHIN_CONFED, c1ToC2.getDstConfed().type());
    Edge c2ToC3 = incoming(info, "c3", C2_C3.getIp(), C3_C2.getIp());
    assertFalse(c2ToC3.isEBGP());
    assertEquals(Long.valueOf(65002L), c2ToC3.getDstAs());
    assertEquals(ConfedSessionType.WITHIN_CONFED, c2ToC3.getDstConfed().type());

    // a session across the border with a router in the confederation's AS number is iBGP
    Edge mToC2 = incoming(info, "c2", M_C2.getIp(), C2_M.getIp());
    assertEquals("m", mToC2.getSrcNode().getName());
    assertFalse(mToC2.isEBGP());
    assertEquals(Long.valueOf(CONFED), mToC2.getDstAs());
    assertEquals(ConfedSessionType.ACROSS_CONFED_BORDER, mToC2.getDstConfed().type());
    Edge c2ToM = incoming(info, "m", C2_M.getIp(), M_C2.getIp());
    assertFalse(c2ToM.isEBGP());
    assertEquals(Long.valueOf(CONFED), c2ToM.getDstAs());

    // between two confederations, each end uses its confederation's AS number
    Edge gToC1 = incoming(info, "c1", G_C1.getIp(), C1_G.getIp());
    assertEquals("g", gToC1.getSrcNode().getName());
    assertTrue(gToC1.isEBGP());
    assertEquals(Long.valueOf(200L), gToC1.getSrcAs());
    assertEquals(Long.valueOf(CONFED), gToC1.getDstAs());
    assertEquals(ConfedSessionType.ACROSS_CONFED_BORDER, gToC1.getDstConfed().type());
    Edge c1ToG = incoming(info, "g", C1_G.getIp(), G_C1.getIp());
    assertEquals(Long.valueOf(CONFED), c1ToG.getSrcAs());
    assertEquals(Long.valueOf(200L), c1ToG.getDstAs());
    assertEquals(ConfedSessionType.ACROSS_CONFED_BORDER, c1ToG.getDstConfed().type());

    // without the sender's config, c1's own config decides: x's AS is not a member, while y is in
    // c1's own member AS
    Edge xToC1 = incoming(info, "c1", X, C1_X.getIp());
    assertEquals(Long.valueOf(CONFED), xToC1.getDstAs());
    assertEquals(ConfedSessionType.ACROSS_CONFED_BORDER, xToC1.getDstConfed().type());
    Edge yToC1 = incoming(info, "c1", Y, C1_Y.getIp());
    assertEquals(Long.valueOf(65001L), yToC1.getDstAs());
    assertEquals(ConfedSessionType.WITHIN_CONFED, yToC1.getDstConfed().type());
  }

  @Test
  public void confederationInfoFromConfigs() throws IOException {
    checkConfederationInfo(Source.CONFIGS);
  }

  @Test
  public void confederationInfoFromSnapshot() throws IOException {
    checkConfederationInfo(Source.SNAPSHOT);
  }

  @Test
  public void confederationInfoFromSnapshotWithDataPlane() throws IOException {
    checkConfederationInfo(Source.SNAPSHOT_WITH_DATA_PLANE);
  }
}
