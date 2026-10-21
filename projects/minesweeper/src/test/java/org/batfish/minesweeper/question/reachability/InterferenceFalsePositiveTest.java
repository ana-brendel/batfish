package org.batfish.minesweeper.question.reachability;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.BgpProcess;
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
import org.batfish.datamodel.routing_policy.expr.LiteralLong;
import org.batfish.datamodel.routing_policy.statement.SetLocalPreference;
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Pure reachability queries (target = true at node T, prefix 2.4.8.0/24) on which the interference
 * check of ReachabilityAnswerer.run is too strong: it reports interference although, in real BGP,
 * T always ends up with a route for the prefix. See INTERFERENCE_FALSE_POSITIVES.md in
 * projects/minesweeper for the explanation of each case.
 *
 * <p>Each test asserts that a good path is found and that the interference verdict equals the
 * ground truth for real BGP (worked out by hand for the all-eBGP version of the network; see the
 * comment on each spec). Where the check currently reports a false positive, the interference
 * assertion is commented out with a TODO and only the good path is asserted.
 *
 * <p>Base network (all variants are small edits of it):
 *
 * <pre>
 *   E1 (100.0.0.10) --import: clear all communities--> A --import: deny 2:2, else permit--> T
 *   E2 (100.0.0.20) --import: permit unchanged--------> A
 *                                                       A --permit--> B --permit--> T
 * </pre>
 *
 * All other imports/exports permit everything; every session is configured on both ends.
 */
public class InterferenceFalsePositiveTest {
  private static final NetworkFactory nf = new NetworkFactory();
  private static final String PREFIX = "2.4.8.0/24";
  private static final String COMM = "2:2";

  private static final NodeRecord A_R = new NodeRecord("10.0.0.1", "aNode");
  private static final NodeRecord B_R = new NodeRecord("10.0.0.2", "bNode");
  private static final NodeRecord T_R = new NodeRecord("10.0.0.3", "tNode");
  private static final Ip E1_IP = Ip.parse("100.0.0.10");
  private static final Ip E2_IP = Ip.parse("100.0.0.20");
  private static final Ip A2_IP = Ip.parse("10.0.1.1");
  private static final Ip T2_IP = Ip.parse("10.0.1.3");

  /** How AS numbers are assigned to the sessions. */
  enum Sessions {
    /** No AS numbers at all (what the existing unit tests do); the tool treats these as iBGP. */
    NO_AS,
    /** A=65001, B=65002, T=65003, E1=65100, E2=65200: every session is eBGP. */
    EBGP,
    /** A, B, T share AS 65000 (iBGP full mesh among them); E1=65100, E2=65200 are eBGP. */
    IBGP_CORE
  }

  /** Where the second external neighbor E2 attaches. */
  enum E2At {
    NONE,
    A,
    B
  }

  record Spec(
      String name,
      boolean withB, // second path A -> B -> T (sessions A-B and B-T)
      E2At e2At, // where E2 attaches
      boolean e2Clears, // E2's import also clears communities (control)
      boolean e2LowerLocalPref, // E1 import sets LP 200, E2 import sets LP 50
      boolean tTagsExportToA, // T's export back to A adds 2:2
      boolean tDeniesFromB, // T's import from B also denies 2:2
      Sessions sessions,
      boolean ingressE1Only, // pass {E1 -> A} as the ingress set instead of {}
      Boolean realInterference,
      // 0: single A-T session; 1: add a second A-T session (10.0.1.1 <-> 10.0.1.3) whose imports
      // permit all; 2: same two sessions but T's 2:2 filter is on the second session instead
      int parallelAT) {

    Spec(
        String name,
        boolean withB,
        E2At e2At,
        boolean e2Clears,
        boolean e2LowerLocalPref,
        boolean tTagsExportToA,
        boolean tDeniesFromB,
        Sessions sessions,
        boolean ingressE1Only,
        Boolean realInterference) {
      this(
          name,
          withB,
          e2At,
          e2Clears,
          e2LowerLocalPref,
          tTagsExportToA,
          tDeniesFromB,
          sessions,
          ingressE1Only,
          realInterference,
          0);
    }

    Spec with(Sessions s) {
      return new Spec(
          name + "/" + s,
          withB,
          e2At,
          e2Clears,
          e2LowerLocalPref,
          tTagsExportToA,
          tDeniesFromB,
          s,
          ingressE1Only,
          null,
          parallelAT);
    }
  }

  // ---------------------------------------------------------------------------------------------
  // entry point
  // ---------------------------------------------------------------------------------------------

  private static TableAnswerElement runQuery(
      NetworkInfo info, PrefixSpace prefix, Node target, Invariant inv, Set<Edge> ingress) {
    return ReachabilityAnswerer.run(info, prefix, target, inv, ingress);
  }

  // ---------------------------------------------------------------------------------------------
  // helpers copied from LivenessAnswererTest / ReachabilityAnswererTest
  // ---------------------------------------------------------------------------------------------

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
      String imp, String exp, Long localAs, Long remoteAs) {
    if (localAs == null) {
      return getBgpActivePeerConfig("g", imp, exp);
    }
    return BgpActivePeerConfig.builder()
        .setGroup("g")
        .setLocalAs(localAs)
        .setRemoteAs(remoteAs)
        .setIpv4UnicastAddressFamily(
            Ipv4UnicastAddressFamily.builder().setImportPolicy(imp).setExportPolicy(exp).build())
        .build();
  }

  /** Same as peer(...) but with an explicit local IP (used for the parallel A-T session). */
  private static BgpActivePeerConfig peerWithLocalIp(
      String imp, String exp, Long localAs, Long remoteAs, Ip localIp) {
    if (localAs == null) {
      return BgpActivePeerConfig.builder()
          .setGroup("g")
          .setLocalIp(localIp)
          .setIpv4UnicastAddressFamily(
              Ipv4UnicastAddressFamily.builder().setImportPolicy(imp).setExportPolicy(exp).build())
          .build();
    }
    return BgpActivePeerConfig.builder()
        .setGroup("g")
        .setLocalIp(localIp)
        .setLocalAs(localAs)
        .setRemoteAs(remoteAs)
        .setIpv4UnicastAddressFamily(
            Ipv4UnicastAddressFamily.builder().setImportPolicy(imp).setExportPolicy(exp).build())
        .build();
  }

  private static Long as(String who, Sessions s) {
    switch (s) {
      case NO_AS:
        return null;
      case EBGP:
        switch (who) {
          case "A":
            return 65001L;
          case "B":
            return 65002L;
          case "T":
            return 65003L;
          case "E1":
            return 65100L;
          default:
            return 65200L;
        }
      default: // IBGP_CORE
        switch (who) {
          case "E1":
            return 65100L;
          case "E2":
            return 65200L;
          default:
            return 65000L;
        }
    }
  }

  // ---------------------------------------------------------------------------------------------
  // the network builder
  // ---------------------------------------------------------------------------------------------

  TestConfigConstructionUtils.Networkv2 build(Spec s) {
    assert s.e2At() != E2At.B || s.withB();
    Map<NodeRecord, Configuration> configs = new HashMap<>();
    List<NodeRecord> nodes = s.withB() ? List.of(A_R, B_R, T_R) : List.of(A_R, T_R);
    for (NodeRecord n : nodes) {
      Configuration c =
          nf.configurationBuilder()
              .setHostname(n.name())
              .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
              .setDefaultInboundAction(PERMIT)
              .build();
      includeCommunities(c, "^" + COMM + "$");
      configs.put(n, c);
    }
    Map<NodeRecord, BgpProcess> procs = new HashMap<>();
    for (NodeRecord n : nodes) {
      procs.put(n, getBgpProcess(configs.get(n), n));
    }

    Long asA = as("A", s.sessions());
    Long asB = as("B", s.sessions());
    Long asT = as("T", s.sessions());
    Long asE1 = as("E1", s.sessions());
    Long asE2 = as("E2", s.sessions());

    String permitAll = "permitAll";
    String e1Import = "e1Import";
    String e2Import = "e2Import";
    String tImportFromA = "tImportFromA";
    String tImportFromB = "tImportFromB";
    String tExportToA = "tExportToA";

    // ---- A
    Map<Ip, BgpActivePeerConfig> aN = new TreeMap<>();
    aN.put(E1_IP, peer(e1Import, permitAll, asA, asE1));
    if (s.e2At() == E2At.A) {
      aN.put(E2_IP, peer(e2Import, permitAll, asA, asE2));
    }
    aN.put(T_R.getIp(), peer(permitAll, permitAll, asA, asT));
    if (s.withB()) {
      aN.put(B_R.getIp(), peer(permitAll, permitAll, asA, asB));
    }
    if (s.parallelAT() > 0) {
      aN.put(T2_IP, peerWithLocalIp(permitAll, permitAll, asA, asT, A2_IP));
    }
    procs.get(A_R).setNeighbors(ImmutableSortedMap.copyOf(aN));

    // ---- T
    Map<Ip, BgpActivePeerConfig> tN = new TreeMap<>();
    tN.put(
        A_R.getIp(),
        peer(
            s.parallelAT() == 2 ? permitAll : tImportFromA,
            s.tTagsExportToA() ? tExportToA : permitAll,
            asT,
            asA));
    if (s.withB()) {
      tN.put(B_R.getIp(), peer(s.tDeniesFromB() ? tImportFromB : permitAll, permitAll, asT, asB));
    }
    if (s.parallelAT() > 0) {
      tN.put(
          A2_IP,
          peerWithLocalIp(
              s.parallelAT() == 2 ? tImportFromA : permitAll, permitAll, asT, asA, T2_IP));
    }
    procs.get(T_R).setNeighbors(ImmutableSortedMap.copyOf(tN));

    // ---- B
    if (s.withB()) {
      Map<Ip, BgpActivePeerConfig> bN = new TreeMap<>();
      bN.put(A_R.getIp(), peer(permitAll, permitAll, asB, asA));
      bN.put(T_R.getIp(), peer(permitAll, permitAll, asB, asT));
      if (s.e2At() == E2At.B) {
        bN.put(E2_IP, peer(e2Import, permitAll, asB, asE2));
      }
      procs.get(B_R).setNeighbors(ImmutableSortedMap.copyOf(bN));
    }

    // ---- policies
    Configuration a = configs.get(A_R);
    RoutingPolicy template = makePolicy(a, permitAll, permitRoute(true));
    List<Statement> e1Body = new ArrayList<>(clearCommunities());
    if (s.e2LowerLocalPref()) {
      e1Body.add(0, new SetLocalPreference(new LiteralLong(200L)));
    }
    makePolicy(a, e1Import, e1Body);

    List<Statement> e2Body;
    if (s.e2Clears()) {
      e2Body = new ArrayList<>(clearCommunities());
    } else {
      e2Body = new ArrayList<>(permitRoute(true));
    }
    if (s.e2LowerLocalPref()) {
      e2Body.add(0, new SetLocalPreference(new LiteralLong(50L)));
    }
    if (s.e2At() == E2At.A) {
      makePolicy(a, e2Import, e2Body);
    }

    Configuration t = configs.get(T_R);
    makePolicy(t, permitAll, permitRoute(true));
    makePolicy(
        t,
        tImportFromA,
        ifStatement(checkForCommunity(COMM), permitRoute(false), permitRoute(true)));
    makePolicy(
        t,
        tImportFromB,
        ifStatement(checkForCommunity(COMM), permitRoute(false), permitRoute(true)));
    makePolicy(t, tExportToA, addToCommunities(COMM));

    if (s.withB()) {
      Configuration b = configs.get(B_R);
      makePolicy(b, permitAll, permitRoute(true));
      if (s.e2At() == E2At.B) {
        makePolicy(b, e2Import, e2Body);
      }
    }

    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(COMM)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);
    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, template, List.of());
  }

  private Pair<Boolean, Boolean> run(Spec s) {
    return run(s, null);
  }

  /// If externalAsPathLength is non-null, assumes that every external neighbor (E1, and E2 wherever
  /// it attaches) sends routes with that AS-path length
  private Pair<Boolean, Boolean> run(Spec s, Integer externalAsPathLength) {
    TestConfigConstructionUtils.Networkv2 net = build(s);
    PrefixSpace prefix = new PrefixSpace(PrefixRange.fromString(PREFIX));
    NetworkInfo info = net.getInfo(prefix);
    Node target = T_R.instantiate(info);
    if (externalAsPathLength != null) {
      List<Node> attached = s.withB() ? List.of(A_R.instantiate(info), B_R.instantiate(info))
          : List.of(A_R.instantiate(info));
      for (Node n : attached) {
        for (Ip external : List.of(E1_IP, E2_IP)) {
          n.getIncomingFrom(external)
              .ifPresent(
                  e ->
                      info.addAssumption(
                          e,
                          new Invariant(
                              net.tbdd(),
                              Invariant.clauseBuilder()
                                  .setAsPathLength(externalAsPathLength)
                                  .build(net.tbdd(), net.template()))));
        }
      }
    }
    Set<Edge> ingress = Set.of();
    if (s.ingressE1Only()) {
      Node a = A_R.instantiate(info);
      ingress = Set.of(a.getIncomingFrom(E1_IP).orElseThrow());
    }
    TableAnswerElement tae = runQuery(info, prefix, target, new Invariant(net.tbdd()), ingress);
    Pair<Boolean, Boolean> res = processResultRows(tae.getRowsList());
    StringBuilder sb = new StringBuilder();
    String name =
        externalAsPathLength == null ? s.name() : s.name() + "/len" + externalAsPathLength;
    sb.append("=== CASE ").append(name).append(" ===\n");
    for (Row row : tae.getRowsList()) {
      sb.append("  [")
          .append(row.getString("Result_Label"))
          .append("] ")
          .append(row.getString("Result"))
          .append("\n");
    }
    sb.append("SUMMARY ")
        .append(name)
        .append(" goodPath=")
        .append(res.getLeft())
        .append(" interference=")
        .append(res.getRight())
        .append(" realInterference=")
        .append(s.realInterference())
        .append("\n");
    System.out.print(sb);
    return res;
  }

  /// For the known false positives: asserts only that a good path is found
  private void checkGoodPath(Spec s) {
    assertTrue("good path expected for " + s.name(), run(s).getLeft());
  }

  private void check(Spec s) {
    Pair<Boolean, Boolean> res = run(s);
    assertTrue("good path expected for " + s.name(), res.getLeft());
    if (s.realInterference() != null) {
      assertEquals(
          "interference verdict vs. real BGP for " + s.name(),
          s.realInterference(),
          res.getRight());
    }
  }

  // ---------------------------------------------------------------------------------------------
  // the specs
  // ---------------------------------------------------------------------------------------------

  /**
   * Hypothesis, 3 nodes, eBGP everywhere. No real interference: A only ever selects E1's or E2's
   * route (anything coming back from B or T carries AS 65001 and is dropped by A's loop check).
   * If A selects a route without 2:2, T accepts it from A. If A selects E2's route with 2:2, T's
   * import from A drops it, but B accepts it from A and exports it to T, whose import from B
   * permits it (B never prefers T's route, which contains AS 65002 or was dropped).
   */
  static final Spec BASE =
      new Spec("base", true, E2At.A, false, false, false, false, Sessions.EBGP, false, false);

  /** Same as BASE but the ingress set is {E1 -> A} explicitly. */
  static final Spec BASE_INGRESS_E1 =
      new Spec(
          "base-ingressE1", true, E2At.A, false, false, false, false, Sessions.EBGP, true, false);

  /** Control: E2's import also clears communities, so no route at A can carry 2:2. */
  static final Spec CONTROL_E2_CLEARS =
      new Spec(
          "control-e2Clears", true, E2At.A, true, false, false, false, Sessions.EBGP, false, false);

  /** Control: single ingress, single path, no competing route at all. */
  static final Spec CONTROL_SINGLE =
      new Spec(
          "control-single", false, E2At.NONE, false, false, false, false, Sessions.EBGP, false,
          false);

  /**
   * (a) Second path removed (nodes A, T only). Real interference: if E2 announces a route with
   * 2:2 that A prefers (e.g. shorter AS path), T's import from A drops it and T has no route.
   */
  static final Spec A_NO_SECOND_PATH =
      new Spec("a-noSecondPath", false, E2At.A, false, false, false, false, Sessions.EBGP, false,
          true);

  /**
   * (a') Second path present but T's import from B also drops 2:2. Real interference, for the
   * same reason as (a).
   */
  static final Spec A2_SECOND_PATH_ALSO_FILTERS =
      new Spec(
          "a2-secondPathAlsoFilters", true, E2At.A, false, false, false, true, Sessions.EBGP, false,
          true);

  /**
   * (b) One path (A, T), E1's import sets local-pref 200 and E2's sets 50. No real interference:
   * E1 always announces (good ingress), so A always selects E1's route, which has no 2:2.
   */
  static final Spec B_LOWER_LOCAL_PREF =
      new Spec("b-e2LowerLocalPref", false, E2At.A, false, true, false, false, Sessions.EBGP,
          false, false);

  /**
   * (c) The competing route enters at B (E2 -> B) instead of at A; B exports it to A and to T.
   * No real interference: if A selects B's route (which may carry 2:2), B's own best is E2's route
   * (A's copy comes back with AS 65002 in its path and is dropped), which B exports to T.
   */
  static final Spec C_E2_AT_B =
      new Spec("c-e2AtB", true, E2At.B, false, false, false, false, Sessions.EBGP, false, false);

  /** (c) with ingress {E1 -> A}, so the good path is forced to be E1 -> A -> T. */
  static final Spec C_E2_AT_B_INGRESS_E1 =
      new Spec(
          "c-e2AtB-ingressE1", true, E2At.B, false, false, false, false, Sessions.EBGP, true,
          false);

  /**
   * (e) No second ingress and no second path: nodes A, T, single external neighbor E1, but T's
   * export back to A tags 2:2. No real interference: T's route back to A has A's AS in its path,
   * so A drops it (with iBGP, T would not send an iBGP-learned route back to its iBGP peer A).
   * The tool has no loop prevention, so it must assume A can select T's tagged route.
   */
  static final Spec E_LOOP_BACK_TAG =
      new Spec(
          "e-loopBackTag", false, E2At.NONE, false, false, true, false, Sessions.EBGP, false, false);

  /**
   * Smallest form of the two-path hypothesis: nodes A and T only, joined by two sessions. Session
   * 10.0.0.1 <-> 10.0.0.3 has T's 2:2 filter; the parallel session 10.0.1.1 <-> 10.0.1.3 permits
   * everything. No real interference: A advertises its best route on both sessions, so even when it
   * carries 2:2, T accepts it on the parallel session. (Whether NEW flags it depends on which of
   * the two equally short A -> T edges PathExploration puts on the good path.)
   */
  static final Spec PARALLEL_SESSION =
      new Spec(
          "parallelSession",
          false,
          E2At.A,
          false,
          false,
          false,
          false,
          Sessions.EBGP,
          false,
          false,
          1);

  /** PARALLEL_SESSION with the 2:2 filter moved to the 10.0.1.x session. */
  static final Spec PARALLEL_SESSION_SWAPPED =
      new Spec(
          "parallelSessionSwapped",
          false,
          E2At.A,
          false,
          false,
          false,
          false,
          Sessions.EBGP,
          false,
          false,
          2);

  /** PARALLEL_SESSION with ingress {E1 -> A}. */
  static final Spec PARALLEL_SESSION_INGRESS_E1 =
      new Spec(
          "parallelSession-ingressE1",
          false,
          E2At.A,
          false,
          false,
          false,
          false,
          Sessions.EBGP,
          true,
          false,
          1);

  /** PARALLEL_SESSION_SWAPPED with ingress {E1 -> A}. */
  static final Spec PARALLEL_SESSION_SWAPPED_INGRESS_E1 =
      new Spec(
          "parallelSessionSwapped-ingressE1",
          false,
          E2At.A,
          false,
          false,
          false,
          false,
          Sessions.EBGP,
          true,
          false,
          2);

  @Test
  public void parallelSession() {
    check(PARALLEL_SESSION);
  }

  @Test
  public void parallelSessionSwapped() {
    // TODO the interference check reports a false positive here (see INTERFERENCE_FALSE_POSITIVES.md)
    // check(PARALLEL_SESSION_SWAPPED);
    checkGoodPath(PARALLEL_SESSION_SWAPPED);
  }

  @Test
  public void parallelSessionIngressE1() {
    check(PARALLEL_SESSION_INGRESS_E1);
  }

  @Test
  public void parallelSessionSwappedIngressE1() {
    // TODO the interference check reports a false positive here (see INTERFERENCE_FALSE_POSITIVES.md)
    // check(PARALLEL_SESSION_SWAPPED_INGRESS_E1);
    checkGoodPath(PARALLEL_SESSION_SWAPPED_INGRESS_E1);
  }

  @Test
  public void base() {
    // TODO the interference check reports a false positive here (see INTERFERENCE_FALSE_POSITIVES.md)
    // check(BASE);
    checkGoodPath(BASE);
  }

  @Test
  public void baseIngressE1() {
    // TODO the interference check reports a false positive here (see INTERFERENCE_FALSE_POSITIVES.md)
    // check(BASE_INGRESS_E1);
    checkGoodPath(BASE_INGRESS_E1);
  }

  @Test
  public void controlE2Clears() {
    check(CONTROL_E2_CLEARS);
  }

  @Test
  public void controlSingle() {
    check(CONTROL_SINGLE);
  }

  @Test
  public void aNoSecondPath() {
    check(A_NO_SECOND_PATH);
  }

  @Test
  public void a2SecondPathAlsoFilters() {
    check(A2_SECOND_PATH_ALSO_FILTERS);
  }

  @Test
  public void bLowerLocalPref() {
    check(B_LOWER_LOCAL_PREF);
  }

  @Test
  public void cE2AtB() {
    check(C_E2_AT_B);
  }

  @Test
  public void cE2AtBIngressE1() {
    // TODO the interference check reports a false positive here (see INTERFERENCE_FALSE_POSITIVES.md)
    // check(C_E2_AT_B_INGRESS_E1);
    checkGoodPath(C_E2_AT_B_INGRESS_E1);
  }

  @Test
  public void cE2AtBIngressE1PinnedAsPathLength() {
    // with the external AS-path lengths pinned, E2's route reaches A through B one EBGP hop later
    // than E1's, so it is less preferred at A and route preference excuses it
    Pair<Boolean, Boolean> res = run(C_E2_AT_B_INGRESS_E1, 0);
    assertTrue(res.getLeft());
    assertFalse(res.getRight());
  }

  @Test
  public void eLoopBackTagPinnedAsPathLength() {
    // with E1's AS-path length pinned, the copy of the good route that comes back from T has gone
    // through two more EBGP hops, so it is less preferred at A and route preference excuses it
    Pair<Boolean, Boolean> res = run(E_LOOP_BACK_TAG, 0);
    assertTrue(res.getLeft());
    assertFalse(res.getRight());
  }

  @Test
  public void eLoopBackTag() {
    // TODO the interference check reports a false positive here (see INTERFERENCE_FALSE_POSITIVES.md)
    // check(E_LOOP_BACK_TAG);
    checkGoodPath(E_LOOP_BACK_TAG);
  }

  /**
   * (d) Does the session type matter to the tool? Runs every spec with NO_AS and IBGP_CORE and
   * prints the verdicts (no assertion on interference, only on the good path).
   */
  @Test
  public void dSessionTypeMatrix() {
    Map<String, Pair<Boolean, Boolean>> results = new LinkedHashMap<>();
    for (Spec s :
        List.of(
            BASE,
            CONTROL_E2_CLEARS,
            CONTROL_SINGLE,
            A_NO_SECOND_PATH,
            A2_SECOND_PATH_ALSO_FILTERS,
            B_LOWER_LOCAL_PREF,
            C_E2_AT_B,
            C_E2_AT_B_INGRESS_E1,
            E_LOOP_BACK_TAG,
            PARALLEL_SESSION,
            PARALLEL_SESSION_SWAPPED)) {
      for (Sessions sess : List.of(Sessions.NO_AS, Sessions.IBGP_CORE)) {
        Spec v = s.with(sess);
        Pair<Boolean, Boolean> r = run(v);
        results.put(v.name(), r);
        assertTrue("good path expected for " + v.name(), r.getLeft());
      }
    }
    results.forEach(
        (k, v) ->
            System.out.println(
                "MATRIX " + k + " goodPath=" + v.getLeft() + " interference=" + v.getRight()));
  }
}
