package org.batfish.minesweeper.question.reachability;

import net.sf.javabdd.BDD;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.minesweeper.question.isolation.Infer;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
import org.junit.Test;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

/**
 * Diagnostics: replays the interference part of ReachabilityAnswerer.run on
 * the networks of InterferenceFalsePositiveTest and prints the good path's per-location
 * constraints (the Infer targets) and every invariant Infer computes, so the mechanism behind each
 * report is visible.
 */
public class InterferenceDiagnosticsTest {

  private void diag(InterferenceFalsePositiveTest.Spec s) {
    diag(s, false);
  }

  private void diag(InterferenceFalsePositiveTest.Spec s, boolean printConstraintsFirst) {
    InterferenceFalsePositiveTest t = new InterferenceFalsePositiveTest();
    TestConfigConstructionUtils.Networkv2 net = t.build(s);
    PrefixSpace prefix = new PrefixSpace(PrefixRange.fromString("2.4.8.0/24"));
    NetworkInfo info = net.getInfo(prefix);
    Node target = new NodeRecord("10.0.0.3", "tNode").instantiate(info);
    Set<Edge> ingress = Set.of();
    if (s.ingressE1Only()) {
      Node a = new NodeRecord("10.0.0.1", "aNode").instantiate(info);
      ingress = Set.of(a.getIncomingFrom(org.batfish.datamodel.Ip.parse("100.0.0.10")).orElseThrow());
    }
    PathExploration exploration =
        info.toPathExploration(prefix, target, new Invariant(net.tbdd()), ingress, new HashMap<>());
    Pair<Path, Set<Path>> paths = exploration.run();
    StringBuilder sb = new StringBuilder();
    sb.append("=== DIAG ").append(s.name()).append(" ===\n");
    Path good = paths.getKey();
    if (good == null) {
      sb.append("  no good path\n");
      System.out.print(sb);
      return;
    }
    sb.append("  good path: ").append(good.display(info)).append("\n");
    if (printConstraintsFirst) {
      int len = 0;
      for (Invariant i : good.getConstraints().values()) {
        len += i.toString().length();
      }
      sb.append("  (printed path constraints before inference, ").append(len).append(" chars)\n");
    }
    Infer inference = info.toInfer();
    inference.addPrefixToAssumptions(prefix);
    for (Map.Entry<Location, Invariant> e : good.getConstraints().entrySet()) {
      if (e.getKey() instanceof Node) {
        BDD bdd = e.getValue().getBDDCopy();
        inference.addProperty(
            e.getKey(),
            new Invariant(
                info.tbdd,
                bdd.existEq(info.tbdd.getOriginalRoute().getProtocolHistory().support())));
      }
    }
    Infer.Result r = inference.run(true);
    // NOTE: Invariant.toString() (BDDString) mutates tbdd.getCommunityAtomicPredicates() (it drops
    // every AP that some other regex uses from the "[^^$]*" all-communities entry), which changes
    // how later policies that clear/match all communities are analyzed. So invariants are only
    // printed after inference, unless printConstraintsFirst is set to demonstrate that effect.
    if (printConstraintsFirst) {
      sb.append("  (path constraints were printed BEFORE inference: see note)\n");
    }
    Map<String, String> constraints = new TreeMap<>();
    good.getConstraints()
        .forEach((loc, inv) -> constraints.put(loc.toUniqueString(), inv.toString()));
    constraints.forEach(
        (k, v) -> sb.append("  path constraint  ").append(k).append(" : ").append(v).append("\n"));
    Map<String, String> inv = new TreeMap<>();
    r.invariants.forEach((loc, i) -> inv.put(loc.toUniqueString(), i.toString()));
    inv.forEach((k, v) -> sb.append("  inferred  ").append(k).append(" : ").append(v).append("\n"));
    r.checks.forEach(
        (loc, route) ->
            sb.append("  FAILED CHECK at ")
                .append(loc.toUniqueString())
                .append(" : ")
                .append(route)
                .append("\n"));
    sb.append("  counter=").append(r.counter).append("\n");
    System.out.print(sb);
  }

  private void viaAnswerer(InterferenceFalsePositiveTest.Spec s) {
    InterferenceFalsePositiveTest t = new InterferenceFalsePositiveTest();
    TestConfigConstructionUtils.Networkv2 net = t.build(s);
    PrefixSpace prefix = new PrefixSpace(PrefixRange.fromString("2.4.8.0/24"));
    NetworkInfo info = net.getInfo(prefix);
    Node target = new NodeRecord("10.0.0.3", "tNode").instantiate(info);
    org.batfish.datamodel.table.TableAnswerElement tae =
        ReachabilityAnswerer.run(info, prefix, target, new Invariant(net.tbdd()), Set.of());
    StringBuilder sb = new StringBuilder("=== ANSWERER " + s.name() + " ===\n");
    tae.getRowsList()
        .forEach(
            r ->
                sb.append("  [")
                    .append(r.getString("Result_Label"))
                    .append("] ")
                    .append(r.getString("Result"))
                    .append("\n"));
    System.out.print(sb);
  }

  @Test
  public void orderCheck() {
    System.out.println("##### orderCheck");
    viaAnswerer(InterferenceFalsePositiveTest.CONTROL_SINGLE);
    diag(InterferenceFalsePositiveTest.CONTROL_SINGLE, false);
    diag(InterferenceFalsePositiveTest.CONTROL_SINGLE, true);
    viaAnswerer(InterferenceFalsePositiveTest.CONTROL_SINGLE);
    viaAnswerer(InterferenceFalsePositiveTest.BASE);
    diag(InterferenceFalsePositiveTest.BASE, false);
  }

  @Test
  public void diagnostics() {
    System.out.println("##### diagnostics");
    diag(InterferenceFalsePositiveTest.BASE);
    diag(InterferenceFalsePositiveTest.A_NO_SECOND_PATH);
    diag(InterferenceFalsePositiveTest.B_LOWER_LOCAL_PREF);
    diag(InterferenceFalsePositiveTest.C_E2_AT_B);
    diag(InterferenceFalsePositiveTest.C_E2_AT_B_INGRESS_E1);
    diag(InterferenceFalsePositiveTest.E_LOOP_BACK_TAG);
    diag(InterferenceFalsePositiveTest.CONTROL_SINGLE);
  }
}
