package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Setup;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_safety;
import static org.batfish.minesweeper.question.verificationutilities.Setup.nonDefaultRoute;

public record SafetyResult(
    NetworkInfo info,
    boolean refinementOccurred,
    Map<Location, Bgpv4Route> checks,
    Map<Location, Invariant> targets,
    Refine.Result refinement,
    Optional<Infer.CounterExample> inferenceCounter) {

  private void addGroupsToTAE(
      TableAnswerElement tae,
      boolean isAssumptions,
      Map<String, Map<String, Map<String, Set<String>>>> groupings) {
    groupings.keySet().stream()
        .sorted()
        .forEach(
            assumption -> {
              groupings
                  .get(assumption)
                  .forEach(
                      (inferred, m2) -> {
                        m2.forEach(
                            (cex, locations) -> {
                              tae.addRow(
                                  Row.builder()
                                      .put(
                                          Setup.LOCATION_RELEVANCE_COL,
                                          isAssumptions ? "Assumption" : "Internal Location")
                                      .put(Setup.PROVIDED_INVARIANT_COL, assumption)
                                      .put(Setup.LOCATIONS_COL, String.join(", ", locations))
                                      .put(Setup.INFERRED_INVARIANTS_COL, inferred)
                                      .put(Setup.COUNTEREXAMPLE_COL, cex)
                                      .build());
                            });
                      });
            });
  }

  private void addTargetToTAE(
      TableAnswerElement tae,
      String location,
      Invariant provided,
      Invariant inferred,
      Map<BDD, String> cache) {
    tae.addRow(
        Row.builder()
            .put(Setup.LOCATION_RELEVANCE_COL, "Target")
            .put(Setup.PROVIDED_INVARIANT_COL, provided.toString(refinementOccurred, cache))
            .put(Setup.LOCATIONS_COL, location)
            .put(Setup.INFERRED_INVARIANTS_COL, inferred.toString(refinementOccurred, cache))
            .put(Setup.COUNTEREXAMPLE_COL, "")
            .build());
  }

  private void addViolationNote(TableAnswerElement tae, String violation) {
    if (!violation.isEmpty()) {
      tae.addRow(
          Row.builder()
              .put(Setup.LOCATION_RELEVANCE_COL, "Violation Note")
              .put(Setup.PROVIDED_INVARIANT_COL, "")
              .put(Setup.LOCATIONS_COL, violation)
              .put(Setup.INFERRED_INVARIANTS_COL, "")
              .put(Setup.COUNTEREXAMPLE_COL, "...")
              .build());
    }
  }

  /// Gather the answer element needed for a question return
  public TableAnswerElement getAnswerElementAll(String violations) {
    Map<Location, Invariant> results = refinement.refined;
    Map<BDD, String> cache = new HashMap<>();
    TableAnswerElement tae = new TableAnswerElement(metadata_safety());

    // added to try to isolate exact violations with verification failure
    addViolationNote(tae, violations);

    // assumption -> inferred invariant -> counterexample -> set of locations
    Map<String, Map<String, Map<String, Set<String>>>> assumptionGroups = new HashMap<>();
    Map<String, Map<String, Map<String, Set<String>>>> intermediateGroups = new HashMap<>();
    Map<BDD, String> stringLimits = new HashMap<>();

    // add targets and assumptions to cache so they can be used if useful
    targets.values().forEach(inv -> cache.put(inv.getBDDCopy(), inv.toString(refinementOccurred)));
    info.getCheckedAssumptions()
        .values()
        .forEach(inv -> cache.put(inv.getBDDCopy(), inv.toString(refinementOccurred)));
    info.getEnforcedAssumptions()
        .values()
        .forEach(inv -> cache.put(inv.getBDDCopy(), inv.toString(refinementOccurred)));

    // group the results and add the target first
    AtomicBoolean targetAdded = new AtomicBoolean(false);
    results
        .keySet()
        .forEach(
            loc -> {
              if (targets.containsKey(loc)) {
                if (!targetAdded.get()) { // we support one target or all going edges
                  String locationStr = targets.size() == 1 ? info.locationStr(loc) : "ALL-OUTGOING";
                  addTargetToTAE(tae, locationStr, targets.get(loc), results.get(loc), cache);
                  targetAdded.set(true);
                }
              } else {
                String assumption_str =
                    info.getCheckedAssumptions().containsKey(loc)
                        ? info.getCheckedAssumptions().get(loc).toString(refinementOccurred, cache)
                        : info.getEnforcedAssumptions().containsKey(loc)
                            ? info.getEnforcedAssumptions()
                                .get(loc)
                                .toString(refinementOccurred, cache)
                            : "";

                String inferred_str = results.get(loc).toString(true, cache);
                if (inferred_str.equals("LIMIT (Complex BDD)") || inferred_str.isEmpty()) {
                  // String update = info.getRouteExampleStr(results.get(loc));
                  inferred_str =
                      stringLimits.computeIfAbsent(
                          results.get(loc).getBDD(),
                          //  k -> update.isEmpty() ? "LIMIT (Complex BDD) [" + (stringLimits.size()
                          // + 1) + "]" : update);
                          k -> "LIMIT (Complex BDD) [" + (stringLimits.size() + 1) + "]");
                }
                String counterexample_str =
                    checks.containsKey(loc)
                        ? nonDefaultRoute(checks.get(loc))
                        : (refinement.refined.get(loc).isFalse() && !refinementOccurred
                            ? "any route is counterexample"
                            : "");

                // add the specific result to the map
                if (assumption_str.isEmpty()) {
                  intermediateGroups
                      .computeIfAbsent("", k -> new HashMap<>())
                      .computeIfAbsent(inferred_str, k -> new HashMap<>())
                      .computeIfAbsent(counterexample_str, k -> new HashSet<>())
                      .add(info.locationStr(loc));
                } else if (!info.isIncomingEdge(loc)) {
                  intermediateGroups
                      .computeIfAbsent(assumption_str, k -> new HashMap<>())
                      .computeIfAbsent(inferred_str, k -> new HashMap<>())
                      .computeIfAbsent(counterexample_str, k -> new HashSet<>())
                      .add(info.locationStr(loc));
                } else {
                  assumptionGroups
                      .computeIfAbsent(assumption_str, k -> new HashMap<>())
                      .computeIfAbsent(inferred_str, k -> new HashMap<>())
                      .computeIfAbsent(counterexample_str, k -> new HashSet<>())
                      .add(info.locationStr(loc));
                }
              }
            });

    // next add the groups of assumptions
    addGroupsToTAE(tae, true, assumptionGroups);

    // last add the intermediate nodes
    addGroupsToTAE(tae, false, intermediateGroups);

    return tae;
  }

  /// Gather the answer element needed for a question return, only include information associated
  /// with assumptions and targets, only include intermediate invariants if false inferred
  public TableAnswerElement getAnswerElementLimited(String violations) {
    Map<BDD, String> cache = new HashMap<>();
    TableAnswerElement tae = new TableAnswerElement(metadata_safety());

    // added to try to isolate exact violations with verification failure
    addViolationNote(tae, violations);

    // at the target to the top, refinement included if it occurred
    assert !targets.isEmpty() : "We need to have some assumption";
    Map.Entry<Location, Invariant> target = targets.entrySet().stream().findFirst().get();
    if (targets.size() == 1) {
      addTargetToTAE(
          tae,
          info.locationStr(target.getKey()),
          target.getValue(),
          refinement.refined.get(target.getKey()),
          cache);
    } else {
      // right now this means we provided all outgoing as target
      addTargetToTAE(
          tae, "ALL-OUTGOING", target.getValue(), refinement.refined.get(target.getKey()), cache);
    }

    // if there is an inference counterexamples, return those
    if (inferenceCounter.isPresent()) {
      Infer.CounterExample cex = inferenceCounter.get();
      tae.addRow(
          Row.builder()
              .put(Setup.LOCATION_RELEVANCE_COL, "Intermediate")
              .put(Setup.PROVIDED_INVARIANT_COL, "")
              .put(Setup.LOCATIONS_COL, info.locationStr(cex.location()))
              .put(Setup.INFERRED_INVARIANTS_COL, cex.post().toString(false, cache))
              .put(Setup.COUNTEREXAMPLE_COL, "any route is counterexample")
              .build());
    } else {
      // otherwise, report whether the assumptions were satisfied
      // assumption -> inferred invariant -> counterexample -> set of locations
      Map<String, Map<String, Map<String, Set<String>>>> groupings = new HashMap<>();
      info.getCheckedAssumptions()
          .forEach(
              (loc, assumption) -> {
                String assumption_str = assumption.toString(refinementOccurred, cache);
                assert refinement.refined.containsKey(loc);
                String inferred_str = refinement.refined.get(loc).toString(true, cache);
                String counterexample_str =
                    checks.containsKey(loc)
                        ? nonDefaultRoute(checks.get(loc))
                        : (refinement.refined.get(loc).isFalse()
                            ? "any route is counterexample"
                            : "");

                // add the specific result to the map
                groupings
                    .computeIfAbsent(assumption_str, k -> new HashMap<>())
                    .computeIfAbsent(inferred_str, k -> new HashMap<>())
                    .computeIfAbsent(counterexample_str, k -> new HashSet<>())
                    .add(info.locationStr(loc));
              });
      // add groupings to the table answer element
      addGroupsToTAE(tae, true, groupings);
    }
    return tae;
  }
}
