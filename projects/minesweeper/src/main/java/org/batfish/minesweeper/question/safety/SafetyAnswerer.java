package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Setup;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.batfish.minesweeper.question.verificationutilities.Setup.buildInvariant;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_safety;
import static org.batfish.minesweeper.question.verificationutilities.Setup.nonDefaultRoute;

// Currently the question takes in a single target location-invariant pair whereas the assumptions
// might be a list
public final class SafetyAnswerer extends Answerer {
  private static final Logger LOGGER = LogManager.getLogger(SafetyAnswerer.class);

  private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets;
  private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions;
  private final @Nonnull Optional<Invariant.Builder> _default_assumption;
  private final @Nonnull Set<RegexConstraint> _communityRegexes;
  private final @Nonnull Set<RegexConstraint> _asPathRegexes;
  private final boolean _showAll;
  private final boolean _refine;

  public SafetyAnswerer(SafetyQuestion question, IBatfish batfish) {
    super(question, batfish);
    _showAll = question.get_show_all();
    _targets = question.get_targets();
    _refine = question.get_refine();
    _default_assumption = question.get_default_assumption();

    // this is added because the assumptions are taken as two lists with corresponding inputs
    List<Invariant.Builder> invAssumptions =
        question.get_assumptions().isPresent()
            ? question.get_assumptions().get().get_builders()
            : List.of();
    List<Location.Builder> locAssumptions =
        question.get_assumption_locations().isPresent()
            ? question.get_assumption_locations().get().get_builders()
            : List.of();

    assert invAssumptions.size() == locAssumptions.size()
        : "Arguments checked in question, if this fails there is bug in code.";

    _assumptions = new HashMap<>();
    for (int i = 0; i < invAssumptions.size(); i++) {
      _assumptions.put(locAssumptions.get(i), invAssumptions.get(i));
    }

    _communityRegexes = new HashSet<>();
    _asPathRegexes = new HashSet<>(); // not included in the NetworkClause nor Invariant class yet

    invAssumptions.forEach(
        clauses ->
            clauses
                .getClauses()
                .forEach(c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints())));
    _targets
        .values()
        .forEach(
            clauses ->
                clauses
                    .getClauses()
                    .forEach(
                        c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints())));
  }

  public record Result(
      NetworkInfo info,
      boolean refinementOccurred,
      Map<Location, Optional<Bgpv4Route>> checks,
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
                                            isAssumptions ? "Assumption" : "Intermediate")
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
        Location location,
        Invariant provided,
        Invariant inferred,
        Map<BDD, String> cache) {
      tae.addRow(
          Row.builder()
              .put(Setup.LOCATION_RELEVANCE_COL, "Target")
              .put(Setup.PROVIDED_INVARIANT_COL, provided.toString(refinementOccurred, cache))
              .put(Setup.LOCATIONS_COL, info.locationStr(location))
              .put(Setup.INFERRED_INVARIANTS_COL, inferred.toString(refinementOccurred, cache))
              .put(Setup.COUNTEREXAMPLE_COL, "")
              .build());
    }

    /// Gather the answer element needed for a question return
    public TableAnswerElement getAnswerElementAll() {
      Map<Location, Invariant> results = refinement.refined;
      Map<BDD, String> cache = new HashMap<>();
      TableAnswerElement tae = new TableAnswerElement(metadata_safety());
      // assumption -> inferred invariant -> counterexample -> set of locations
      Map<String, Map<String, Map<String, Set<String>>>> assumptionGroups = new HashMap<>();
      Map<String, Map<String, Set<String>>> intermediateGroups = new HashMap<>();
      Map<BDD, String> stringLimits = new HashMap<>();

      // group the results and add the target first
      results
          .keySet()
          .forEach(
              loc -> {
                if (targets.containsKey(loc)) {
                  addTargetToTAE(tae, loc, targets.get(loc), results.get(loc), cache);
                } else {
                  String assumption_str =
                      info.getAssumptions().containsKey(loc)
                          ? info.getAssumptions().get(loc).toString(refinementOccurred, cache)
                          : "";

                  String inferred_str = results.get(loc).toString(true, cache);
                  if (inferred_str.equals("LIMIT (Complex BDD)")) {
                    inferred_str =
                        stringLimits.computeIfAbsent(
                            results.get(loc).peakAtBDD(),
                            k -> "LIMIT (Complex BDD) [" + (stringLimits.size() + 1) + "]");
                  }
                  String counterexample_str =
                      checks.containsKey(loc) && checks.get(loc).isPresent()
                          ? nonDefaultRoute(checks.get(loc).get())
                          : (refinement.refined.get(loc).isFalse() && !refinementOccurred
                              ? "any route is counterexample"
                              : "");

                  // add the specific result to the map
                  if (assumption_str.isEmpty()) {
                    intermediateGroups
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
      addGroupsToTAE(tae, false, Map.of("", intermediateGroups));

      return tae;
    }

    /// Gather the answer element needed for a question return, only include information associated
    /// with assumptions and targets, only include intermediate invariants if false inferred
    public TableAnswerElement getAnswerElementLimited() {
      Map<BDD, String> cache = new HashMap<>();
      TableAnswerElement tae = new TableAnswerElement(metadata_safety());
      // at the target to the top, refinement included if it occurred
      assert targets.size() == 1 : "Currently we only support one target property.";
      Map.Entry<Location, Invariant> target = targets.entrySet().stream().findFirst().get();
      addTargetToTAE(
          tae, target.getKey(), target.getValue(), refinement.refined.get(target.getKey()), cache);

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
        info.getAssumptions()
            .forEach(
                (loc, assumption) -> {
                  String assumption_str = assumption.toString(refinementOccurred, cache);
                  assert refinement.refined.containsKey(loc);
                  String inferred_str = refinement.refined.get(loc).toString(true, cache);
                  String counterexample_str =
                      checks.containsKey(loc) && checks.get(loc).isPresent()
                          ? nonDefaultRoute(checks.get(loc).get())
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

  /// Driving function to run complete invariant inference and refinement (if applicable)
  public static Result run(NetworkInfo info, boolean refine, Location location, Invariant target) {
    // Set up and run the invariant inference
    Infer inference = info.toInfer();
    inference.addProperty(location, target);

    LOGGER.info("Beginning inference...");
    Infer.Result result = inference.run();
    LOGGER.info("Finished inferring weakest conditions needed for property to hold.");

    // Run the refinement of invariants, if the initial inference supports the safety condition
    Refine.Result refined;
    boolean refinementOccurred = true;

    if (result.counter.isPresent() || !refine || !result.verified) {
      // should only refine if verification succeeds and flag is set to refine
      LOGGER.info("No invariant refinement.");
      refinementOccurred = false;
      refined = inference.refiner().noRefinement();
    } else {
      LOGGER.info("Beginning invariant refinement...");
      refined = inference.refiner().refine();
      LOGGER.info("Finished refining invariants.");
    }

    assert result.verified == refined.verified : "Refine should NOT change verification outcome.";

    return new Result(
        info, refinementOccurred, result.checks, Map.of(location, target), refined, result.counter);
  }

  @Override
  public AnswerElement answer(NetworkSnapshot snapshot) {
    LOGGER.info("Within the answerer for verification.");

    // Gather information from the network
    SpecifierContext context = _batfish.specifierContext(snapshot);
    Map<String, Configuration> configs = context.getConfigs();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(_communityRegexes, _asPathRegexes, configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);
    NetworkInfo info =
        _default_assumption
            .map(builder -> new NetworkInfo(tbdd, configs, builder.build(tbdd, null)))
            .orElseGet(() -> new NetworkInfo(tbdd, configs));
    _assumptions.forEach(info::addAssumption);
    LOGGER.info(info.displayNodes());

    // if there is no provided target, return a list of the network locations
    if (_targets.isEmpty()) {
      return info.getAnswerElement();
    }

    assert _targets.size() == 1 : "Current API limits to a single property to verify";

    // determine the target and run the inference algorithm
    Map.Entry<Location, Invariant> target =
        buildInvariant(info, true, _targets.entrySet().stream().findFirst().get());
    Result result = run(info, _refine, target.getKey(), target.getValue());
    LOGGER.info("Completed analysis. Working on displaying results...");

    // return the answer element associated with desired level of granularity
    return _showAll ? result.getAnswerElementAll() : result.getAnswerElementLimited();
  }
}
