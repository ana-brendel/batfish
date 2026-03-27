package org.batfish.minesweeper.question.safety;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

// Currently the question takes in a single target location-invariant pair whereas the assumptions
// might be a list
public final class SafetyAnswerer extends Answerer {
  private static final Logger LOGGER = LogManager.getLogger(SafetyAnswerer.class);

  private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets = new HashMap<>();
  private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions = new HashMap<>();
  private final @Nullable Invariant.Builder _default_assumption;
  private final @Nonnull Set<RegexConstraint> _communityRegexes = new HashSet<>();
  private final @Nonnull Set<RegexConstraint> _asPathRegexes = new HashSet<>();
  private final boolean _showAll;
  private final boolean _refine;

  public SafetyAnswerer(SafetyQuestion question, IBatfish batfish) {
    super(question, batfish);
    _showAll = question.get_show_all();
    _refine = question.get_refine();
    _default_assumption = question.get_default_assumption().orElse(null);

    // we take target property and corresponding locations as two lists with corresponding inputs
    List<Invariant.Builder> targetProperties =
        question.get_target().isPresent() ? question.get_target().get().get_builders() : List.of();
    List<Location.Builder> targetLocations =
        question.get_location().isPresent()
            ? question.get_location().get().get_builders()
            : List.of();

    assert targetProperties.size() == targetLocations.size()
        : "Arguments checked in question, if this fails there is bug in code.";

    for (int i = 0; i < targetProperties.size(); i++) {
      _targets.put(targetLocations.get(i), targetProperties.get(i));
    }

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

    for (int i = 0; i < invAssumptions.size(); i++) {
      _assumptions.put(locAssumptions.get(i), invAssumptions.get(i));
    }

    if (_default_assumption != null) {
      _default_assumption
          .getClauses()
          .forEach(
              c -> {
                _communityRegexes.addAll(c.getCommunities().getRegexConstraints());
                _asPathRegexes.addAll(c.getAsPath().getRegexConstraints());
              });
    }

    invAssumptions.forEach(
        clauses ->
            clauses
                .getClauses()
                .forEach(
                    c -> {
                      _communityRegexes.addAll(c.getCommunities().getRegexConstraints());
                      _asPathRegexes.addAll(c.getAsPath().getRegexConstraints());
                    }));
    _targets
        .values()
        .forEach(
            clauses ->
                clauses
                    .getClauses()
                    .forEach(
                        c -> {
                          _communityRegexes.addAll(c.getCommunities().getRegexConstraints());
                          _asPathRegexes.addAll(c.getAsPath().getRegexConstraints());
                        }));
  }

  /// Driving function to run complete invariant inference and refinement (if applicable)
  public static SafetyResult run(
      NetworkInfo info, boolean refine, Map<Location, Invariant.Builder> targets) {
    // Set up and run the invariant inference
    Infer inference = info.toInfer();
    targets.forEach(
        (loc, builder) -> inference.addProperty(loc, info.buildInvariant(loc, builder, true)));

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

    return new SafetyResult(
        info, refinementOccurred, result.checks, inference.getTargets(), refined, result.counter);
  }

  @Override
  public AnswerElement answer(NetworkSnapshot snapshot) {
    LOGGER.info("Within the answerer for verification.");

    // Gather information from the network
    SpecifierContext context = _batfish.specifierContext(snapshot);
    LOGGER.info("Created BATFISH context");
    Map<String, Configuration> configs = context.getConfigs();

    LOGGER.info("Gathering relevant information from configs...");
    NetworkInfo info =
        _default_assumption == null
            ? new NetworkInfo(configs, _communityRegexes, _asPathRegexes)
            : new NetworkInfo(configs, _communityRegexes, _asPathRegexes, _default_assumption);
    LOGGER.info("Constructed Verification.NetworkInfo object");

    LOGGER.info("Adding any provided assumptions to the NetworkInfo object");
    Set<Location> instantiatedAssumptions = new HashSet<>();
    for (Map.Entry<Location.Builder, Invariant.Builder> entry : _assumptions.entrySet()) {
      instantiatedAssumptions.addAll(info.addAssumption(entry.getKey(), entry.getValue()));
    }

    // if there is no provided target, return a list of the network locations
    if (_targets.isEmpty()) {
      return info.getAnswerElement();
    }

    assert _targets.size() == 1 : "Current API limits to a single property to verify";

    // implemented as set to allow for multiple targets in the future, right now used in cases where
    // we want to verify a property on all edges leaving the network
    Map<Location, Invariant.Builder> targetBuilders = new HashMap<>();
    _targets.forEach(
        (location, invariant) ->
            location
                .instantiate(info)
                .forEach(
                    loc -> {
                      // we prioritize assumptions provided
                      if (!instantiatedAssumptions.contains(loc)) {
                        targetBuilders.put(loc, invariant);
                      } else {
                        LOGGER.info(
                            "Attempted to verify property at a location ({}) with an assumption present.",
                            info.locationStr(loc));
                      }
                    }));
    SafetyResult result = run(info, _refine, targetBuilders);

    // potential special case to more efficiently isolate violations (if multiple targets), unused
    // Optional<String> violations = ViolationAnalysis.run(info, result)

    LOGGER.info("Completed analysis. Working on displaying results...");

    // return the answer element associated with desired level of granularity
    return _showAll ? result.getAnswerElementAll("") : result.getAnswerElementLimited("");
  }
}
