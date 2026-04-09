package org.batfish.minesweeper.question.liveness;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.batfish.minesweeper.question.verificationutilities.Setup.buildLocationInvariant;

public class LivenessAnswerer extends Answerer {
  private static final Logger LOGGER = LogManager.getLogger(LivenessAnswerer.class);

  private final @Nonnull PrefixSpace _prefix;
  private final @Nullable Pair<Location.Builder, Invariant.Builder> _target;
  private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions = new HashMap<>();
  private final @Nonnull Set<RegexConstraint> _communityRegexes = new HashSet<>();
  private final @Nonnull Set<RegexConstraint> _asPathRegexes = new HashSet<>();
  private final @Nullable Invariant.Builder _default_assumption;
  private final @Nullable Location.Builders _ingress;

  public LivenessAnswerer(LivenessQuestion question, IBatfish batfish) {
    super(question, batfish);
    _prefix = question.get_prefix();
    _target = question.get_target();
    _default_assumption = question.get_default_assumption();
    _ingress = question.get_ingress();

    // this is added because the assumptions are taken as two lists with corresponding inputs
    List<Invariant.Builder> invAssumptions =
        question.get_assumptions().isPresent()
            ? question.get_assumptions().get().get_builders()
            : List.of();
    List<Location.Builder> locAssumptions =
        question.get_assumption_locations().isPresent()
            ? question.get_assumption_locations().get().get_builders()
            : List.of();

    assert invAssumptions.size() == locAssumptions.size();
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

    if (_target != null) {
      _target
          .getRight()
          .getClauses()
          .forEach(
              c -> {
                _communityRegexes.addAll(c.getCommunities().getRegexConstraints());
                _asPathRegexes.addAll(c.getAsPath().getRegexConstraints());
              });
    }
  }

  /**
   * Completes liveness verification of the target property for the provided prefix at the given
   * location, based on the network described by the info object provided.
   *
   * @param info network information
   * @param prefix prefix considered for liveness property
   * @param location location liveness property should hold
   * @param target target liveness property to verify
   * @param ingress option to specify the origin of traffic
   * @return LivenessAnswerer.Result object storing corresponding verification result
   */
  public static LivenessResult run(
      NetworkInfo info,
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Set<Edge> ingress) {
    LOGGER.info("Beginning to run liveness property analysis...");
    PathAnalyzer analyzer = info.toPathAnalyzer(prefix, location, target);
    InterferenceCheck interferenceCheck = info.toInterferenceCheck(prefix, location, target);

    LOGGER.info("LOOKING FOR GOOD PATH");
    Pair<Optional<Path>, List<Path>> paths =
        ingress == null ? analyzer.run() : analyzer.run(ingress);

    if (paths.getLeft().isEmpty()) {
      return new LivenessResult(Optional.empty(), paths.getRight(), Optional.empty());
    } else {
      LOGGER.info("CHECKING INTERFERENCE");
      // compute the reachable set of routes along the good path, at each node on that path
      Path goodPath = paths.getLeft().get();
      Map<Node, Invariant> reachableGood = goodPath.reachableRoutes();
      return new LivenessResult(paths.getLeft(), List.of(), interferenceCheck.run(reachableGood));
    }
  }

  public static LivenessResult run(
      NetworkInfo info, PrefixSpace prefix, Location location, Invariant target) {
    return run(info, prefix, location, target, null);
  }

  @Override
  public AnswerElement answer(NetworkSnapshot snapshot) {
    LOGGER.info("Within the answerer for liveness verification.");

    LOGGER.info("Gathering relevant information from snapshot...");
    NetworkInfo info =
        new NetworkInfo(_batfish, snapshot, _communityRegexes, _asPathRegexes, _default_assumption);
    LOGGER.info("Constructed Verification.NetworkInfo object");

    _assumptions.forEach(info::addAssumption);

    if (_target == null || _prefix.isEmpty()) {
      // if no target or prefix is provided, send back locations
      return info.getAnswerElement();
    } else {
      Map.Entry<Location, Invariant> target = buildLocationInvariant(info, true, _target);
      LivenessResult result;
      if (_ingress != null) {
        Set<Edge> origins = new HashSet<>();
        _ingress
            .instantiate(info)
            .forEach(
                loc -> {
                  if (loc instanceof Edge edge) {
                    origins.add(edge);
                  } else {
                    throw new BatfishException(
                        "Only considers traffic coming in on an edge (not originating at a node).");
                  }
                });
        result = run(info, _prefix, target.getKey(), target.getValue(), origins);
      } else {
        result = run(info, _prefix, target.getKey(), target.getValue());
      }
      LOGGER.info("Analysis done!");
      return result.getAnswerElement(info);
    }
  }
}
