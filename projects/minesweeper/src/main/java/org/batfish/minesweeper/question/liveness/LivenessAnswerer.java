package org.batfish.minesweeper.question.liveness;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.Setup;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.batfish.minesweeper.question.verificationutilities.Setup.buildInvariant;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_liveness;
import static org.batfish.minesweeper.question.verificationutilities.Setup.nonDefaultRoute;

public class LivenessAnswerer extends Answerer {
  private static final Logger LOGGER = LogManager.getLogger(LivenessAnswerer.class);

  private final @Nonnull PrefixSpace _prefix;
  private final @Nullable Pair<Location.Builder, Invariant.Builder> _target;
  private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions;
  private final @Nonnull Set<RegexConstraint> _communityRegexes;
  private final @Nonnull Set<RegexConstraint> _asPathRegexes;
  private final @Nullable Invariant.Builder _default_assumption;
  private final @Nullable Location.Builder _ingress;

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
    _assumptions = new HashMap<>();
    for (int i = 0; i < invAssumptions.size(); i++) {
      _assumptions.put(locAssumptions.get(i), invAssumptions.get(i));
    }

    _communityRegexes = new HashSet<>();
    invAssumptions.forEach(
        clauses ->
            clauses
                .getClauses()
                .forEach(c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints())));
    _asPathRegexes = new HashSet<>(); // not included in the NetworkClause nor Invariant class yet
    if (_target != null) {
      _target
          .getRight()
          .getClauses()
          .forEach(c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints()));
    }
  }

  public record Result(
      Optional<Path> goodPath,
      List<Path> badPaths,
      Optional<Map<Location, Bgpv4Route>> potentialInterferences) {
    public TableAnswerElement getAnswerElement(NetworkInfo info) {
      TableAnswerElement tae = new TableAnswerElement(metadata_liveness());

      boolean verified =
          goodPath.isPresent()
              && (potentialInterferences.isEmpty() || potentialInterferences.get().isEmpty());

      // add overall result
      tae.addRow(
          Row.builder()
              .put(Setup.RESULT_LABEL_COL, Setup.OVERALL_RESULT)
              .put(Setup.RESULT_VALUE_COL, verified ? "True" : "False")
              .build());

      // add the good route, if present
      goodPath.ifPresent(
          p ->
              tae.addRow(
                  Row.builder()
                      .put(Setup.RESULT_LABEL_COL, Setup.GOOD_PATH_LABEL)
                      .put(Setup.RESULT_VALUE_COL, p.display(info))
                      .build()));

      // if no good paths are found, report back paths which fail to help diagnose problem
      assert goodPath.isPresent() || !badPaths.isEmpty();
      badPaths.forEach(
          path ->
              tae.addRow(
                  Row.builder()
                      .put(Setup.RESULT_LABEL_COL, Setup.BAD_PATH_LABEL)
                      .put(Setup.RESULT_VALUE_COL, path.displayBadPath(info))
                      .build()));

      // add possible interference, if applicable
      assert badPaths.isEmpty() || potentialInterferences.isEmpty();
      potentialInterferences.ifPresent(
          interferences ->
              interferences.forEach(
                  (entersAt, counter) ->
                      tae.addRow(
                          Row.builder()
                              .put(
                                  Setup.RESULT_LABEL_COL,
                                  Setup.SOURCE_OF_INTERFERENCE + info.locationStr(entersAt))
                              .put(Setup.RESULT_VALUE_COL, nonDefaultRoute(counter))
                              .build())));

      return tae;
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
  public static Result run(
      NetworkInfo info, PrefixSpace prefix, Location location, Invariant target, Edge ingress) {
    LOGGER.info("Beginning to run liveness property analysis...");
    PathAnalyzer analyzer = info.toPathAnalyzer(prefix, location, target);
    InterferenceCheck interferenceCheck = info.toInterferenceCheck(prefix, location, target);

    Pair<Optional<Path>, List<Path>> paths =
        ingress == null ? analyzer.run() : analyzer.run(ingress);

    if (paths.getLeft().isEmpty()) {
      return new Result(Optional.empty(), paths.getRight(), Optional.empty());
    } else {
      // compute the reachable set of routes along the good path, at each node on that path
      Path goodPath = paths.getLeft().get();
      Map<Node, Invariant> reachableGood = goodPath.reachableRoutes();
      return new Result(paths.getLeft(), List.of(), interferenceCheck.run(reachableGood));
    }
  }

  public static Result run(
      NetworkInfo info, PrefixSpace prefix, Location location, Invariant target) {
    return run(info, prefix, location, target, null);
  }

  @Override
  public AnswerElement answer(NetworkSnapshot snapshot) {
    // Gathering and formatting information from snapshot
    SpecifierContext context = _batfish.specifierContext(snapshot);
    Map<String, Configuration> configs = context.getConfigs();
    LOGGER.info("Creating ConfigAtomicPredicates for analysis...");
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(_communityRegexes, _asPathRegexes, configs.values());
    TransferBDD tbdd = new TransferBDD(configAPs);
    // we want the default, if not provided, to be that the traffic has the target prefix
    NetworkInfo info =
        _default_assumption != null
            ? new NetworkInfo(tbdd, configs, _default_assumption.build(tbdd, null))
            : new NetworkInfo(tbdd, configs);

    _assumptions.forEach(info::addAssumption);

    if (_target == null || _prefix.isEmpty()) {
      // if no target or prefix is provided, send back locations
      return info.getAnswerElement();
    } else {
      Map.Entry<Location, Invariant> target = buildInvariant(info, true, _target);
      Result result;
      if (_ingress != null && _ingress.instantiate(info) instanceof Edge ingress) {
        result = run(info, _prefix, target.getKey(), target.getValue(), ingress);
      } else {
        result = run(info, _prefix, target.getKey(), target.getValue());
      }
      LOGGER.info("Analysis done!");
      return result.getAnswerElement(info);
    }
  }
}
