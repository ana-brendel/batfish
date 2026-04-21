package org.batfish.minesweeper.question.liveness;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Inference;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.Setup;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.batfish.minesweeper.question.verificationutilities.Setup.buildLocationInvariant;
import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_liveness;

public class LivenessAnswerer extends Answerer {
  private static final Logger LOGGER = LogManager.getLogger(LivenessAnswerer.class);

  private final @Nonnull PrefixSpace _prefix;
  private final @Nullable Pair<Location.Builder, Invariant.Builder> _target;
  private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions = new HashMap<>();
  private final @Nonnull Set<RegexConstraint> _communityRegexes = new HashSet<>();
  private final @Nonnull Set<RegexConstraint> _asPathRegexes = new HashSet<>();
  private final @Nullable Invariant.Builder _default_assumption;
  private final @Nullable Location.Builders _ingress;
  private final boolean _exact_communities;

  public LivenessAnswerer(LivenessQuestion question, IBatfish batfish) {
    super(question, batfish);
    _prefix = question.get_prefix();
    _target = question.get_target();
    _default_assumption = question.get_default_assumption();
    _ingress = question.get_ingress();
    _exact_communities = question.get_exact_communities();

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
    Map<RoutingPolicy, List<TransferReturn>> computedPathsCache = new HashMap<>();
    LOGGER.info("Beginning to run liveness property analysis...");
    PathAnalyzer analyzer = info.toPathAnalyzer(prefix, location, target, computedPathsCache);
    InterferenceCheck interferenceCheck =
        info.toInterferenceCheck(prefix, location, target, computedPathsCache);

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
        new NetworkInfo(
            _batfish,
            snapshot,
            _communityRegexes,
            _asPathRegexes,
            _default_assumption,
            _exact_communities);
    LOGGER.info("Constructed Verification.NetworkInfo object");

    _assumptions.forEach(info::addAssumption);

    if (_target == null || _prefix.isEmpty()) {
      // if no target or prefix is provided, send back locations
      return info.getAnswerElement();
    } else {
      Map.Entry<Location, Invariant> target = buildLocationInvariant(info, true, _target);
      // LivenessResult result;
      Set<Edge> origins = new HashSet<>();
      if (_ingress != null) {
        _ingress
            .instantiate(info)
            .forEach(
                loc -> {
                  if (loc instanceof Edge edge && !edge.hasSrcNode()) {
                    origins.add(edge);
                  } else {
                    throw new BatfishException(
                        "Only considers traffic coming in on an edge (not originating at a node).");
                  }
                });
        // result = run(info, _prefix, target.getKey(), target.getValue(), origins);
      }
      // else {
      // result = run(info, _prefix, target.getKey(), target.getValue());
      // }
      // LOGGER.info("Analysis done!");
      // return result.getAnswerElement(info);
      return updatedRun(info, _prefix, target.getKey(), target.getValue(), origins);
    }
  }

  public static TableAnswerElement updatedRun(
      NetworkInfo info,
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Set<Edge> ingress) {
    Inference infer = info.toInference();
    if (!ingress.isEmpty()) {
      infer.setOrigins(ingress.stream().map(e -> (Location) e).collect(Collectors.toSet()));
    }
    infer.addPrefixToAssumptions(prefix);

    // Finding if good path exists through inference loop -- commented out, unsound
    //    Invariant goodPathCondition =
    //        new Invariant(info.tbdd, target.getBDDCopy().and(infer.prefixSpaceToBDD(prefix)));
    //    Pair<Location, Map<Location, Bgpv4Route>> reachable =
    //        infer.run(Map.of(location, goodPathCondition), Inference.Check.EXISTS, true);
    //    assert reachable.getKey() == null && reachable.getValue() != null;
    //    Map<Location, Bgpv4Route> routes = reachable.getValue();

    LOGGER.info("Searching for a good path (via checking shortest path from ingresses)...");
    Map<RoutingPolicy, List<TransferReturn>> computedPathsCache = new HashMap<>();
    PathExploration exploration =
        info.toPathExploration(prefix, location, target, ingress, computedPathsCache);
    Pair<Path, Set<Path>> paths = exploration.run();
    Map<Location, String> routes = new HashMap<>();
    if (paths.getKey() != null) {
      routes.put(paths.getKey().getStartingPoint(), paths.getKey().display(info));
    }

    TableAnswerElement tae = new TableAnswerElement(metadata_liveness());

    if (routes.isEmpty()) {
      LOGGER.info("No path found to satisfy the property.");
      tae.addRow(
          Row.builder()
              .put(Setup.RESULT_LABEL_COL, Setup.OVERALL_RESULT)
              .put(Setup.RESULT_VALUE_COL, "False (No Good Route Found)")
              .build());
      paths
          .getRight()
          .forEach(
              p ->
                  tae.addRow(
                      Row.builder()
                          .put(Setup.RESULT_LABEL_COL, Setup.BAD_PATH_LABEL)
                          .put(Setup.RESULT_VALUE_COL, p.displayStartCondition())
                          .build()));
    } else {
      LOGGER.info("FOUND good path");
      LinkedList<Row> rows = new LinkedList<>();
      // include starting points of potential good paths (only add 5 path origins)
      int count = 0;
      for (Location origin : routes.keySet()) {
        if (count < 5) {
          count += 1;
          rows.add(
              Row.builder()
                  .put(Setup.RESULT_LABEL_COL, Setup.GOOD_PATH_LABEL)
                  .put(
                      Setup.RESULT_VALUE_COL,
                      "[" + info.locationStr(origin) + "] " + routes.get(origin))
                  .build());
        }
      }
      LOGGER.info("Checking for interference...");
      // check for interference
      Invariant interferenceCondition =
          new Invariant(info.tbdd, target.negate().getBDD().and(infer.prefixSpaceToBDD(prefix)));
      Pair<Location, Map<Location, Bgpv4Route>> interferenceOccurs =
          infer.run(Map.of(location, interferenceCondition), Inference.Check.NONE_EXIST, true);
      assert interferenceOccurs.getKey() == null && interferenceOccurs.getValue() != null;
      LOGGER.info("Interference check COMPLETE");
      if (interferenceOccurs.getValue().isEmpty()) {
        tae.addRow(
            Row.builder()
                .put(Setup.RESULT_LABEL_COL, Setup.OVERALL_RESULT)
                .put(Setup.RESULT_VALUE_COL, "True")
                .build());
        rows.forEach(tae::addRow);
      } else {
        tae.addRow(
            Row.builder()
                .put(Setup.RESULT_LABEL_COL, Setup.OVERALL_RESULT)
                .put(Setup.RESULT_VALUE_COL, "False")
                .build());
        count = 0;
        for (Location origin : interferenceOccurs.getValue().keySet()) {
          if (count < 5) {
            count += 1;
            rows.add(
                Row.builder()
                    .put(
                        Setup.RESULT_LABEL_COL,
                        Setup.SOURCE_OF_INTERFERENCE + info.locationStr(origin))
                    .put(
                        Setup.RESULT_VALUE_COL,
                        interferenceOccurs.getValue().get(origin).toString())
                    .build());
          }
        }
        rows.forEach(tae::addRow);
      }
    }
    return tae;
  }
}
