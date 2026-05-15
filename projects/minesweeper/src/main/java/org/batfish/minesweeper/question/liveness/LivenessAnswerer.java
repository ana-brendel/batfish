package org.batfish.minesweeper.question.liveness;

import net.sf.javabdd.BDD;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.safety.Infer;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Edge;
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
import java.util.Set;

import static org.batfish.minesweeper.question.verificationutilities.Setup.buildTargetLocationInvariant;
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
      Map.Entry<Location, Invariant> target = buildTargetLocationInvariant(info, true, _target);
      Set<Edge> origins = new HashSet<>();
      if (_ingress != null) {
        _ingress
            .instantiate(info)
            .forEach(
                loc -> {
                  // removed the originate outside network requirement (!edge.hasSrcNode())
                  if (loc instanceof Edge edge) {
                    origins.add(edge);
                  } else {
                    throw new BatfishException(
                        "Only considers traffic coming in on an edge (not originating at a node).");
                  }
                });
      }
      return run(info, _prefix, target.getKey(), target.getValue(), origins);
    }
  }

  public static TableAnswerElement run(
      NetworkInfo info,
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Set<Edge> ingress) {
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

      // Right now, this checks all the constraints hold at the same time to limit queries,
      assert paths.getKey() != null;

      Path weakenedPathConstraints = paths.getKey();
      Infer inference = info.toInfer();

      /// IN PROGRESS: commented out code attempts to weaken the reachability constraints
      // Pair<Path, Map<Location, BDD>> temp =
      //    exploration.weakenConstraints(paths.getKey().getLocations());
      // Path weakenedPathConstraints = temp.getLeft();
      // Map<Location, BDD> auxiliaryRequirements = temp.getRight();

      // enforce that all reachability conditions hold (no interference)
      for (Map.Entry<Location, Invariant> entry :
          weakenedPathConstraints.getConstraints().entrySet()) {
        if (entry.getKey() instanceof Node) {
          BDD bdd = entry.getValue().getBDDCopy();
          // if (auxiliaryRequirements.containsKey(entry.getKey())) {
          //  bdd.orWith(bdd);
          // }
          Invariant removeProtocolHistory =
              new Invariant(
                  info.tbdd,
                  bdd.existEq(info.tbdd.getOriginalRoute().getProtocolHistory().support()));
          inference.addProperty(entry.getKey(), removeProtocolHistory);
        }
      }

      /* for (Map.Entry<Location, BDD> entry : auxiliaryRequirements.entrySet()) {
        if (entry.getKey() instanceof Node) {
          Invariant removeProtocolHistory =
              new Invariant(
                  info.tbdd,
                  entry
                      .getValue()
                      .existEq(info.tbdd.getOriginalRoute().getProtocolHistory().support()));
          if (!inference.getTargets().containsKey(entry.getKey())) {
            inference.addProperty(entry.getKey(), removeProtocolHistory);
          }
        }
      } */

      // added true flag to push false through in case there denied traffic that is actually ok
      // because it is denied -- so the inference shouldn't be halted if false is inferred
      Infer.Result result = inference.run(true);
      Map<Location, String> cex = new HashMap<>();
      result.checks.forEach((l, r) -> cex.put(l, r.toString()));
      result.counter.ifPresent(
          counterExample ->
              cex.put(counterExample.location(), "Inferred False (Dead End for Traffic)"));
      Pair<Location, Map<Location, String>> interferenceOccurs = Pair.of(null, cex);

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
                    .put(Setup.RESULT_VALUE_COL, interferenceOccurs.getValue().get(origin))
                    .build());
          }
        }
        rows.forEach(tae::addRow);
      }
    }
    return tae;
  }
}
