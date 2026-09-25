package org.batfish.minesweeper.question.liveness;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.TransferBDDUtils;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;

import static org.batfish.minesweeper.question.verificationutilities.NetworkInfo.getRouteExample;

public class InterferenceCheck {
  private static final Logger LOGGER = LogManager.getLogger(InterferenceCheck.class);
  private final Path.Context context;

  private final PrefixSpace prefix;
  private final Location location;
  private final Invariant target;

  private final Queue<Location> working = new LinkedList<>();
  private final Map<Location, Invariant> inferred = new HashMap<>();
  private final Map<RoutingPolicy, List<TransferReturn>> computedPathsCache;

  public InterferenceCheck(
      @Nonnull Path.Context context,
      @Nonnull PrefixSpace prefix,
      @Nonnull Location location,
      @Nonnull Invariant target,
      @Nonnull Map<RoutingPolicy, List<TransferReturn>> computedPathsCache) {
    this.context = context;
    this.prefix = prefix;
    this.location = location;
    this.target = target;
    this.computedPathsCache = computedPathsCache;
  }

  private boolean checksFalseAssumption(Location location) {
    return context.checkedAssumptions().containsKey(location)
        && context.checkedAssumptions().get(location).isFalse();
  }

  /// Iteratively infer the "bad invariants" which allow for a "bad route" to reach the liveness
  // property location. The reachableGood parameter allows us to restrict the inference to only
  // consider routes that are not less preferred than the good routes that can reach nodes
  // along the "good" path.
  private void inferenceLoop(Map<Node, Invariant> reachableGood) {
    // carries out invariant inference similar to safety property, but we don't allow for denied
    // routes to be considered in the weakest precondition computation
    while (!working.isEmpty()) {
      Location location = working.remove();
      Invariant property = inferred.get(location);
      if (location instanceof Edge edge && edge.hasSrcNode()) {
        Node src = edge.getSrcNode();
        assert src != null;
        if (this.checksFalseAssumption(src)) {
          // inferred can be false because false implies anything
          inferred.put(src, Invariant.getFalse(this.context.tbdd()));
          continue;
        }
        assert edge.getSrcNode() != null;
        // the prepending of the source node's ASN to the AS-path on an EBGP session is undone by
        // the preImport that produced this edge's invariant
        RoutingPolicy exportPolicy = context.exports().get(edge);
        Invariant wp =
            exportPolicy == null
                ? property.copy()
                : property.weakestPrecondition(exportPolicy, false, this.computedPathsCache);
        // if there is no inferred assumption, use the negation of the enforced assumption if
        // present, otherwise default is false
        Invariant existing =
            inferred.getOrDefault(
                src,
                context.enforcedAssumptions().containsKey(src)
                    ? context.enforcedAssumptions().get(src).negate()
                    : Invariant.getFalse(context.tbdd()));
        Invariant updated =
            new Invariant(context.tbdd(), existing.getBDDCopy().or(wp.getBDDCopy()));
        if (reachableGood.containsKey(src)) {
          // restrict the inferred invariant to only those routes that are not
          // less preferred than the good routes that are reachable
          BDD reachableGoodBDD = reachableGood.get(src).getBDD();
          BDD notLessPreferred =
              TransferBDDUtils.lessPreferredThanBgp(reachableGoodBDD, context.tbdd()).notEq();
          BDD restricted = notLessPreferred.andWith(updated.getBDD());
          updated = new Invariant(context.tbdd(), restricted);
        }
        inferred.put(src, updated);
        if (!existing.equals(updated) && !working.contains(src)) {
          working.add(src);
        }
        existing.free(); // can be freed because the updated invariant has replaced
        wp.free();
      } else if (location instanceof Node node) {
        for (Edge edge : node.getAllIncomingEdges()) {
          if (this.checksFalseAssumption(edge)) {
            // inferred can be false because false implies anything
            inferred.put(edge, Invariant.getFalse(this.context.tbdd()));
            continue;
          }
          RoutingPolicy importPolicy = context.imports().get(edge);
          Invariant wp =
              importPolicy == null
                  ? property.copy()
                  : property.weakestPrecondition(importPolicy, false, this.computedPathsCache);
          // if there is no inferred assumption, use the negation of the enforced assumption if
          // present, otherwise default is false
          Invariant existing =
              inferred.getOrDefault(
                  edge,
                  context.enforcedAssumptions().containsKey(edge)
                      ? context.enforcedAssumptions().get(edge).negate()
                      : Invariant.getFalse(context.tbdd()));
          // we maintain an invariant that the edge invariants represent the routes
          // from the sender's perspective; the call to preImport converts from the
          // receiver's perspective to the sender's perspective.  The existing invariant is
          // already from the sender's perspective, so it must not be converted again.
          Invariant fromSender = wp.preImport(edge.isEBGP()); // consumes wp
          Invariant updated =
              new Invariant(context.tbdd(), existing.getBDDCopy().orWith(fromSender.getBDDCopy()));
          inferred.put(edge, updated);
          if (!existing.equals(updated) && !working.contains(edge)) {
            working.add(edge);
          }
          existing.free(); // can be freed because the updated invariant has replaced
          fromSender.free();
        }
      }
    }
  }

  /// For all ingress locations, we find a counterexample if one exists
  private Map<Location, Bgpv4Route> interferenceExample() {
    Map<Location, Bgpv4Route> checks = new HashMap<>();
    for (Location assumption_location : context.checkedAssumptions().keySet()) {
      if (inferred.containsKey(assumption_location)) {
        BDD assumption = context.checkedAssumptions().get(assumption_location).getBDDCopy();
        BDD intersection = assumption.andWith(inferred.get(assumption_location).getBDDCopy());
        intersection.andWith(context.tbdd().getOriginalRoute().wellFormednessConstraints(true));
        // if there exists some assumption which also satisfies the "bad condition", add counter
        if (!intersection.isZero()) {
          checks.put(assumption_location, getRouteExample(context.tbdd(), intersection));
        }
        assumption.free();
      }
      // In the else branch, we didn't infer an incoming invariant, thus no route is possible so we
      // are good
    }
    return checks;
  }

  /// Checks for interference, if any counterexamples were found they are returned. (If the result
  /// is empty, then this is interpreted as no interference detected.)
  /// The reachableGood parameter allows us to restrict the inference to only consider routes that
  // are not less preferred than the good routes that can reach nodes along the "good" path.
  public Optional<Map<Location, Bgpv4Route>> run(Map<Node, Invariant> reachableGood) {
    LOGGER.info("Isolating local preference conditions...");
    inferred.clear();
    working.clear();
    BDD conditionBDD = target.negate().getBDD().and(context.prefixSpaceToBDD(prefix));
    if (location instanceof Node node && reachableGood.containsKey(node)) {
      // restrict the condition to only those routes that are not
      // less preferred than the good routes that are reachable
      BDD reachableGoodBDD = reachableGood.get(node).getBDD();
      BDD notLessPreferred =
          TransferBDDUtils.lessPreferredThanBgp(reachableGoodBDD, context.tbdd()).notEq();
      conditionBDD.andWith(notLessPreferred);
    }
    Invariant condition = new Invariant(context.tbdd(), conditionBDD);
    if (condition.isFalse()) {
      // no possible "bad route" exists that matches the target prefix
      return Optional.empty();
    }
    inferred.put(location, condition);
    working.add(location.copy());
    LOGGER.info("Running interference check via inference loop...");
    inferenceLoop(reachableGood);
    Map<Location, Bgpv4Route> checks = interferenceExample();
    return checks.isEmpty() ? Optional.empty() : Optional.of(checks);
  }
}
