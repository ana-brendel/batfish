package org.batfish.minesweeper.question.liveness;

import net.sf.javabdd.BDD;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;

public class InterferenceCheck {
  private final Path.Context context;

  private final PrefixSpace prefix;
  private final Location location;
  private final Invariant target;

  private final Map<Ip, Node> nodes;
  private final Map<Node, Set<Edge>> edgesByDestination;

  private final Queue<Location> working = new LinkedList<>();
  private final Map<Location, Invariant> inferred = new HashMap<>();

  public InterferenceCheck(
      @Nonnull Path.Context context,
      @Nonnull PrefixSpace prefix,
      @Nonnull Location location,
      @Nonnull Invariant target,
      @Nonnull Map<Ip, Node> nodes,
      @Nonnull Map<Node, Set<Edge>> edgesByDestination) {
    this.context = context;
    this.prefix = prefix;
    this.location = location;
    this.target = target;
    this.nodes = nodes;
    this.edgesByDestination = edgesByDestination;
  }

  /// Iteratively infer the "bad invariants" which allow for a "bad route" to reach the liveness
  // property location. Note,
  /// this is sound but not complete as BGP preferences, which we don't account for, might rule out
  // some of these "bad routes."
  private void inferenceLoop() {
    // carries out invariant inference similar to safety property, but we don't allow for denied
    // routes to be
    // considered in the weakest precondition computation
    while (!working.isEmpty()) {
      Location location = working.remove();
      Invariant property = inferred.get(location);
      if (location instanceof Edge edge && nodes.containsKey(edge.getSrc())) {
        RoutingPolicy exportPolicy = context.exports().get(edge);
        Invariant wp =
            exportPolicy == null
                ? property.copy()
                : property.weakestPrecondition(exportPolicy, false);
        Node src = nodes.get(edge.getSrc());
        Invariant existing = inferred.getOrDefault(src, Invariant.getFalse(context.tbdd()));
        // TODO verify that disjoining here is the correct move - we want to consider any "bad
        // route"
        Invariant updated =
            new Invariant(context.tbdd(), existing.wellFormedBDD().or(wp.wellFormedBDD()));
        inferred.put(src, updated);
        if (!existing.equals(updated) && !working.contains(src)) {
          working.add(src);
        }
      } else if (location instanceof Node node) {
        for (Edge edge : edgesByDestination.get(node)) {
          RoutingPolicy importPolicy = context.imports().get(edge);
          Invariant wp =
              importPolicy == null
                  ? property.copy()
                  : property.weakestPrecondition(importPolicy, false);
          Invariant existing = inferred.getOrDefault(edge, Invariant.getFalse(context.tbdd()));
          Invariant updated =
              new Invariant(context.tbdd(), existing.wellFormedBDD().or(wp.wellFormedBDD()));
          inferred.put(edge, updated);
          if (!existing.equals(updated) && !working.contains(edge)) {
            working.add(edge);
          }
        }
      }
    }
  }

  /// For all ingress locations, we find a counterexample if one exists
  private Map<Location, Bgpv4Route> interferenceExample() {
    Map<Location, Bgpv4Route> checks = new HashMap<>();
    for (Location assumption_location : context.assumptions().keySet()) {
      if (inferred.containsKey(assumption_location)) {
        BDD assumption = context.assumptions().get(assumption_location).wellFormedBDD();
        BDD badRouteCondition = inferred.get(assumption_location).wellFormedBDD();
        BDD intersection = assumption.and(badRouteCondition);
        if (!intersection.isZero()) {
          // if the intersection is not empty, then routes meeting this condition at this location
          // might cause interference
          BDD model =
              ModelGeneration.constraintsToModel(
                  intersection, context.tbdd().getConfigAtomicPredicates());
          Bgpv4Route counter =
              ModelGeneration.satAssignmentToBgpInputRoute(
                  model, context.tbdd().getConfigAtomicPredicates());
          checks.put(assumption_location, counter);
        }
      }
      // In the else branch, we didn't infer an incoming invariant, thus no route is possible so we
      // are good
    }
    return checks;
  }

  /// Checks for interference, if any counterexamples were found they are returned. (If the result
  // is
  /// empty, then this is interpreted as no interference detected.)
  public Optional<Map<Location, Bgpv4Route>> run() {
    inferred.clear();
    working.clear();
    Invariant condition =
        new Invariant(
            context.tbdd(), target.negate().wellFormedBDD().and(context.prefixSpaceToBDD(prefix)));
    if (condition.isFalse()) {
      // no possible "bad route" exists that matches the target prefix
      return Optional.empty();
    }
    inferred.put(location, condition);
    working.add(location.copy());
    inferenceLoop();
    Map<Location, Bgpv4Route> checks = interferenceExample();
    return checks.isEmpty() ? Optional.empty() : Optional.of(checks);
  }
}
