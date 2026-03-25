package org.batfish.minesweeper.question.liveness;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.bdd.MutableBDDInteger;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.TransferBDDUtils;
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

import static org.batfish.minesweeper.question.verificationutilities.NetworkInfo.getRouteExample;

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
  // property location. The reachableGood parameter allows us to restrict the inference to only
  // consider routes that are not less preferred than the good routes that can reach nodes
  // along the "good" path.
  private void inferenceLoop(Map<Node, Invariant> reachableGood) {
    // carries out invariant inference similar to safety property, but we don't allow for denied
    // routes to be considered in the weakest precondition computation
    while (!working.isEmpty()) {
      Location location = working.remove();
      Invariant property = inferred.get(location);
      if (location instanceof Edge edge && nodes.containsKey(edge.getSrc())) {
        if (edge.isEBGP()) {
          // Symbolically undo the effect of prepending the source node's ASN to the AS-path
          // on the property by replacing all references to the AS-path length (call it x) with
          // (x + 1). Then when we do the WP computation below we'll get the right precondition
          // for the source node.
          MutableBDDInteger origAsPathLength = context.tbdd().getOriginalRoute().getAsPathLength();
          MutableBDDInteger asPathLengthPlusOne =
              origAsPathLength.addClipping(
                  MutableBDDInteger.makeFromValue(context.tbdd().getFactory(), 4, 1));
          BDDPairing pairing = context.tbdd().getFactory().makePair();
          asPathLengthPlusOne.augmentPairing(origAsPathLength, pairing);
          BDD old = property.getBDD();
          BDD updated = old.veccompose(pairing);
          property = new Invariant(context.tbdd(), updated);
        }
        RoutingPolicy exportPolicy = context.exports().get(edge);
        Invariant wp =
            exportPolicy == null
                ? property.copy()
                : property.weakestPrecondition(exportPolicy, false);
        Node src = nodes.get(edge.getSrc());
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
        for (Edge edge : edgesByDestination.get(node)) {
          RoutingPolicy importPolicy = context.imports().get(edge);
          Invariant wp =
              importPolicy == null
                  ? property.copy()
                  : property.weakestPrecondition(importPolicy, false);
          // if there is no inferred assumption, use the negation of the enforced assumption if
          // present, otherwise default is false
          Invariant existing =
              inferred.getOrDefault(
                  edge,
                  context.enforcedAssumptions().containsKey(edge)
                      ? context.enforcedAssumptions().get(edge).negate()
                      : Invariant.getFalse(context.tbdd()));
          BDD updatedBDD = existing.getBDDCopy().or(wp.getBDDCopy());
          // we maintain an invariant that the edge invariants represent the routes
          // from the sender's perspective; the call to preImport converts from the
          // receiver's perspective to the sender's perspective
          Invariant updated = new Invariant(context.tbdd(), updatedBDD).preImport();
          updatedBDD.free();
          inferred.put(edge, updated);
          if (!existing.equals(updated) && !working.contains(edge)) {
            working.add(edge);
          }
          existing.free(); // can be freed because the updated invariant has replaced
          wp.free();
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
    inferenceLoop(reachableGood);
    Map<Location, Bgpv4Route> checks = interferenceExample();
    return checks.isEmpty() ? Optional.empty() : Optional.of(checks);
  }
}
