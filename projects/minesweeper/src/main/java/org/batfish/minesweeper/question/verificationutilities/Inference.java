package org.batfish.minesweeper.question.verificationutilities;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;

import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;
import static org.batfish.minesweeper.bdd.TransferBDDUtils.lessPreferredThanBgp;
import static org.batfish.minesweeper.question.verificationutilities.NetworkInfo.getRouteExample;

public class Inference {
  // private static final Logger LOGGER = LogManager.getLogger(Inference.class);
  private final TransferBDD tbdd;

  private final Map<Edge, RoutingPolicy> imports;
  private final Map<Edge, RoutingPolicy> exports;

  private final Map<Location, Invariant> checkedAssumptions;
  private final Map<Location, Invariant> enforcedAssumptions;

  private final Queue<Location> working = new LinkedList<>();
  private final Map<Location, Invariant> inferred = new HashMap<>();

  private final Set<Location> originsForExistence = new HashSet<>();

  /// For each node on the good path, the routes that are less preferred than every good route that
  /// can reach it (see addPreferenceRestrictions)
  private final Map<Node, BDD> lessPreferredByNode = new HashMap<>();

  private final Map<RoutingPolicy, List<TransferReturn>> computedPathsCache = new HashMap<>();

  public enum Check {
    SAFETY,
    EXISTS,
    NONE_EXIST
  }

  public Inference(
      TransferBDD tbdd,
      Map<Edge, RoutingPolicy> imports,
      Map<Edge, RoutingPolicy> exports,
      Map<Location, Invariant> checkedAssumptions,
      Map<Location, Invariant> enforcedAssumptions) {
    this.tbdd = tbdd;
    this.imports = imports;
    this.exports = exports;
    this.checkedAssumptions = checkedAssumptions;
    this.enforcedAssumptions = enforcedAssumptions;
    this.originsForExistence.addAll(checkedAssumptions.keySet());
  }

  public void setOrigins(Set<Location> origins) {
    this.originsForExistence.clear();
    this.originsForExistence.addAll(origins);
  }

  /// Records the routes that can reach each node along the good path, so that subsequent runs
  /// account for route preference: a route that is less preferred than every one of them is never
  /// selected at that node.
  public void addPreferenceRestrictions(@Nonnull Map<Node, Invariant> reachableGood) {
    lessPreferredByNode.values().forEach(BDD::free);
    lessPreferredByNode.clear();
    reachableGood.forEach(
        (node, good) -> {
          // if no good route reaches the node then there is nothing for other routes to lose to
          if (!good.isFalse()) {
            lessPreferredByNode.put(node, lessPreferredThanBgp(good.getBDD(), tbdd));
          }
        });
  }

  /// A route that is less preferred than the good route at a node is never selected there, so it
  /// does not matter what happens to it: a universal invariant can allow it, and an existential
  /// one (e.g., the routes that could interfere) can leave it out.  Does not consume inv.
  private Invariant accountForPreference(Location location, Invariant inv, boolean isUniversal) {
    if (!(location instanceof Node node)) {
      return inv;
    }
    BDD lessPreferred = lessPreferredByNode.get(node);
    if (lessPreferred == null) {
      return inv;
    }
    return new Invariant(
        tbdd,
        isUniversal
            ? inv.getBDDCopy().orWith(lessPreferred.id())
            : inv.getBDDCopy().diffWith(lessPreferred.id()));
  }

  private boolean checksFalseAssumption(Location location) {
    return checkedAssumptions.containsKey(location) && checkedAssumptions.get(location).isFalse();
  }

  private Invariant getWeakestPrecondition(
      Invariant post, boolean isUniversal, RoutingPolicy policy) {
    if (policy == null) {
      return post.copy();
    } else {
      return post.weakestPrecondition(policy, isUniversal, computedPathsCache);
    }
  }

  /// Combines the invariants based on whether the update is universal or existential. This frees
  /// the `update` invariant provided; the `existing` is unchanged.
  private Invariant mergeInvariants(
      RoutingPolicy policy, Invariant post, Location location, boolean isUniversal) {
    Invariant wp = this.getWeakestPrecondition(post, isUniversal, policy);
    if (location instanceof Edge edge) {
      // an edge invariant is stated from the sender's point of view: it constrains the route as
      // the sender's export policy produced it, before BGP's own export transformations.  This
      // matches how checked assumptions on edges are interpreted.
      wp = wp.preImport(edge.isEBGP());
    }
    // get inferred if present, otherwise get enforced assumption, otherwise default is true
    Invariant existing =
        inferred.getOrDefault(
            location,
            enforcedAssumptions.getOrDefault(
                location, isUniversal ? new Invariant(tbdd) : Invariant.getFalse(tbdd)));
    Invariant updated =
        isUniversal
            ? new Invariant(tbdd, existing.getBDDCopy().and(wp.getBDDCopy()))
            : new Invariant(tbdd, existing.getBDDCopy().or(wp.getBDDCopy()));
    wp.free();
    // this must be done on every update, not just to the targets: otherwise an update that comes
    // back around a cycle would undo it
    Invariant adjusted = accountForPreference(location, updated, isUniversal);
    if (adjusted != updated) {
      updated.free();
    }
    return adjusted;
  }

  private Optional<Location> inferenceLoop(boolean isUniversal) {
    while (!working.isEmpty()) {
      Location location = working.remove();
      assert inferred.containsKey(location)
          : "Trying to get existing invariant for unvisited location: " + location;
      Invariant property = inferred.get(location);

      boolean locationIsEdge = location instanceof Edge;
      for (Location predecessor : location.predecessors()) {
        if (this.checksFalseAssumption(predecessor)) {
          // inferred can be false because false implies anything
          inferred.put(predecessor, Invariant.getFalse(this.tbdd));
          continue;
        }
        assert (predecessor instanceof Edge && !locationIsEdge)
            || (predecessor instanceof Node && locationIsEdge);
        RoutingPolicy policy = locationIsEdge ? exports.get(location) : imports.get(predecessor);
        Invariant existing = inferred.get(predecessor);
        Invariant updated = this.mergeInvariants(policy, property, predecessor, isUniversal);
        inferred.put(predecessor, updated);
        if (updated.isFalse() && isUniversal) {
          if (existing != null) {
            existing.free();
          }
          return Optional.of(predecessor);
        } else if ((existing == null || !existing.equals(updated))
            && !working.contains(predecessor)) {
          if (existing != null) {
            existing.free();
          }
          working.add(predecessor);
        }
      }
    }
    return Optional.empty(); // success - no counterexample
  }

  private Map<Location, Bgpv4Route> universalAssumptionCheck(boolean earlyReturn) {
    Map<Location, Bgpv4Route> checks = new HashMap<>();
    for (Location location : checkedAssumptions.keySet()) {
      // fix to make sure that we only consider well-formed assumptions
      Invariant wellFormedAssumption =
          new Invariant(
              tbdd,
              checkedAssumptions
                  .get(location)
                  .getBDDCopy()
                  .andWith(tbdd.getOriginalRoute().wellFormednessConstraints(true)));
      Invariant infer = inferred.getOrDefault(location, Invariant.getFalse(tbdd));
      if (!wellFormedAssumption.implies(infer)) {
        BDD constraint =
            wellFormedAssumption
                .getBDDCopy()
                .andWith(infer.getBDD().not())
                .andWith(tbdd.getOriginalRoute().wellFormednessConstraints(true));
        assert !constraint.isZero();
        checks.put(location, getRouteExample(tbdd, constraint));
        constraint.free();
        if (earlyReturn) {
          return checks;
        }
      }
    }
    return checks;
  }

  private Map<Location, Bgpv4Route> nonExistentialAssumptionCheck(boolean earlyReturn) {
    Map<Location, Bgpv4Route> checks = new HashMap<>();
    for (Location assumption_location : checkedAssumptions.keySet()) {
      if (inferred.containsKey(assumption_location)) {
        BDD assumption = checkedAssumptions.get(assumption_location).getBDDCopy();
        BDD intersection = assumption.andWith(inferred.get(assumption_location).getBDDCopy());
        intersection.andWith(tbdd.getOriginalRoute().wellFormednessConstraints(true));
        // if there exists some assumption which also satisfies the "bad condition", add counter
        if (!intersection.isZero()) {
          checks.put(assumption_location, getRouteExample(tbdd, intersection));
          if (earlyReturn) {
            assumption.free();
            return checks;
          }
        }
        assumption.free();
      }
      // In the else branch, we didn't infer an incoming invariant, thus no route is possible so we
      // are good
    }
    return checks;
  }

  private Map<Location, Bgpv4Route> existentialAssumptionCheck(boolean earlyReturn) {
    Map<Location, Bgpv4Route> checks = new HashMap<>();
    for (Location assumption_location : originsForExistence) {
      if (inferred.containsKey(assumption_location)) {
        Invariant inferredWithOutProtocolHistory =
            new Invariant(
                tbdd,
                inferred
                    .get(assumption_location)
                    .getBDDCopy()
                    .existEq(tbdd.getOriginalRoute().getProtocolHistory().support()));

        if (checkedAssumptions.get(assumption_location).implies(inferredWithOutProtocolHistory)) {
          BDD incoming = checkedAssumptions.get(assumption_location).getBDDCopy();
          incoming.andWith(tbdd.getOriginalRoute().wellFormednessConstraints(true));
          if (!incoming.isZero()) {
            checks.put(assumption_location, getRouteExample(tbdd, incoming));
            if (earlyReturn) {
              return checks;
            }
          }
        }
      }
    }
    return checks;
  }

  // Returns counterexamples for universal queries, returns routes which can satisfy the
  // reachability query
  public Pair<Location, Map<Location, Bgpv4Route>> run(
      Map<Location, Invariant> targets, Check check, boolean earlyReturn) {
    boolean isUniversal = check == Check.SAFETY;
    inferred.clear();
    working.clear();
    targets.forEach((loc, inv) -> inferred.put(loc, accountForPreference(loc, inv, isUniversal)));
    working.addAll(targets.keySet());
    Optional<Location> cex = this.inferenceLoop(isUniversal);
    if (cex.isPresent()) {
      return Pair.of(cex.get(), null);
    } else {
      return Pair.of(
          null,
          isUniversal
              ? universalAssumptionCheck(earlyReturn)
              : check == Check.EXISTS
                  ? existentialAssumptionCheck(earlyReturn)
                  : nonExistentialAssumptionCheck(earlyReturn));
    }
  }

  public BDD prefixSpaceToBDD(PrefixSpace space) {
    BDDRoute r = new BDDRoute(tbdd.getFactory(), tbdd.getConfigAtomicPredicates());
    BDDFactory factory = r.getPrefix().getFactory();
    BDD result = factory.zero();
    for (PrefixRange range : space.getPrefixRanges()) {
      BDD rangeBDD = isRelevantForDestination(r, range);
      result = result.or(rangeBDD);
    }
    return result;
  }

  public void addPrefixToAssumptions(PrefixSpace space) {
    for (Location location : checkedAssumptions.keySet()) {
      BDD existing = checkedAssumptions.get(location).getBDDCopy();
      existing.andWith(prefixSpaceToBDD(space));
      checkedAssumptions.put(location, new Invariant(tbdd, existing));
    }
  }
}
