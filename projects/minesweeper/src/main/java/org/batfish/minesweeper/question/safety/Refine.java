package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import static org.batfish.minesweeper.bdd.TransferBDDUtils.interpolate;
import static org.batfish.minesweeper.question.safety.Infer.copyInferred;

public class Refine {
  private static final Logger LOGGER = LogManager.getLogger(Refine.class);

  private final TransferBDD tbdd;
  private final Map<Ip, Node> nodes;
  private final Map<Edge, RoutingPolicy> imports;
  private final Map<Edge, RoutingPolicy> exports;
  private final Set<Edge> enteringNetwork;

  private final Map<Location, Invariant> targets;
  private final Map<Location, Invariant> assumptions;
  private final Map<Location, Invariant> inferred;

  private final Queue<Location> working = new LinkedList<>();

  /// Class to build Refine object, used by Infer class to get a Refine object from Infer object
  public static class Builder {
    private final TransferBDD tbdd;
    private Map<Ip, Node> nodes;
    private Map<Edge, RoutingPolicy> imports;
    private Map<Edge, RoutingPolicy> exports;
    private Map<Location, Invariant> targets;
    private Map<Location, Invariant> assumptions;
    private Set<Edge> incoming;
    private Map<Location, Invariant> inferred;

    public Builder(TransferBDD tbdd) {
      this.tbdd = tbdd;
    }

    public Builder setNodes(Map<Ip, Node> nodes) {
      this.nodes = nodes;
      return this;
    }

    public Builder setImports(Map<Edge, RoutingPolicy> imports) {
      this.imports = imports;
      return this;
    }

    public Builder setExports(Map<Edge, RoutingPolicy> exports) {
      this.exports = exports;
      return this;
    }

    public Builder setTargets(Map<Location, Invariant> targets) {
      this.targets = targets;
      return this;
    }

    public Builder setAssumptions(Map<Location, Invariant> assumptions) {
      this.assumptions = assumptions;
      return this;
    }

    public Builder setIncoming(Set<Location> incoming) {
      assert incoming.stream().allMatch(l -> l instanceof Edge);
      this.incoming = incoming.stream().map(l -> (Edge) l).collect(Collectors.toSet());
      return this;
    }

    public Builder setInferred(Map<Location, Invariant> inferred) {
      this.inferred = inferred;
      return this;
    }

    public Refine build() {
      return new Refine(
          this.tbdd,
          this.nodes,
          this.imports,
          this.exports,
          this.targets,
          this.assumptions,
          this.incoming,
          this.inferred);
    }
  }

  /// Provides builder instance
  public static Builder builder(TransferBDD tbdd) {
    return new Builder(tbdd);
  }

  /// Stores useful results collected during invariant refinement
  public static class Result {
    public final boolean verified;
    public final Map<Location, Invariant> initial;
    public final Map<Location, Invariant> refined;
    public final Map<BDD, String> cache = new HashMap<>();

    public Result(
        boolean verified, Map<Location, Invariant> initial, Map<Location, Invariant> refined) {
      this.verified = verified;
      this.initial = initial;
      this.refined = refined;
    }

    /// Included for testing - displays the initial inferred invariants
    public Map<Location, String> displayInitial() {
      Map<Location, String> strings = new HashMap<>();

      initial.forEach((loc, inv) -> strings.put(loc, inv.toString(true, this.cache)));
      return strings;
    }

    /// Included for testing - displays the refined inferred invariants
    public Map<Location, String> displayRefinement() {
      Map<Location, String> strings = new HashMap<>();
      refined.forEach((loc, inv) -> strings.put(loc, inv.toString(true, this.cache)));
      return strings;
    }
  }

  private Refine(
      TransferBDD tbdd,
      Map<Ip, Node> nodes,
      Map<Edge, RoutingPolicy> imports,
      Map<Edge, RoutingPolicy> exports,
      Map<Location, Invariant> targets,
      Map<Location, Invariant> assumptions,
      Set<Edge> incoming,
      Map<Location, Invariant> inferred) {
    this.tbdd = tbdd;
    this.nodes = nodes;
    this.imports = imports;
    this.exports = exports;
    this.targets = targets;
    this.assumptions = assumptions;
    this.enteringNetwork =
        incoming.stream().filter(inferred::containsKey).collect(Collectors.toSet());
    this.inferred = inferred;
  }

  ///  Performs iterative invariant refinement using the strongest postcondition, interpolation and
  // inferred invariants
  private Map<Location, Invariant> strengtheningLoop() {
    // we assume that the working list includes the correct starting points for refinement, that
    // is specifically ingress edges
    Map<Location, Invariant> refinements = new HashMap<>();
    // assigning all the starting incoming edges back to their inferred invariant otherwise set
    // false
    inferred
        .keySet()
        .forEach(
            starter ->
                refinements.put(
                    starter,
                    working.contains(starter) ? inferred.get(starter) : Invariant.getFalse(tbdd)));
    while (!working.isEmpty()) {
      Location lastKnown = working.remove();
      LOGGER.info("Working to refine the property following: {}", lastKnown);
      if (lastKnown instanceof Edge edge && nodes.containsKey(edge.getDst())) {
        Node toRefine = nodes.get(edge.getDst());
        if (!inferred.containsKey(toRefine)) {
          throw new BatfishException(
              "This should not happen - any reachable node should have inferred invariant");
        }
        Invariant weakest = inferred.get(toRefine).copy();
        RoutingPolicy importPolicy = imports.get(edge);
        Invariant strongest =
            importPolicy == null
                ? refinements.get(edge).copy()
                : refinements.get(edge).strongestPostcondition(importPolicy);
        BDD interpolant =
            interpolate(tbdd, strongest.wellFormedBDD(), weakest.wellFormedBDD())
                .orElse(weakest.wellFormedBDD());
        Invariant previous = refinements.get(toRefine);
        refinements.put(toRefine, new Invariant(tbdd, interpolant.or(previous.wellFormedBDD())));
        if (!refinements.get(toRefine).equals(previous)) {
          working.add(toRefine);
        }
      } else if (lastKnown instanceof Node source) {
        Invariant precondition = refinements.get(source);
        // should try to use neighbor mapping to improve runtime
        for (Location neighbor : inferred.keySet()) {
          if (neighbor instanceof Edge toRefine && toRefine.isSrc(source)) {
            if (!inferred.containsKey(toRefine)) {
              throw new BatfishException(
                  "This should not happen - any reachable edge should have inferred invariant");
            }
            Invariant weakest = inferred.get(toRefine).copy();
            RoutingPolicy exportPolicy = exports.get(toRefine);
            Invariant strongest =
                exportPolicy == null
                    ? precondition.copy()
                    : precondition.strongestPostcondition(exportPolicy);
            BDD interpolant =
                interpolate(tbdd, strongest.wellFormedBDD(), weakest.wellFormedBDD())
                    .orElse(weakest.wellFormedBDD());
            Invariant previous = refinements.put(toRefine, new Invariant(tbdd, interpolant));
            if (previous == null || !refinements.get(toRefine).equals(previous)) {
              // if there is already an edge entering this destination, we don't need to add it
              // twice
              if (!working.contains(nodes.get(toRefine.getDst()))) {
                working.add(toRefine);
              }
            }
          }
        }
      }
    }
    return refinements;
  }

  /// Returns refinement result object without performing refinement
  public Result noRefinement() {
    boolean verified =
        assumptions.keySet().stream()
            .allMatch(
                loc ->
                    inferred.containsKey(loc) && assumptions.get(loc).implies(inferred.get(loc)));
    return new Result(verified, inferred, inferred);
  }

  /// Driving method to perform invariant refinement
  public Result refine() {
    working.clear();
    // TODO determine if we want to include assumptions as ingress nodes (or maybe have option for
    // user to specify ingress)
    // right now we just use any edge entering the network, not including assumptions within
    // network... maybe we should swap
    // any inferred invariant specifically with the assumption as the assumption would be stronger
    // (if verification didn't
    // produce any counterexample)
    working.addAll(enteringNetwork);
    if (working.isEmpty()) {
      boolean verified =
          assumptions.keySet().stream()
              .allMatch(
                  loc ->
                      inferred.containsKey(loc) && assumptions.get(loc).implies(inferred.get(loc)));
      return new Result(verified, inferred, inferred);
    }

    // need to update the inferred invariants to include the stronger assumption - safe update via
    // previous check
    // TODO if we add refinement even when assumptions don't imply inferred condition, we should
    // tweak something here
    Map<Location, Invariant> original = copyInferred(inferred);
    enteringNetwork.forEach(
        e -> {
          if (assumptions.containsKey(e)) {
            inferred.put(e, assumptions.get(e));
          }
        });

    Map<Location, Invariant> finalized = strengtheningLoop();
    finalized.forEach(
        (loc, inv) -> {
          assert inv.implies(inferred.get(loc));
        });
    finalized.forEach(
        (loc, inv) -> {
          if (!inv.implies(original.get(loc))) {
            // based on our algorithm, this should never happen
            throw new BatfishException(
                "Inferred invariant does not imply the weakest condition that was needed @ location "
                    + loc);
          }
        });

    targets.forEach(
        (loc, i) -> {
          assert finalized.containsKey(loc);
        });
    boolean verified =
        assumptions.keySet().stream()
            .allMatch(
                loc ->
                    finalized.containsKey(loc) && assumptions.get(loc).implies(finalized.get(loc)));
    return new Result(verified, original, finalized);
  }
}
