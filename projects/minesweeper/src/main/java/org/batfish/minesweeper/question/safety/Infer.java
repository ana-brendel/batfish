package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.liveness.Path;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Lightyear;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static org.batfish.minesweeper.question.verificationutilities.Invariant.strongestCommonImplicant;

public class Infer {
  private static final Logger LOGGER = LogManager.getLogger(Infer.class);
  private final TransferBDD tbdd;

  private final Map<Ip, Node> nodes = new HashMap<>();
  // for better runtime, should switch locations to a neighbors map
  private final Map<Node, Set<Edge>> edgesByDestination = new HashMap<>();
  private final Map<Edge, RoutingPolicy> imports = new HashMap<>();
  private final Map<Edge, RoutingPolicy> exports = new HashMap<>();

  private final Map<Location, Invariant> targets = new HashMap<>();
  private final Map<Location, Invariant> assumptions = new HashMap<>();
  private final Queue<Location> working = new LinkedList<>();
  private final Map<Location, Invariant> inferred = new HashMap<>();

  /// Inference counterexample, used for when we infer false within the network
  public record CounterExample(Location location, Invariant post, Location cause) {}

  /// Stores useful results collected during invariant inference
  public static class Result {
    public final boolean verified;
    public final Map<Location, Invariant> invariants;
    public final Optional<CounterExample> counter;
    public final Map<Location, Optional<Bgpv4Route>> checks;
    public final Map<BDD, String> cache = new HashMap<>();

    public Result(
        boolean verified,
        Map<Location, Invariant> invariants,
        Optional<CounterExample> counter,
        Map<Location, Optional<Bgpv4Route>> checks) {
      this.verified = verified;
      this.invariants = invariants;
      this.counter = counter;
      this.checks = checks;
    }

    public boolean inferredTrue() {
      if (counter.isEmpty()) {
        return invariants.values().stream().anyMatch(Invariant::isTrue);
      }
      return false;
    }

    public Map<Location, String> strings() {
      Map<Location, String> strings = new HashMap<>();
      invariants.forEach((loc, inv) -> strings.put(loc, inv.toString(false, this.cache)));
      return strings;
    }
  }

  public Infer(
      @Nonnull Path.Context context,
      @Nonnull Map<Ip, Node> nodes,
      @Nonnull Map<Node, Set<Edge>> edgesByDestination) {
    this.tbdd = context.tbdd();
    this.nodes.putAll(nodes);
    this.edgesByDestination.putAll(edgesByDestination);
    this.imports.putAll(context.imports());
    this.exports.putAll(context.exports());
    this.assumptions.putAll(context.assumptions());
  }

  /**
   * Add a property to be verified at provided location. If provided a node, this will add the node
   * that we've created which includes all IP addresses that may be associated with it.
   *
   * @param loc location for invariant to hold at
   * @param inv invariant to hold
   * @return updated Verified object
   */
  public Infer addProperty(Location loc, Invariant inv) {
    checkArgument(
        loc instanceof Edge || loc instanceof Node,
        "Only implementations of Location that should be provided are nodes or edges.");

    if (loc instanceof Edge edge) {
      // we only need to check source because if the source is outside the network we cannot verify
      // anything
      if (!nodes.containsKey(edge.getSrc())) {
        throw new BatfishException(
            "Infer.addProperty() - Edge's source node is not within network. We cannot verify properties originating from outside our network.");
      } else {
        targets.put(loc, inv);
      }
    } else {
      Node node = (Node) loc;
      Optional<Ip> ipWithNode = node.getIps().stream().filter(nodes::containsKey).findFirst();
      if (ipWithNode.isEmpty()) {
        throw new BatfishException(
            "Infer.addProperty() - Node provided not within network. We cannot verify a property on a node that is not within our network.");
      } else {
        targets.put(nodes.get(ipWithNode.get()), inv);
      }
    }
    return this;
  }

  /// Initializes all target invariants
  private void initializeInvariants() {
    for (Location location : targets.keySet()) {
      if (!inferred.containsKey(location)) {
        inferred.put(location, this.targets.get(location).copy());
      }
    }
  }

  /// Performs iterative invariant inference using the weakest preconditions
  private Optional<CounterExample> inferenceLoop() {
    while (!working.isEmpty()) {
      Location location = working.remove();
      assert inferred.containsKey(location)
          : "Trying to get existing invariant for unvisited location: " + location;
      Invariant property = inferred.get(location);
      LOGGER.info("Working to weakest precondition for property to hold at: {}", location);
      assert !property.isFalse();
      if (location instanceof Edge edge && nodes.containsKey(edge.getSrc())) {
        RoutingPolicy exportPolicy = exports.get(edge);
        Invariant wp =
            exportPolicy == null ? property.copy() : property.weakestPrecondition(exportPolicy);
        Node src = nodes.get(edge.getSrc());
        boolean firstVisit = !inferred.containsKey(src);
        Invariant existing = inferred.getOrDefault(src, new Invariant(tbdd));
        Invariant updated = strongestCommonImplicant(existing, wp);
        inferred.put(src, updated);
        if (updated.isFalse()) {
          return Optional.of(new CounterExample(src.copy(), property.copy(), location.copy()));
        } else if ((firstVisit || !existing.equals(updated)) && !working.contains(src)) {
          working.add(src);
        }
      } else if (location instanceof Node node) {
        for (Location l : edgesByDestination.get(node)) {
          if (l instanceof Edge edge && edge.isDst(node)) {
            RoutingPolicy importPolicy = imports.get(edge);
            Invariant wp =
                importPolicy == null ? property.copy() : property.weakestPrecondition(importPolicy);
            boolean firstVisit = !inferred.containsKey(edge);
            Invariant existing = inferred.getOrDefault(edge, new Invariant(tbdd));
            Invariant updated = strongestCommonImplicant(existing, wp);
            inferred.put(edge, updated);
            if (updated.isFalse()) {
              return Optional.of(new CounterExample(edge.copy(), property.copy(), location.copy()));
            } else if ((firstVisit || !existing.equals(updated)) && !working.contains(edge)) {
              working.add(edge);
            }
          }
        }
      }
    }
    return Optional.empty(); // success - no counterexample
  }

  /// Checks if verification succeed by checking assumptions.
  /// If it fails (i.e. the assumption does not imply the needed invariant), we find a route example
  // which is
  /// a counterexample that adheres to the assumption but does not satisfy the invariant
  private Map<Location, Optional<Bgpv4Route>> verificationAssumptionCheck() {
    Map<Location, Optional<Bgpv4Route>> checks = new HashMap<>();
    for (Location location : assumptions.keySet()) {
      Invariant assumption = assumptions.get(location);
      Invariant infer = inferred.getOrDefault(location, Invariant.getFalse(tbdd));
      if (assumption.implies(infer)) {
        checks.put(location, Optional.empty());
      } else {
        BDD constraint =
            assumption
                .getBDD()
                .andWith(infer.getBDD().not())
                .andWith(tbdd.getOriginalRoute().wellFormednessConstraints(true));
        assert !constraint.isZero();
        BDD model =
            ModelGeneration.constraintsToModel(constraint, tbdd.getConfigAtomicPredicates());
        Bgpv4Route counter =
            ModelGeneration.satAssignmentToBgpInputRoute(model, tbdd.getConfigAtomicPredicates());
        checks.put(location, Optional.of(counter));
      }
    }
    return checks;
  }

  /**
   * Based on configured values, runs verification by inferring invariants in order to verify
   * whatever target properties and locations are provided.
   *
   * @return Result indicating if verification succeeded, what the inferred invariants are and a
   *     counterexample if applicable
   */
  public Result run() {
    inferred.clear();
    working.clear();
    LOGGER.info("Initializing invariants for inference.");
    initializeInvariants();
    working.addAll(targets.keySet());
    LOGGER.info("Beginning initial inference of safety invariants.");
    Optional<CounterExample> counter = inferenceLoop();
    LOGGER.info("Inference loop terminated.");
    Map<Location, Optional<Bgpv4Route>> checks = verificationAssumptionCheck();

    // Lightyear style check to only run during testing
    assert counter.isPresent()
            || (new Lightyear(this.nodes, this.imports, this.exports)).check(inferred).isEmpty()
        : "Checks that all invariants are sufficient as preconditions to imply the following postcondition";

    return new Result(
        counter.isEmpty() && checks.values().stream().allMatch(Optional::isEmpty),
        copyInferred(inferred),
        counter,
        checks);
  }

  /// Returns a Refiner object which is used to refine invariants in order to tease out key
  // properties
  public Refine refiner() {
    return Refine.builder(this.tbdd)
        .setNodes(this.nodes)
        .setImports(this.imports)
        .setExports(this.exports)
        .setTargets(copyInferred(this.targets))
        .setAssumptions(copyInferred(this.assumptions))
        .setIncoming(
            inferred.keySet().stream()
                .filter(x -> x instanceof Edge e && !nodes.containsKey(e.getSrc()))
                .collect(Collectors.toSet()))
        .setInferred(copyInferred(this.inferred))
        .build();
  }

  /// Deep copies invariants inferred
  public static Map<Location, Invariant> copyInferred(Map<Location, Invariant> base) {
    Map<Location, Invariant> result = new HashMap<>();
    for (Location location : base.keySet()) {
      result.put(location.copy(), base.get(location).copy());
    }
    return result;
  }
}
