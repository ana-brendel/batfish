package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
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
import static org.batfish.minesweeper.question.verificationutilities.NetworkInfo.getRouteExample;

public class Infer {
  private static final Logger LOGGER = LogManager.getLogger(Infer.class);
  private final TransferBDD tbdd;

  private final Map<Ip, Node> nodes = new HashMap<>();
  // for better runtime, should switch locations to a neighbors map
  private final Map<Node, Set<Edge>> edgesByDestination;
  private final Map<Edge, RoutingPolicy> imports;
  private final Map<Edge, RoutingPolicy> exports;

  private final Map<Location, Invariant> targets = new HashMap<>();
  private final Map<Location, Invariant> checkedAssumptions;
  private final Map<Location, Invariant> enforcedAssumptions;
  private final Queue<Location> working = new LinkedList<>();
  private final Map<Location, Invariant> inferred = new HashMap<>();

  /// Inference counterexample, used for when we infer false within the network
  public record CounterExample(Location location, Invariant post, Location cause) {}

  /// Stores useful results collected during invariant inference
  public static class Result {
    public final boolean verified;
    public final Map<Location, Invariant> invariants;
    public final Optional<CounterExample> counter;
    public final Map<Location, Bgpv4Route> checks;
    public final Map<BDD, String> cache = new HashMap<>();

    public Result(
        boolean verified,
        Map<Location, Invariant> invariants,
        Optional<CounterExample> counter,
        Map<Location, Bgpv4Route> checks) {
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
    this.edgesByDestination = edgesByDestination;
    this.imports = context.imports();
    this.exports = context.exports();
    this.checkedAssumptions = context.checkedAssumptions();
    this.enforcedAssumptions = context.enforcedAssumptions();
  }

  public Map<Location, Invariant> getTargets() {
    return this.targets;
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
      // we don't expect the target to be in the inferred map
      assert !inferred.containsKey(location);
      inferred.putIfAbsent(location, this.targets.get(location).copy());
      working.add(location);
    }
    for (Location location : enforcedAssumptions.keySet()) {
      if (location instanceof Edge edge && !nodes.containsKey(edge.getDst())) {
        assert !inferred.containsKey(location);
        inferred.putIfAbsent(location, this.enforcedAssumptions.get(location).copy());
        working.add(location);
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
      assert !property.isFalse();
      if (location instanceof Edge edge && nodes.containsKey(edge.getSrc())) {
        RoutingPolicy exportPolicy = exports.get(edge);
        Invariant wp =
            exportPolicy == null ? property.copy() : property.weakestPrecondition(exportPolicy);
        Node src = nodes.get(edge.getSrc());
        boolean firstVisit = !inferred.containsKey(src);
        // get inferred if present, otherwise get enforced assumption, otherwise default is true
        Invariant existing =
            inferred.getOrDefault(src, enforcedAssumptions.getOrDefault(src, new Invariant(tbdd)));
        Invariant updated = strongestCommonImplicant(existing, wp);
        wp.free();
        inferred.put(src, updated);
        // a node will never be a checked assumption
        if (updated.isFalse()) {
          existing.free();
          return Optional.of(new CounterExample(src, property, location));
        } else if ((firstVisit || !existing.equals(updated)) && !working.contains(src)) {
          existing.free();
          working.add(src);
        }
      } else if (location instanceof Node node) {
        for (Location l : edgesByDestination.get(node)) {
          if (l instanceof Edge edge && edge.isDst(node)) {
            RoutingPolicy importPolicy = imports.get(edge);
            Invariant wp =
                importPolicy == null ? property.copy() : property.weakestPrecondition(importPolicy);
            boolean firstVisit = !inferred.containsKey(edge);
            // get inferred if present, otherwise get enforced assumption, otherwise default is true
            Invariant existing =
                inferred.getOrDefault(
                    edge, enforcedAssumptions.getOrDefault(edge, new Invariant(tbdd)));
            Invariant updated = strongestCommonImplicant(existing, wp);
            wp.free();
            inferred.put(edge, updated);
            // if we inferred false, but the edge is incoming then this isn't necessarily a
            // counterexample - rather a condition which should be checked if it holds
            if (updated.isFalse() && !checkedAssumptions.containsKey(edge)) {
              existing.free();
              return Optional.of(new CounterExample(edge, property, location));
            } else if ((firstVisit || !existing.equals(updated)) && !working.contains(edge)) {
              existing.free();
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
  /// which is a counterexample that adheres to the assumption but does not satisfy the invariant
  private Map<Location, Bgpv4Route> verificationAssumptionCheck() {
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
      }
    }
    return checks;
  }

  /**
   * Based on configured values, runs verification by inferring invariants in order to verify
   * whatever target properties and locations are provided. Included for violation analysis to avoid
   * logging every inference query in the loop.
   *
   * @param log indicates if logging message should be displayed
   * @return Result indicating if verification succeeded, what the inferred invariants are and a
   *     counterexample if applicable
   */
  public Result run(boolean log) {
    inferred.clear();
    working.clear();
    if (log) {
      LOGGER.info("Initializing invariants for inference.");
    }
    initializeInvariants(); // adds to working list
    if (log) {
      LOGGER.info("Beginning initial inference of safety invariants.");
    }
    Optional<CounterExample> counter = inferenceLoop();
    if (log) {
      LOGGER.info("Inference loop terminated.");
    }
    Map<Location, Bgpv4Route> checks = verificationAssumptionCheck();

    // Lightyear style check to only run during testing
    assert counter.isPresent()
            || (new Lightyear(this.nodes, this.imports, this.exports)).check(inferred).isEmpty()
        : "Checks that all invariants are sufficient as preconditions to imply the following postcondition";

    return new Result(counter.isEmpty() && checks.isEmpty(), inferred, counter, checks);
  }

  /**
   * Based on configured values, runs verification by inferring invariants in order to verify
   * whatever target properties and locations are provided.
   *
   * @return Result indicating if verification succeeded, what the inferred invariants are and a
   *     counterexample if applicable
   */
  public Result run() {
    return this.run(true);
  }

  /// Returns a Refiner object which is used to refine invariants in order to tease out key
  // properties
  public Refine refiner() {
    return Refine.builder(this.tbdd)
        .setNodes(this.nodes)
        .setImports(this.imports)
        .setExports(this.exports)
        .setTargets(copyInferred(this.targets))
        .setAssumptions(copyInferred(this.checkedAssumptions))
        .setIncoming(
            inferred.keySet().stream()
                .filter(x -> x instanceof Edge e && !nodes.containsKey(e.getSrc()))
                .collect(Collectors.toSet()))
        .setInferred(copyInferred(this.inferred))
        .build();
  }

  /// Deep copies invariants inferred
  public static Map<Location, Invariant> copyInferred(Map<Location, Invariant> base) {
    return new HashMap<>(base);
  }
}
