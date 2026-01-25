package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.liveness.Path;
import org.batfish.minesweeper.question.verificationutilities.BDDString;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Lightyear;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import static org.batfish.minesweeper.question.verificationutilities.Invariant.strongestCommonImplicant;

public class Infer {
    public final BDDString.Shortcuts shortcuts;
    private final TransferBDD tbdd;

    private final Map<Ip, Node> nodes = new HashMap<>();
    private final Set<Location> locations = new HashSet<>();
    private final Map<Edge, RoutingPolicy> imports = new HashMap<>();
    private final Map<Edge, RoutingPolicy> exports = new HashMap<>();

    private final Map<Location, Invariant> targets = new HashMap<>();
    private final Map<Location, Invariant> assumptions = new HashMap<>();
    private final Queue<Location> working = new LinkedList<>();
    private final Map<Location, Invariant> inferred = new Hashtable<>();

    public record CounterExample(
            Location location,
            Invariant post,
            Location cause) { }

    public record Result(
            boolean verified,
            Map<Location, Invariant> invariants,
            Optional<CounterExample> counter,
            Map<Location,Optional<Bgpv4Route>> checks) {
        public boolean inferredTrue() {
            if (counter().isEmpty()) {
                return invariants.values().stream().anyMatch(Invariant::isTrue);
            }
            return false;
        }
        public Map<Location,String> strings(Infer infer) {
            Map<Location,String> strings = new HashMap<>();
            invariants.forEach((loc,inv) -> strings.put(loc,inv.toString(false,infer.shortcuts)));
            return strings;
        }
    }

    public Infer(@Nonnull Path.Context context, BDDString.Shortcuts shortcuts, @Nonnull Map<Ip, Node> nodes, @Nonnull Set<Location> locations) {
        this.tbdd = context.tbdd();
        this.shortcuts = shortcuts;
        this.nodes.putAll(nodes);
        this.locations.addAll(locations);
        this.imports.putAll(context.imports());
        this.exports.putAll(context.exports());
        this.assumptions.putAll(context.assumptions());
    }

    public Lightyear checker() {
        return new Lightyear(this.tbdd,this.nodes,this.imports,this.exports);
    }

    /// Added for pybatfish question development
//    public RoutingPolicy getPolicy(Edge location, boolean getImport) {
//        if (getImport) {
//            return imports.getOrDefault(location,null);
//        } else {
//            return exports.getOrDefault(location,null);
//        }
//    }

    /**
     * Add a property to be verified at provided location. If provided a node, this will add the node
     * that we've created which includes all IP addresses that may be associated with it.
     * @param loc location for invariant to hold at
     * @param inv invariant to hold
     * @return updated Verified object
     */
    public Infer addProperty(Location loc, Invariant inv) {
        if (loc instanceof Edge edge) {
            // we only need to check source because if the source is outside the network we cannot verify anything
            if (!nodes.containsKey(edge.getSrc())) {
                throw new BatfishException("Infer.addProperty() - Edge's source node is not within network.");
            } else {
                targets.put(loc,inv);
            }
        } else if (loc instanceof Node node) {
            Optional<Ip> ipWithNode = node.getIps().stream().filter(nodes::containsKey).findFirst();
            if (ipWithNode.isEmpty()) {
                throw new BatfishException("Infer.addProperty() - Node provided not within network.");
            } else {
                targets.put(nodes.get(ipWithNode.get()),inv);
            }
        } else {
            throw new BatfishException("Infer.addProperty() - Location neither edge nor node, should not be reachable.");
        }
        return this;
    }

    /// Initializes all invariants to true except for setting the targets
    private void initializeInvariants() {
        for (Location location : locations) {
            // add the default invariants to the inferred, and the target property
            if (this.targets.containsKey(location)) {
                inferred.put(location, this.targets.get(location).copy());
            } else {
                inferred.put(location,new Invariant(this.tbdd));
            }
        }
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
            Invariant property = inferred.get(location);
            assert !property.isFalse();
            if (location instanceof Edge edge && nodes.containsKey(edge.getSrc())) {
                RoutingPolicy exportPolicy = exports.getOrDefault(edge, null);
                if (exportPolicy == null)
                    throw new BatfishException("Infer.inferenceLoop() - No export policy for: " + edge);
                Node src = nodes.get(edge.getSrc());
                Invariant existing = inferred.get(src);
                Invariant wp = property.weakestPrecondition(exportPolicy);
                Invariant updated = strongestCommonImplicant(existing,wp);
                inferred.put(src,updated);
                if (updated.isFalse()) {
                    return Optional.of(new CounterExample(src.copy(),property.copy(),location.copy()));
                } else if (!existing.equals(updated) && !working.contains(src)) {
                    working.add(src);
                }
            } else if (location instanceof Node node) {
                for (Location l : locations) {
                    if (l instanceof Edge edge && edge.isDst(node)) {
                        RoutingPolicy importPolicy = imports.getOrDefault(edge, null);
                        if (importPolicy == null)
                            throw new BatfishException("Infer.inferenceLoop() - No import policy for: " + edge);
                        Invariant existing = inferred.get(edge);
                        Invariant wp = property.weakestPrecondition(importPolicy);
                        Invariant updated = strongestCommonImplicant(existing,wp);
                        inferred.put(edge,updated);
                        if (updated.isFalse()) {
                            return Optional.of(new CounterExample(edge.copy(),property.copy(),location.copy()));
                        } else if (!existing.equals(updated) && !working.contains(edge)) {
                            working.add(edge);
                        }
                    }
                }
            }
        }
        return Optional.empty(); // success - no counterexample
    }

    /// Checks if verification succeed by checking assumptions.
    /// If it fails, we find a route example which (in dev)
    private Map<Location,Optional<Bgpv4Route>> verificationAssumptionCheck() {
        Map<Location,Optional<Bgpv4Route>> checks = new HashMap<>();
        for (Location location : assumptions.keySet()) {
            Invariant assumption = assumptions.get(location);
            Invariant infer = inferred.getOrDefault(location,Invariant.getFalse(tbdd));
            if (assumption.implies(infer)) {
                checks.put(location,Optional.empty());
            } else {
                BDD constraint = assumption.wellFormedBDD().and(infer.negate().wellFormedBDD());
                assert !constraint.isZero();
                BDD model = ModelGeneration.constraintsToModel(constraint, tbdd.getConfigAtomicPredicates());
                Bgpv4Route counter = ModelGeneration.satAssignmentToBgpInputRoute(model, tbdd.getConfigAtomicPredicates());
                checks.put(location,Optional.of(counter));
            }
        }
        return checks;
    }

    /**
     * Based on configured values, runs verification by inferring invariants in order
     * to verify whatever target properties and locations are provided.
     * @return Result indicating if verification succeeded, what the inferred invariants are and a counterexample
     * if applicable
     */
    public Result run() {
        inferred.clear();
        working.clear();
        initializeInvariants();
        working.addAll(targets.keySet());
        Optional<CounterExample> counter = inferenceLoop();
        Map<Location,Optional<Bgpv4Route>> checks = verificationAssumptionCheck();
        return new Result(counter.isEmpty() && checks.values().stream().allMatch(Optional::isEmpty),copyInferred(inferred),counter,checks);
    }

    /// Returns a refiner object which is used to refine invariants in order to tease out key properties
    public Refine refiner() {
        return Refine.builder(this.tbdd)
                .setNodes(this.nodes)
                .setLocations(this.locations)
                .setImports(this.imports)
                .setExports(this.exports)
                .setTargets(copyInferred(this.targets))
                .setAssumptions(copyInferred(this.assumptions))
                .setIncoming(inferred.keySet().stream()
                        .filter(x -> x instanceof Edge e && !nodes.containsKey(e.getSrc())).collect(Collectors.toSet()))
                .setInferred(copyInferred(this.inferred)).build();
    }

    /// Deep copies invariants inferred
    private Map<Location, Invariant> copyInferred(Map<Location, Invariant> base) {
        Map<Location, Invariant> result = new HashMap<>();
        for (Location location : base.keySet()) {
            result.put(location.copy(),base.get(location).copy());
        }
        return result;
    }
}
