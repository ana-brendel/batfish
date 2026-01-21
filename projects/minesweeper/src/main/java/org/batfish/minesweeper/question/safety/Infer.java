package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.BDDString;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Lightyear;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.Objects.isNull;
import static java.util.Objects.nonNull;
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
//        public Map<Location,String> weakDisplay(List<String> prefixes) {
//            Map<Location,String> strings = new HashMap<>();
//            invariants.forEach((loc,inv) -> strings.put(loc,inv.weakDisplay(prefixes)));
//            return strings;
//        }
        public Map<Location,String> strings(Infer infer) {
            Map<Location,String> strings = new HashMap<>();
            invariants.forEach((loc,inv) -> strings.put(loc,inv.toString(false,infer.shortcuts)));
            return strings;
        }
    }

    private void processConfigs(@Nonnull Map<String, Configuration> configs) {
        for (String nodeName : configs.keySet()) {
            Configuration config = configs.get(nodeName);
            // no need to evaluate any configs which are null or don't yield anything
            if (isNull(config) || isNull(config.getVrfs())) continue;
            // filter out any null VRFs
            Stream<Vrf> forwarding = config.getVrfs().values().stream().filter(Objects::nonNull);
            // gets the bgp processes and filters out any null processes
            List<BgpProcess> bgpProcesses = forwarding.map(Vrf::getBgpProcess).filter(Objects::nonNull).toList();
            // note, getRouterId's return value is Nonnull
            Set<Ip> nodeIps = bgpProcesses.stream().map(BgpProcess::getRouterId).collect(Collectors.toSet());
            // gather the policies
            bgpProcesses.stream().flatMap(proc -> proc.getActiveNeighbors().entrySet().stream())
                    // make sure any null neighbors are filtered out, and filter out any node without an ip address
                    .filter(entry -> nonNull(entry) && nonNull(entry.getKey()) && nonNull(entry.getValue()) &&
                            (nodeIps.stream().findFirst().isPresent() || nonNull(entry.getValue().getLocalIp())))
                    .forEach(entry -> {
                        // at least one of these will be non-null based on filter, null pointer exception should never be thrown
                        Ip nodeIp = nonNull(entry.getValue().getLocalIp()) ?
                                entry.getValue().getLocalIp() : nodeIps.stream().findFirst().get();
                        nodeIps.add(nodeIp);
                        Edge incoming = new Edge(entry.getKey(),nodeIp);
                        Edge outgoing = new Edge(nodeIp,entry.getKey());
                        Ipv4UnicastAddressFamily unicast = entry.getValue().getIpv4UnicastAddressFamily();
                        imports.put(incoming,isNull(unicast) || isNull(unicast.getImportPolicy())
                                || isNull(config.getRoutingPolicies()) || isNull(config.getRoutingPolicies().get(unicast.getImportPolicy()))
                                ? new RoutingPolicy("from null",config)
                                : config.getRoutingPolicies().get(unicast.getImportPolicy()));
                        exports.put(outgoing,isNull(unicast) || isNull(unicast.getExportPolicy())
                                || isNull(config.getRoutingPolicies()) || isNull(config.getRoutingPolicies().get(unicast.getExportPolicy()))
                                ? new RoutingPolicy("from null",config)
                                : config.getRoutingPolicies().get(unicast.getExportPolicy()));
                        // add anywhere edge is going into this node (i.e. the incoming edge above)
                        locations.add(new Edge(entry.getKey(),nodeIp));
                    });
            Node node = new Node(nodeIps,nodeName);
            locations.add(node); // add node
            nodeIps.forEach(nodeIp -> nodes.put(nodeIp,node));
        }
    }

    public Infer(@Nonnull TransferBDD tbdd, @Nonnull Map<String, Configuration> configs) {
        this.tbdd = tbdd;
        processConfigs(configs);
        shortcuts = BDDString.Shortcuts.ofConfigs(configs.values());
        // default assumption of True for incoming edges
        for (Location location : locations) {
            if (location instanceof Edge edge) {
                // if the edge's source is not in the set of nodes (i.e. out of network)
                if (!nodes.containsKey(edge.getSrc())) {
                    assumptions.put(edge,new Invariant(tbdd));
                }
            }
        }
    }

    public Lightyear checker() {
        return new Lightyear(this.tbdd,this.nodes,this.imports,this.exports);
    }

    /// Added for pybatfish question development
    public TransferBDD getTBDD() {
        return tbdd;
    }

    /// Added for pybatfish question development
    public RoutingPolicy getPolicy(Edge location, boolean getImport) {
        if (getImport) {
            return imports.getOrDefault(location,null);
        } else {
            return exports.getOrDefault(location,null);
        }
    }

    /// Added for pybatfish question development
    public Optional<Collection<Ip>> ipsFromNodeName(String name) {
        for (Location location : locations) {
            if (location instanceof Node node && node.getName().equals(name))
                return Optional.of(node.getIps());
        }
        return Optional.empty();
    }

    /// Added for pybatfish question development
    public boolean containsPolicy(Edge edge) {
        return imports.containsKey(edge) || exports.containsKey(edge);
    }

    /// Added for pybatfish question development
    public Edge getAnyIncomingEdge(Node node) {
        for (Location location : locations) {
            if (location instanceof Edge edge) {
                if (edge.isDst(node)) {
                    return edge.copy();
                }
            }
        }
        return null;
    }

    /// Added for pybatfish question development
    public Map<Location, Invariant> getTargets() { return targets; }

    /// Added for pybatfish question development
    public Map<Location, Invariant> getAssumptions() { return assumptions; }

    /**
     * Add a location which should allow for any route
     * @param anchor location where invariant should be true
     * @return updated Verified object
     */
    public Infer addAnchor(Location anchor) {
        return this.addAssumption(anchor,new Invariant(this.tbdd));
    }

    public Infer addAssumption(@Nonnull Location location, @Nonnull Invariant assumption) {
        assumptions.put(location,assumption);
        return this;
    }

    public void addAssumption(@Nonnull Location.Builder locationBuilder, @Nonnull Invariant.Builder assumption) {
        Location location = locationBuilder.instantiate(this);
        RoutingPolicy policy;
        if (location instanceof Node node) {
            Optional<Edge> incoming = imports.keySet().stream().filter(e -> e.isDst(node)).findFirst();
            if (incoming.isPresent()) {
                policy = imports.get(incoming.get());
            } else {
                Optional<Edge> outgoing = exports.keySet().stream().filter(e -> e.isSrc(node)).findFirst();
                policy = outgoing.map(imports::get).orElse(null);
            }
        } else {
            assert location instanceof Edge;
            policy = exports.getOrDefault(location,imports.getOrDefault(location,null));
        }
        this.addAssumption(location,assumption.build(tbdd,policy));
    }

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

    public String displayNodes() {
        StringBuilder builder = new StringBuilder();
        Set<Node> done = new HashSet<>();
        for (Node n : nodes.values().stream().sorted().toList()) {
            if (!done.contains(n)) {
                done.add(n);
                builder.append("\n + ").append(n);
                for (Location l : locations) {
                    if (l instanceof Edge e && e.isSrc(n)) {
                        builder.append("\n    - ").append(e.getDst());
                    }
                }
            }
        }
        return builder.toString();
    }
}
