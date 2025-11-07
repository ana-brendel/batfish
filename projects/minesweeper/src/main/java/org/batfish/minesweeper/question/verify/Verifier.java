package org.batfish.minesweeper.question.verify;

import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.TransferBDD;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;

import static java.util.Objects.isNull;
import static org.batfish.minesweeper.question.verify.Invariant.strongestCommonImplicant;

public class Verifier {
    private final TransferBDD tbdd;
    private final Map<Ip,Node> nodes = new HashMap<>();
    private final Set<Location> locations = new HashSet<>();
    private final Map<Edge, RoutingPolicy> imports = new HashMap<>();
    private final Map<Edge, RoutingPolicy> exports = new HashMap<>();

    private final Map<Location, Invariant> targets = new HashMap<>();
    private final Set<Location> anchors = new HashSet<>();
    private final Queue<Location> working = new LinkedList<>();
    private final Map<Location, Invariant> inferred = new Hashtable<>();

    public record CounterExample(Location location, Invariant post) { }
    public record Result(boolean verified, Map<Location, Invariant> invariants, Optional<CounterExample> counter) {
        public boolean inferredTrue() {
            if (verified) {
                return invariants.values().stream().anyMatch(Invariant::isTrue);
            }
            return false;
        }
    }

    private void processConfigs(Map<String, Configuration> configs) {
        for (String nodeName : configs.keySet()) {
            Configuration config = configs.get(nodeName);
            List<BgpProcess> bgpProcesses = config.getVrfs().values().stream().map(Vrf::getBgpProcess).toList();
            Ip nodeIp = bgpProcesses.stream().findFirst().orElseThrow().getRouterId();
            locations.add(new Node(nodeIp,nodeName)); // add node
            nodes.put(nodeIp,new Node(nodeIp,nodeName));
            // gather the policies
            bgpProcesses.stream().flatMap(proc -> proc.getActiveNeighbors().entrySet().stream())
                    .forEach(entry -> {
                        Edge incoming = new Edge(entry.getKey(),nodeIp);
                        Edge outgoing = new Edge(nodeIp,entry.getKey());
                        Ipv4UnicastAddressFamily unicast = (entry.getValue().getIpv4UnicastAddressFamily());
                        imports.put(incoming,isNull(unicast) || isNull(unicast.getImportPolicy())
                                ? new RoutingPolicy("from null",config)
                                : config.getRoutingPolicies().get(unicast.getImportPolicy()));
                        exports.put(outgoing,isNull(unicast) || isNull(unicast.getExportPolicy())
                                ? new RoutingPolicy("from null",config)
                                : config.getRoutingPolicies().get(unicast.getExportPolicy()));
                    });
            // add the edges
            bgpProcesses.stream().flatMap(proc -> proc.getActiveNeighbors().entrySet().stream())
                    .forEach(entry -> locations.add(new Edge(entry.getKey(),nodeIp)));
        }
    }

    public Verifier(TransferBDD tbdd, Map<String, Configuration> configs) {
        this.tbdd = tbdd;
        processConfigs(configs);
    }

    /**
     * Add a location which should allow for any route
     * @param anchor location where invariant should be true
     * @return updated Verified object
     */
    public Verifier addAnchor(Location anchor) {
        anchors.add(anchor);
        return this;
    }

    /**
     * Add a property to be verified at provided location
     * @param loc location for invariant to hold at
     * @param inv invariant to hold
     * @return updated Verified object
     */
    public Verifier addProperty(Location loc, Invariant inv) {
        targets.put(loc,inv);
        return this;
    }

    private void initializeInvariants() {
        for (Location location : locations) {
            // add the default invariants to the inferred, and the target property
            if (this.targets.containsKey(location)) {
                inferred.put(location, this.targets.get(location).copy());
            } else {
                inferred.put(location,new Invariant(this.tbdd));
            }
        }
    }

    private boolean sourceInNetwork(Edge edge) {
        Ip srcIp = edge.getSrc();
        return nodes.containsKey(srcIp);
    }

    private Optional<CounterExample> inferenceLoop() {
        while (!working.isEmpty()) {
            Location location = working.remove();
            Invariant property = inferred.get(location);
            if (property.isFalse()) {
                // need to figure out formatting
                return Optional.of(new CounterExample(location.copy(),property.copy()));
            } else if (location instanceof Edge && sourceInNetwork(((Edge) location))) {
                RoutingPolicy exportPolicy = exports.getOrDefault(location, null);
                assert exportPolicy != null;
                Node src = nodes.get(((Edge) location).getSrc());
                Invariant existing = inferred.get(src);
                Invariant wp = property.weakestPrecondition(exportPolicy);
                Invariant updated = strongestCommonImplicant(existing,wp);
                inferred.put(src,updated);
                if (!existing.equals(updated)) {
                    working.add(src);
                }
                if (anchors.contains(src) && !inferred.get(src).isTrue()) {
                    // builder.put(COUNTEREXAMPLE, getCounterExamplePreTrue(OUT,property, exportPolicy));
                    // TODO figure out how to return invariant description
                    return Optional.of(new CounterExample(location.copy(),property.copy()));
                }
            } else if (location instanceof Node) {
                Ip dst = ((Node) location).getIp();
                for (Location edge : locations) {
                    if (edge instanceof Edge && ((Edge) edge).getDst().equals(dst)) {
                        RoutingPolicy importPolicy = imports.getOrDefault(edge, null);
                        assert importPolicy != null;
                        Invariant existing = inferred.get(edge);
                        Invariant wp = property.weakestPrecondition(importPolicy);
                        Invariant updated = strongestCommonImplicant(existing,wp);
                        inferred.put(edge,updated);
                        if (!existing.equals(updated)) {
                            working.add(edge);
                        }
                        if (anchors.contains(edge) && !inferred.get(edge).isTrue()) {
                            // builder.put(COUNTEREXAMPLE, getCounterExamplePreTrue(IN,property, importPolicy));
                            // TODO figure out how to return invariant description
                            return Optional.of(new CounterExample(location.copy(),property.copy()));
                        }
                    }
                }
            }
        }
        return Optional.empty(); // success - no counterexample
    }

    /**
     * Based on configured values, runs verification by inferring invariants in order
     * to verify whatever target properties and locations are provided.
     * @return Result indicating if verification succeeded, what the inferred invariants are and a counterexample
     * if applicable
     */
    public Result run() {
        initializeInvariants();
        working.addAll(targets.keySet());
        Optional<CounterExample> counter = inferenceLoop();
        return new Result(counter.isEmpty(),copyInferred(),counter);
    }

    private Map<Location, Invariant> copyInferred() {
        Map<Location, Invariant> result = new HashMap<>();
        for (Location location : inferred.keySet()) {
            result.put(location.copy(),inferred.get(location).copy());
        }
        return result;
    }
}
