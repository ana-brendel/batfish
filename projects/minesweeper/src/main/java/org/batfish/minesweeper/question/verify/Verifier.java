package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import net.sf.javabdd.BDD;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.AsPath;
import org.batfish.datamodel.AsSet;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.questions.BgpRoute;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.utils.RouteMapEnvironment;
import org.batfish.question.testroutepolicies.Result;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import static java.util.Objects.isNull;
import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.searchroutepolicies.SearchRoutePoliciesAnswerer.simulatePolicy;
import static org.batfish.minesweeper.question.verify.Invariant.conditionsForConstraint;
import static org.batfish.minesweeper.question.verify.Invariant.strongestCommonImplicant;
import static org.batfish.minesweeper.question.verify.Invariant.policyPostConditions;
import static org.batfish.minesweeper.question.verify.Invariant.weakestCommonResult;

public class Verifier {
    private final TransferBDD tbdd;
    private final Map<Ip,Node> nodes = new HashMap<>();
    private final Set<Location> locations = new HashSet<>();
    private final Map<Edge, RoutingPolicy> imports = new HashMap<>();
    private final Map<Edge, RoutingPolicy> exports = new HashMap<>();

    private final Map<Location, Invariant> strongestPostCondition = new HashMap<>();

    private final Map<Location, Invariant> targets = new HashMap<>();
    private final Set<Location> anchors = new HashSet<>();
    private final Queue<Location> working = new LinkedList<>();
    private final Map<Location, Invariant> inferred = new Hashtable<>();

    public TransferBDD getTBDD() { return new TransferBDD(tbdd.getConfigAtomicPredicates()); }
    public Map<Edge, RoutingPolicy> getImports() { return new HashMap<>(imports); }
    public Map<Edge, RoutingPolicy> getExports() { return new HashMap<>(exports); }
    public Set<Location> getLocations() { return new HashSet<>(locations); }
    public Map<Ip,Node> getNodes() { return new HashMap<>(nodes); }

    public record CounterExample(Location location, Invariant post, BgpRoute example) { }
    public record VerificationResult(boolean verified, Map<Location, Invariant> invariants, Optional<CounterExample> counter) {
        public boolean inferredTrue() {
            if (verified) {
                return invariants.values().stream().anyMatch(Invariant::isTrue);
            }
            return false;
        }

        public Collection<Location> inferredTrueAt() {
            if (verified) {
                return invariants.entrySet().stream().filter(entry -> entry.getValue().isTrue())
                        .map(Map.Entry::getKey).collect(Collectors.toSet());
            }
            return ImmutableList.of();
        }

        public boolean targetsImpliedByInferred(Collection<Invariant> targets) {
            for (Invariant inv : invariants.values()) {
                for (Invariant target : targets) {
                    if (!target.impliedBy(inv)) {
                        return false;
                    }
                }
            }
            return true;
        }

        public List<String> dirtyReadableResults(List<String> prefixesConsidered) {
            ImmutableList.Builder<String> builder = ImmutableList.builder();
            for (Map.Entry<Location,Invariant> entry : invariants.entrySet()) {
                String loc = entry.getKey().toString();
                String inv = String.join(" or ",entry.getValue().dirtyReadability(prefixesConsidered));
                builder.add(loc + " : " + inv);
            }
            return builder.build().stream().sorted().toList();
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
                    .forEach(entry -> {
                        locations.add(new Edge(entry.getKey(), nodeIp));
                        locations.add(new Edge(nodeIp,entry.getKey()));
                    });
        }
    }

    public Verifier(TransferBDD tbdd, Map<String, Configuration> configs) {
        this.tbdd = tbdd;
        processConfigs(configs);
    }

    public Collection<Invariant> getTargets() {
        return targets.values().stream().map(Invariant::copy).collect(Collectors.toSet());
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

    private void initializeTrueInvariants() {
        for (Location location : locations) {
            // add the default invariants to the inferred, and the target property
            if (this.targets.containsKey(location)) {
                inferred.put(location, this.targets.get(location).copy());
            } else if (location instanceof Edge edge) {
                if (nodes.containsKey(edge.getDst())) // only inferring incoming
                    inferred.put(location,new Invariant(this.tbdd));
            } else {
                inferred.put(location,new Invariant(this.tbdd));
            }
        }
        for (Location location : targets.keySet()) {
            // outgoing edge of network
            if (!inferred.containsKey(location)) {
                assert location instanceof Edge; // assert edge
                assert nodes.containsKey(((Edge) location).getSrc()); // assert outgoing
                inferred.put(location,targets.get(location));
            }
        }
    }

    // initializes all invariants to false besides anchors
    private void initializeFalseInvariants(Location anchor) {
        inferred.clear();
        for (Location location : locations) {
            if (location.equals(anchor)) {
                inferred.put(location,new Invariant(this.tbdd));
            } else if (location instanceof Edge edge) {
                if (nodes.containsKey(edge.getSrc())) // only inferring outgoing
                    inferred.put(location,new Invariant(this.tbdd,this.tbdd.getFactory().zero()));
            } else {
                inferred.put(location,new Invariant(this.tbdd,this.tbdd.getFactory().zero()));
            }
        }
        if (!inferred.containsKey(anchor)) {
            assert anchor instanceof Edge; // assert edge
            assert nodes.containsKey(((Edge) anchor).getDst()); // assert incoming
            inferred.put(anchor,new Invariant(this.tbdd));
        }
    }

    private boolean sourceInNetwork(Edge edge) {
        Ip srcIp = edge.getSrc();
        return nodes.containsKey(srcIp);
    }

    private boolean destinationInNetwork(Edge edge) {
        Ip dstIp = edge.getDst();
        return nodes.containsKey(dstIp);
    }

    private Optional<Result<BgpRoute, BgpRoute>> constraintsToResult(
            BDD constraints, RoutingPolicy policy,
            Environment.Direction direction, ConfigAtomicPredicates configAPs,
            BDDRoute outputRoute) {
        if (constraints.isZero()) {
            return Optional.empty();
        } else {
            BDD model = ModelGeneration.constraintsToModel(constraints, configAPs);

            Bgpv4Route inRoute = ModelGeneration.satAssignmentToBgpInputRoute(model, configAPs);
            RouteMapEnvironment env = ModelGeneration.satAssignmentToEnvironment(model, configAPs);

            List<AsSet> asSets = inRoute.getAsPath().getAsSets();
            AsPath newAspath = AsPath.ofAsSets(asSets.subList(outputRoute.getPrependedASes().size(), asSets.size()).toArray(new AsSet[0]));
            inRoute = inRoute.toBuilder().setAsPath(newAspath).build();

            Result<BgpRoute, BgpRoute> result = simulatePolicy(policy, inRoute, direction, env, outputRoute);

            // As a sanity check, compare the simulated result above with what the symbolic route
            // analysis predicts will happen.
            assert ModelGeneration.validateModel(model, outputRoute, configAPs, PERMIT, direction, result);

            return Optional.of(result);
        }
    }

    // TODO - need to figure out how to check default... does no policy/statements mean default permit or default deny
    //  right now in the weakest precondition function, we assume no policy/statements is auto permit
    private Optional<BgpRoute> getCounterExamplePreTrue(Environment.Direction dir, Invariant post, RoutingPolicy policy) {
        TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
        List<TransferReturn> paths;
        try {
            paths = tbdd.computePaths(policy.getStatements(),context,true);
        } catch (Exception e) {
            String name = policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
            throw new BatfishException("Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
        }
        for (TransferReturn path : paths) {
            BDD pathAnnouncements = path.getInputConstraints();
            if (path.getAccepted()) { // path is permitted, only get the input conditions that satisfy invariant
                BDDRoute route = path.getOutputRoute();
                BDD constraintsMatchingOutput = conditionsForConstraint(tbdd, post.getBDD(), false,route);
                BDD diff = pathAnnouncements.diff(constraintsMatchingOutput);
                BDD wf = route.wellFormednessConstraints(true).and(diff);
                Optional<Result<BgpRoute, BgpRoute>> result = constraintsToResult(wf, policy, dir,
                        new ConfigAtomicPredicates(tbdd.getConfigAtomicPredicates()), route);
                if (result.isPresent()) {
                    Result<BgpRoute, BgpRoute> r = result.get();
                    BgpRoute counter = r.getOutputRoute();
                    assert counter != null;
                    return Optional.of(counter);
                }
            }
        }
        return Optional.empty();
    }

    private Optional<CounterExample> inferenceLoop() {
        while (!working.isEmpty()) {
            Location location = working.remove();
            Invariant property = inferred.get(location);
            assert !property.isFalse(); // once false is  inferred, it is returned as counter (not added to queue)
            if (location instanceof Edge && sourceInNetwork(((Edge) location))) {
                RoutingPolicy exportPolicy = exports.getOrDefault(location, null);
                assert exportPolicy != null;
                Node src = nodes.get(((Edge) location).getSrc());
                Invariant existing = inferred.get(src);
                Invariant wp = property.weakestPrecondition(exportPolicy);
                Invariant updated = strongestCommonImplicant(existing,wp);
                inferred.put(src,updated);
                if (!existing.equals(updated) && !working.contains(src)) {
                    working.add(src);
                }
                 if (inferred.get(src).isFalse()) {
                     // TODO if cannot infer non-false invariant, what is counterexample
                     return Optional.of(new CounterExample(location.copy(),property.copy(),null));
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
                        if (!existing.equals(updated) && !working.contains(edge)) {
                            working.add(edge);
                        }
                        if (inferred.get(edge).isFalse()) {
                            // TODO if cannot infer non-false invariant, what is counterexample
                            return Optional.of(new CounterExample(location.copy(),property.copy(),null));
                        }
                    }
                }
            }
        }
        return Optional.empty(); // success - no counterexample
    }

    private Optional<CounterExample> strengthenLoop() {
        while (!working.isEmpty()) {
            Location location = working.remove();
            Invariant property = inferred.get(location);
            assert !property.isFalse(); // initially all but anchor are false, so only added when not false
            if (location instanceof Edge && destinationInNetwork(((Edge) location))) {
                RoutingPolicy importPolicy = imports.getOrDefault(location, null);
                assert importPolicy != null;
                Node dst = nodes.get(((Edge) location).getDst());
                Invariant existing = inferred.get(dst);
                Invariant wp = property.strongestPostcondition(importPolicy);
                Invariant updated = weakestCommonResult(existing,wp);
                inferred.put(dst,updated);
                if (!existing.equals(updated)) {
                    working.add(dst);
                }
            } else if (location instanceof Node node) {
                Ip src = node.getIp();
                for (Location edge : locations) {
                    if (edge instanceof Edge && ((Edge) edge).getSrc().equals(src)) {
                        RoutingPolicy exportPolicy = exports.getOrDefault(edge, null);
                        assert exportPolicy != null;
                        Invariant existing = inferred.get(edge);
                        Invariant wp = property.strongestPostcondition(exportPolicy);
                        Invariant updated = weakestCommonResult(existing,wp);
                        inferred.put(edge,updated);
                        if (!existing.equals(updated)) {
                            working.add(edge);
                        }
                    }
                }
            }
        }
        return Optional.empty();
    }

    private void setUpStrongestPosts() {
        for (Location location : locations) {
            if (location instanceof Edge fromExport) {
                Node fromImport = nodes.get(fromExport.getDst());
                strongestPostCondition.put(fromExport, policyPostConditions(tbdd,exports.get(fromExport)));
                if (!strongestPostCondition.containsKey(fromImport)) {
                    strongestPostCondition.put(fromImport, policyPostConditions(tbdd,imports.get(fromExport)));
                } else {
                    Invariant current = strongestPostCondition.get(fromImport);
                    Invariant strongest = policyPostConditions(tbdd,imports.get(fromExport));
                    strongestPostCondition.put(fromImport,current.disjoin(strongest));
                }
            }
        }
    }

    /**
     * Based on configured values, runs verification by inferring invariants in order
     * to verify whatever target properties and locations are provided.
     * @return Result indicating if verification succeeded, what the inferred invariants are and a counterexample
     * if applicable
     */
    public VerificationResult run() {
        initializeTrueInvariants();
        working.clear();
        working.addAll(targets.keySet());
        Optional<CounterExample> counter = inferenceLoop();
        return new VerificationResult(counter.isEmpty(),copyInferred(inferred),counter);
    }

    /// Currently buggy! -- This function doesn't work and is in development.
    public VerificationResult runForwards(Location anchor) {
        initializeFalseInvariants(anchor);
        working.clear();
        working.add(anchor);
        Optional<CounterExample> counter = strengthenLoop();
        boolean verified = true;
//        for (Location target : targets.keySet()) {
//            Invariant inv = targets.get(target);
//            verified = verified && inv.impliedBy(inferred.get(target));
//        }
        return new VerificationResult(verified,copyInferred(inferred),null);
    }

    /// Currently buggy! -- This function doesn't work and is in development.
    public Optional<Location> bugLocator(Location anchor, VerificationResult verification) {
        if (!verification.inferredTrue()) {
            Map<Location, Invariant> v_inferred = verification.invariants();
            // propagated stores the properties of the routes which reach this location AND are contained in inferred invariant
            Map<Location, Invariant> propagated = new HashMap<>();
            v_inferred.keySet().forEach(loc -> propagated.put(loc.copy(), null));
            assert propagated.containsKey(anchor);
            propagated.put(anchor, new Invariant(tbdd));
            Queue<Location> destination = new LinkedList<>(); // might want to consider a priority queue moving closer to target
            destination.add(anchor.copy());

            while (!destination.isEmpty()) {
                Location check = destination.remove();
                Invariant live = propagated.get(check);
                if (check instanceof Edge && destinationInNetwork(((Edge) check))) {
                    Node dst = nodes.get(((Edge) check).getDst());
                    RoutingPolicy importPolicy = imports.getOrDefault(check, null);
                    assert importPolicy != null;
                    Invariant post = live.strongestPostcondition(importPolicy);
                    Invariant dstInferred = v_inferred.get(dst);
                    if (post.implies(dstInferred)) {
                        return Optional.of(dst.copy());
                    } else {
                        //Invariant contained = new Invariant(tbdd, post.getBDD().and(dstInferred.getBDD()));
                        Invariant update = new Invariant(tbdd, post.getBDD());
                        Invariant original = propagated.get(dst);
                        // disjoin with any existing paths that went through here
                        if (original != null) update = new Invariant(tbdd, post.getBDD().or(original.getBDD()));
                        propagated.put(dst, update);
                        if (!update.equals(original)) {
                            destination.add(dst);
                        }
                    }
                } else if (check instanceof Node) {
                    Ip src = ((Node) check).getIp();
                    for (Location edge : locations) {
                        if (edge instanceof Edge && ((Edge) edge).getSrc().equals(src)) {
                            RoutingPolicy exportPolicy = exports.getOrDefault(edge, null);
                            assert exportPolicy != null;
                            Invariant post = live.strongestPostcondition(exportPolicy);
                            Invariant edgeInferred = v_inferred.get(edge);
                            if (post.implies(edgeInferred)) {
                                return Optional.of(check.copy());
                            } else {
                                //Invariant contained = new Invariant(tbdd, post.getBDD().and(edgeInferred.getBDD()));
                                Invariant update = new Invariant(tbdd, post.getBDD());
                                Invariant original = propagated.get(edge);
                                // disjoin with any existing paths that went through here
                                if (original != null) update = new Invariant(tbdd, post.getBDD().or(original.getBDD()));
                                propagated.put(edge, update);
                                if (!update.equals(original)) {
                                    destination.add(edge);
                                }
                            }
                        }
                    }
                }
            }
        }
        return Optional.empty();
    }

    private Map<Location, Invariant> copyInferred(Map<Location, Invariant> map) {
        Map<Location, Invariant> result = new HashMap<>();
        for (Location location : map.keySet()) {
            result.put(location.copy(),map.get(location).copy());
        }
        return result;
    }
}
