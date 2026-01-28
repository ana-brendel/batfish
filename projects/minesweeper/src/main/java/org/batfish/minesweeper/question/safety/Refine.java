package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.BDDString;
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


public class Refine {
    private static final Logger LOGGER = LogManager.getLogger(Refine.class);

    private final TransferBDD tbdd;
    private final Map<Ip, Node> nodes;
    private final Set<Location> locations;
    private final Map<Edge, RoutingPolicy> imports;
    private final Map<Edge, RoutingPolicy> exports;
    private final Set<Edge> enteringNetwork;

    private final Map<Location, Invariant> targets;
    private final Map<Location, Invariant> assumptions;
    private final Map<Location, Invariant> inferred;

    private final Queue<Location> working = new LinkedList<>();

    public static class Builder {
        private final TransferBDD tbdd;
        private Map<Ip,Node> nodes;
        private Set<Location> locations;
        private Map<Edge, RoutingPolicy> imports;
        private Map<Edge, RoutingPolicy> exports;
        private Map<Location, Invariant> targets;
        private Map<Location, Invariant> assumptions;
        private Set<Edge> incoming;
        private Map<Location, Invariant> inferred;

        public Builder(TransferBDD tbdd) { this.tbdd = tbdd; }

        public Builder setNodes(Map<Ip,Node> nodes) {
            this.nodes = nodes;
            return this;
        }

        public Builder setLocations(Set<Location> locations) {
            this.locations = locations;
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
            return new Refine(this.tbdd,this.nodes, this.locations,
                    this.imports, this.exports, this.targets, this.assumptions, this.incoming, this.inferred);
        }
    }

    public static Builder builder(TransferBDD tbdd) {
        return new Builder(tbdd);
    }

    public record Result(boolean verified,
            Map<Location, Invariant> initial, Map<Location, Invariant> interpolants, Map<Location, Invariant> refined) {
        public Map<Location,String> displayInitial(BDDString.Shortcuts shortcuts) {
            Map<Location,String> strings = new HashMap<>();
            initial.forEach((loc,inv) -> strings.put(loc,inv.toString(true,shortcuts)));
            return strings;
        }
        public Map<Location,String> displayRefinement(BDDString.Shortcuts shortcuts) {
            Map<Location,String> strings = new HashMap<>();
            refined.forEach((loc,inv) -> strings.put(loc,inv.toString(true,shortcuts)));
            return strings;
        }
        public Map<Location,String> displayInterpolants(BDDString.Shortcuts shortcuts) {
            Map<Location,String> strings = new HashMap<>();
            interpolants.forEach((loc,inv) -> strings.put(loc,inv.toString(true,shortcuts)));
            return strings;
        }
    }

    private Refine(TransferBDD tbdd,
                   Map<Ip,Node> nodes, Set<Location> locations,
                   Map<Edge, RoutingPolicy> imports, Map<Edge, RoutingPolicy> exports,
                   Map<Location, Invariant> targets, Map<Location, Invariant> assumptions,
                   Set<Edge> incoming, Map<Location, Invariant> inferred) {
        this.tbdd = tbdd;
        this.nodes = nodes;
        this.locations = locations;
        this.imports = imports;
        this.exports = exports;
        this.targets = targets;
        this.assumptions = assumptions;
        this.enteringNetwork = incoming;
        this.inferred = inferred;
    }

    ///  Assume that the working list includes the correct starting points for inference
    private Map<Location, Invariant> strengtheningLoop() {
        Map<Location, Invariant> refinements = new HashMap<>();
        // assigning all the starting incoming edges back to their inferred invariant otherwise set false
        inferred.keySet().forEach(starter ->
                refinements.put(starter,working.contains(starter) ? inferred.get(starter) : Invariant.getFalse(tbdd)));
        while (!working.isEmpty()) {
            Location lastKnown = working.remove();
            LOGGER.info("Working to refine the property following: {}", lastKnown);
            if (lastKnown instanceof Edge edge && nodes.containsKey(edge.getDst())) {
                Node toRefine = nodes.get(edge.getDst());
                Invariant weakest = inferred.get(toRefine).copy();
                Invariant strongest = refinements.get(edge).strongestPostcondition(imports.get(edge));
                BDD interpolant = interpolate(tbdd,strongest.wellFormedBDD(),weakest.wellFormedBDD());
                Invariant previous = refinements.get(toRefine);
                refinements.put(toRefine,new Invariant(tbdd,interpolant.or(previous.wellFormedBDD())));
                if (!refinements.get(toRefine).equals(previous)) {
                    working.add(toRefine);
                }
            } else if (lastKnown instanceof Node source) {
                Invariant precondition = refinements.get(source);
                for (Location neighbor : inferred.keySet()) {
                    if (neighbor instanceof Edge toRefine && toRefine.isSrc(source)) {
                        Invariant weakest = inferred.get(toRefine).copy();
                        Invariant strongest = precondition.strongestPostcondition(exports.get(toRefine));
                        BDD interpolant = interpolate(tbdd,strongest.wellFormedBDD(),weakest.wellFormedBDD());
                        Invariant previous = refinements.put(toRefine,new Invariant(tbdd,interpolant));
                        if (previous == null || !refinements.get(toRefine).equals(previous)){
                            // if there is already an edge entering this destination, we don't need to add it twice
                            if (!working.contains(nodes.get(toRefine.getDst()))) working.add(toRefine);
                        }
                    }
                }
            }
        }
        return refinements;
    }

    public Result noRefinement() {
        boolean verified = assumptions.keySet().stream().allMatch(
                loc -> inferred.containsKey(loc) && assumptions.get(loc).implies(inferred.get(loc)));
        return new Result(verified,inferred,new HashMap<>(),inferred);
    }

    public Result refine() {
        Map<Location, Invariant> interpolants = new HashMap<>();
        working.clear();
        // TODO determine if we want to include assumptions as ingress nodes (or maybe have option for user to specify ingress)
        working.addAll(enteringNetwork);
        if (working.isEmpty()) {
            boolean verified = assumptions.keySet().stream().allMatch(
                    loc -> inferred.containsKey(loc) && assumptions.get(loc).implies(inferred.get(loc)));
            return new Result(verified,inferred,interpolants,inferred);
        }
        Map<Location, Invariant> finalized = strengtheningLoop();
        finalized.forEach((loc,inv) -> { assert inv.implies(inferred.get(loc)); });
        finalized.forEach((loc,inv) -> {
            if (!inv.implies(inferred.get(loc)))
                throw new BatfishException("Inferred invariant does not imply the weakest condition that was needed @ location " + loc);
        });
        targets.forEach((loc,i) -> { assert finalized.containsKey(loc); });
        boolean verified = assumptions.keySet().stream().allMatch(
                loc -> finalized.containsKey(loc) && assumptions.get(loc).implies(finalized.get(loc)));
        return new Result(verified,inferred,interpolants,finalized);
    }
}
