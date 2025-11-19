package org.batfish.minesweeper.question.verify;

import net.sf.javabdd.BDD;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;
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
import java.util.Set;
import java.util.stream.Collectors;

public class NetworkThread {
    private final Cause cause;
    private final Effect effect;
    private final Map<Node,Set<Path>> threads;

    private NetworkThread(Cause cause, Effect effect, Map<Node, Set<Path>> threads){
        this.cause = cause;
        this.effect = effect;
        this.threads = threads;
    }

    public Set<String> dirtyString(List<String> prefixes) {
        Set<String> paths = this.threads.values().stream().map(Object::toString).collect(Collectors.toSet());
        paths.add("[CAUSE] " + this.cause.dirtyString(prefixes));
        paths.add("[EFFECT] " + this.effect.dirtyString(this.cause.tbdd,prefixes));
        return paths;
    }

    private void explorePaths(Map<Node,Set<Node>> neighbors, Map<Edge,RoutingPolicy> imports, Map<Edge,RoutingPolicy> exports) {
        Set<Node> nodes = new HashSet<>(threads.keySet());
//        for (Node starter : nodes) {
//            Set<Path> paths = new HashSet<>();
//            for (Path path : threads.get(starter)) {
//                paths.addAll(path.expand(cause,effect,neighbors,imports,exports));
//            }
//            threads.put(starter,paths);
//        }
    }

    public static Builder builder(Node starter, Optional<Node> exportTo) {
        return new Builder(starter,exportTo);
    }

    public static class Builder {
        private final Cause.Builder cause;
        private final Effect.Builder effect;
        private final Node starter;
        private final Optional<Node> exportTo;

        private Builder(Node starter, Optional<Node> exportTo) {
            cause = Cause.builder();
            effect = Effect.builder();
            this.starter = starter;
            this.exportTo = exportTo; // if there is no prior, then this came from import
        }

        public Cause.Builder causeBuilder() {
            return cause;
        }

        public Effect.Builder effectBuilder() {
            return effect;
        }

        public NetworkThread build() {
            Cause c = cause.build();
            Map<Node,Set<Path>> map = new HashMap<>();
            map.put(starter,Set.of(new Path(c,starter,exportTo)));
            return new NetworkThread(c,effect.build(),map);
        }
    }

    public static class Cause {
        private final TransferBDD tbdd;
        private final BDD checked;
        private Cause(TransferBDD tbdd, @Nonnull BDD checked) {
            this.tbdd = tbdd;
            this.checked = checked;
        }

        public String dirtyString(List<String> prefixes) {
            Invariant forPrint = new Invariant(tbdd,checked);
            List<String> disjunction = forPrint.dirtyReadability(prefixes);
            return String.join(" OR ",disjunction);
        }

        public Cause copy() {
            return new Cause(tbdd,this.checked.id());
        }

        public static Builder builder() {
            return new Builder();
        }

        public static class Builder {
            private BDD checked;
            private TransferBDD tbdd;

            private Builder() { }

            public void addCondition(TransferBDD tbdd, BDD constraint) {
                checked = constraint.id();
                this.tbdd = tbdd;
            }

            public Cause build() {
                return new Cause(tbdd,checked);
            }

        }
    }

    public static class Effect {
        private final BDDRoute modification;

        private Effect(BDDRoute modification) {
            this.modification = modification == null ? null : modification.deepCopy();
        }

        public static Effect.Builder builder() {
            return new Effect.Builder();
        }

        public static class Builder {
            private BDDRoute modification;
            private Builder() { }

            public Effect.Builder addModification(BDDRoute modification) {
                this.modification = modification == null ? null : modification.deepCopy();
                return this;
            }

            public Effect build() {
                return new Effect(modification);
            }
        }

        public Cause causeFromEffect(Cause input) {
            if (modification == null) {
                return new Cause(input.tbdd,input.tbdd.getFactory().zero());
            } else if (input.checked.isZero()) { // if checked condition is always false, so is this one
                return input.copy();
            } else {
                BDD postconditions = modification.wellFormednessConstraints(true);
                // for each bdd variable, need to determine if it is true on output
                Map<Integer,BDD> pairing = getVariableMappingAsMap(input.tbdd, modification);
                for (int i : pairing.keySet()) {
                    BDD precondition = pairing.get(i);
                    // a variable is true on the output, if the condition that sets it true is true on the input
                    if (input.checked.imp(precondition).isOne()) { // if the input constraint implies the needed precondition
                        BDD var = modification.getFactory().ithVar(i); // that variable is true on the output
                        postconditions = postconditions.and(var);
                    }
                }
                // QUESTION -- Do we need to intersect with the input constraints?
                // TENTATIVE ANSWER -- No, but we'll need to consider both when propagating
                // (i.e. the input constraint for future checks will need to assert that there aren't contradictions)
                return new Cause(input.tbdd,postconditions.id());
            }
        }

        public Cause causeFromEffect(TransferBDD tbdd, BDD input) {
            if (modification == null) {
                return new Cause(tbdd,tbdd.getFactory().zero());
            } else if (input.isZero()) { // if checked condition is always false, so is this one
                return new Cause(tbdd,input.id());
            } else {
                BDD postconditions = modification.wellFormednessConstraints(true);
                // for each bdd variable, need to determine if it is true on output
                Map<Integer,BDD> pairing = getVariableMappingAsMap(tbdd, modification);
                for (int i : pairing.keySet()) {
                    BDD precondition = pairing.get(i);
                    // a variable is true on the output, if the condition that sets it true is true on the input
                    if (input.imp(precondition).isOne()) { // if the input constraint implies the needed precondition
                        BDD var = modification.getFactory().ithVar(i); // that variable is true on the output
                        postconditions = postconditions.and(var);
                    }
                }
                // QUESTION -- Do we need to intersect with the input constraints?
                // TENTATIVE ANSWER -- No, but we'll need to consider both when propagating
                // (i.e. the input constraint for future checks will need to assert that there aren't contradictions)
                return new Cause(tbdd,postconditions.id());
            }
        }

        public String dirtyString(TransferBDD tbdd, List<String> prefixes) {
            if (modification == null) return "DENIED";
            BDD bdd = this.causeFromEffect(tbdd,tbdd.getFactory().one()).checked;
            Invariant forPrint = new Invariant(tbdd,bdd);
            List<String> disjunction = forPrint.dirtyReadability(prefixes);
            return String.join(" OR ",disjunction);
        }
    }

    public static class Path {
        enum Closure { DENIED, CHANGED, OPEN }

        private final LinkedList<Node> sequence;
        private Closure ending;
        private BDD constraints;
        private Optional<Node> exportTo;
        private boolean inNode;

        public Path(Cause cause, Node start, Optional<Node> exportTo) {
            sequence = new LinkedList<>();
            sequence.add(start);
            ending = Closure.OPEN;
            constraints = cause.checked.id();
            this.exportTo = exportTo;
            inNode = exportTo.isPresent(); // if there is a next, that means that this effect was exported out of node
        }

        private Path(List<Node> sequence, Closure ending, BDD constraints, boolean inNode) {
            this.sequence = new LinkedList<>(sequence);
            this.ending = ending;
            this.constraints = constraints.id();
            this.inNode = inNode;
        }

        @Override
        public String toString() {
            String path = String.join(" -> ", sequence.stream().map(Node::toString).collect(Collectors.toSet()));
            if (ending == Closure.CHANGED) {
                return "[CHANGED] " + path;
            } else if (ending == Closure.DENIED) {
                return "[DENIED] " + path;
            } else {
                return "[OPEN] " + path;
            }
        }

        public Path copy() { return new Path(sequence,ending,constraints,inNode); }

        private Path updateClosure(Closure closure) {
            ending = closure;
            return this;
        }

        private Path updateConstraint(BDD constraints) {
            this.constraints = constraints;
            return this;
        }

        private Path withinNode(boolean update) {
            this.inNode = update;
            return this;
        }

        private Path addToPath(Node next) {
            sequence.add(next);
            return this;
        }

        /// From the current path, executes the policy and returns updated paths with all constraints
        /// (the sequence of the path has not been updated this is just to check for behavior at a node)
        private static Set<Path> throughPolicy(Path current, Cause cause, Effect effect, RoutingPolicy policy) {
            if (policy == null || policy.getStatements().isEmpty() || current.ending != Closure.OPEN) {
                return Set.of(current.copy());
            }
            TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
            List<TransferReturn> paths;
            try {
                paths = cause.tbdd.computePaths(policy.getStatements(),context,true);
            } catch (Exception e) {
                String name = policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
                throw new BatfishException("Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
            }
            if (paths.stream().filter(TransferReturn::getAccepted).toList().isEmpty()) {
                // if no route get through, then this ends the cause/effect
                return Set.of(current.copy().updateClosure(Closure.DENIED));
            } else {
                Set<Path> constrainedPaths = new HashSet<>();
                BDDRoute base = new BDDRoute(cause.tbdd.getFactory(), cause.tbdd.getConfigAtomicPredicates());
                BDD wf = base.wellFormednessConstraints(true);
                BDD constraintsFromEffect = effect.causeFromEffect(cause).checked;
                for (TransferReturn path : paths) {
                    // We need to only look at guards that might apply to current thread
                    BDD pathAnnouncements = wf.and(path.getInputConstraints()); // guards from this path
                    //BDD intersectionWithConstraints = pathAnnouncements.and(current.constraints); // checked with accumulated constraints
                    BDD intersectWithEffectConstraints = pathAnnouncements.and(constraintsFromEffect); // also account for effects
                    if (intersectWithEffectConstraints.isZero() || !path.getAccepted()) {
                        // if no route gets through matching constraints, then this ends the cause/effect
                        constrainedPaths.add(current.copy().updateClosure(Closure.DENIED));
                    } else {
                        // Path updated = current.copy();
                        // BDD updatedConstraint = updated.constraints;
                        // effect from this execution path
                        Effect newEffect = Effect.builder().addModification(path.getOutputRoute()).build();
                        // BDD for the modification results on the original effect and constraints, and path constraints
                        BDD modificationBDD = newEffect.causeFromEffect(cause.tbdd,intersectWithEffectConstraints).checked;
                        if (modificationBDD.isZero()) {
                            // the path is still permitted but something has been changed which disagrees with the effect
                            constrainedPaths.add(current.copy().updateClosure(Closure.CHANGED));
                        } else {
                            // this path is still open and the constraints are updated to now include the modifications and
                            // path announcements from this policy
                            constrainedPaths.add(current.copy());
                        }
                    }
                }
                return constrainedPaths;
            }
        }
    }

    /// This will just get the starts of threads (based on guards and modifications) -- still need to expand them
    private static Set<NetworkThread> getThreadsFromPolicy(TransferBDD tbdd, Node start, RoutingPolicy policy, Optional<Node> prior) {
        if (policy == null || policy.getStatements().isEmpty()) {
            return new HashSet<>(); // no new threads started
        }
        TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
        List<TransferReturn> paths;
        try {
            paths = tbdd.computePaths(policy.getStatements(),context,true);
        } catch (Exception e) {
            String name = policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
            throw new BatfishException("Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
        }
        if (paths.stream().filter(TransferReturn::getAccepted).toList().isEmpty()) {
            return new HashSet<>(); // no new threads started
        } else {
            BDDRoute base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
            BDD wf = base.wellFormednessConstraints(true);
            Set<NetworkThread> threads = new HashSet<>();
            for (TransferReturn path : paths) {
                if (path.getAccepted()) {
                    NetworkThread.Builder tb = NetworkThread.builder(start,prior);
                    tb.cause.addCondition(tbdd,wf.and(path.getInputConstraints()));
                    tb.effect.addModification(path.getOutputRoute());
                    if (!path.getOutputRoute().equals(base)) {
                        threads.add(tb.build());
                    }
                } else {
                    NetworkThread.Builder tb = NetworkThread.builder(start,prior);
                    tb.cause.addCondition(tbdd,wf.and(path.getInputConstraints()));
                    threads.add(tb.build());
                }
            }
            return threads;
        }
    }

    public static Set<NetworkThread> getThreadsFromVerifier(Verifier verifier) {
        TransferBDD tbdd = verifier.getTBDD();
        Map<Edge,RoutingPolicy> imports = verifier.getImports();
        Map<Edge,RoutingPolicy> exports = verifier.getExports();
        Map<Ip,Node> nodes = verifier.getNodes();
        Set<Edge> edges = verifier.getLocations().stream().filter(loc -> loc instanceof Edge)
                .map(loc -> (Edge) loc).collect(Collectors.toSet());
        Map<Node,Set<Node>> neighbors = new HashMap<>();
        nodes.values().forEach(node -> neighbors.put(node, edges.stream()
                .filter(e -> e.getSrc().equals(node.getIp()))
                .map(e -> nodes.get(e.getDst())).collect(Collectors.toSet())));

        Set<NetworkThread> threads = new HashSet<>();

        // for import of src -> dst, we are at the dst and don't need prior (within Node)
        imports.forEach((key, value) -> threads.addAll(getThreadsFromPolicy(tbdd, nodes.get(key.getDst()), value,Optional.empty())));
        // for export of src -> dst, we are at the dst and need prior (outside node)
        exports.forEach((key, value) -> threads.addAll(getThreadsFromPolicy(tbdd, nodes.get(key.getSrc()), value,Optional.of(nodes.get(key.getDst())))));

        //Set<Set<String>> strs = threads.stream().map(t -> t.dirtyString(ImmutableList.of("25.13.0.0/16"))).collect(Collectors.toSet());

        threads.forEach(thread -> thread.explorePaths(neighbors,imports,exports));

        return threads;
    }

    private static Map<Integer,BDD> getVariableMappingAsMap(TransferBDD tbdd, BDDRoute route) {
        BDDRoute base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        Map<Integer,BDD> pairs = new HashMap<>();
        // PREFIX CONSTRAINTS
        for (int i = 0; i < base.getPrefix().size(); i++) {
            BDD bdd_var = base.getPrefix().getBitBDD(i);
            BDD new_bdd = route.getPrefix().getBitBDD(i);
            assert bdd_var != null;
            pairs.put(bdd_var.var(),new_bdd);
        }
        // COMMUNITY CONSTRAINTS
        for (int i = 0; i < base.getCommunityAtomicPredicates().length; i++) {
            BDD bdd_var = base.getCommunityAtomicPredicates()[i];
            BDD new_bdd = route.getCommunityAtomicPredicates()[i];
            pairs.put(bdd_var.var(),new_bdd);
        }
        return pairs;
    }
}
