package org.batfish.minesweeper.question.liveness;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableMap;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;

import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;

public class Path {
    private final @Nonnull Context context;
    private final @Nonnull Location[] steps;
    private final @Nonnull Invariant[] properties;

    /// Note, the only way to build a path is through a Path.Builder. This guarantees that
    /// the path is connected and invariants are inferred.
    private Path(Location[] steps, Invariant[] properties, @Nonnull Context context) {
        this.steps = steps == null ? new Location[0] : steps;
        this.properties = properties == null ? new Invariant[0] : properties;
        this.context = context;
        if (this.steps.length != this.properties.length)
            throw new BatfishException("Path.constructor - " + this.steps.length +
                    " locations on the path and " + this.properties.length + " properties provided.");
    }

    /// Network context needed
    public record Context(@Nonnull TransferBDD tbdd, @Nonnull Map<Location, Invariant> assumptions,
                          @Nonnull Map<Edge, RoutingPolicy> imports, @Nonnull Map<Edge, RoutingPolicy> exports) {
        public BDD prefixSpaceToBDD(PrefixSpace space) {
            BDDRoute r = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
            BDDFactory factory = r.getPrefix().getFactory();
            BDD result = factory.zero();
            for (PrefixRange range : space.getPrefixRanges()) {
                BDD rangeBDD = isRelevantForDestination(r,range);
                result = result.or(rangeBDD);
            }
            return result.and(r.wellFormednessConstraints(true));
        }
    }

    /// Return a path builder according to this network's context
    public static Builder builder(@Nonnull Context ctx) { return new Builder(ctx.tbdd(),ctx.imports(),ctx.exports(),ctx.assumptions()); }

    /// Returns this path if the incoming assumption satisfies the needed incoming invariant
    public Optional<Path> isGoodPath() {
        Invariant initialAssumption = context.assumptions().getOrDefault(steps[steps.length-1],new Invariant(context.tbdd()));
        // returns this path if the assumption implies the condition needed to have a live path reach the target location
        return properties[properties.length-1].impliedBy(initialAssumption) ? Optional.of(this) : Optional.empty();
    }

    /// Displays the path
    public String display() {
        StringBuilder builder = new StringBuilder();
        for (Location step : steps) {
            if (step instanceof Edge edge) {
                builder.insert(0,edge);
            } else if (step instanceof Node node) {
                builder.insert(0," [" + node + "] ");
            }
        }
        return builder.toString();
    }

    /// A Path.Builder represents a path which should be connected but has not had any liveness inference performed.
    /// This could be provided by user if we want the user to provide the path.
    @VisibleForTesting
    public static class Builder implements Comparable<Builder> {
        private final @Nonnull TransferBDD tbdd;
        private final @Nonnull Map<Edge, RoutingPolicy> imports;
        private final @Nonnull Map<Edge, RoutingPolicy> exports;
        /// Bottom of the stack is the target location
        private final @Nonnull Stack<Location> steps;
        private final @Nonnull Map<Location, Invariant> assumptions;

        private Builder(@Nonnull TransferBDD tbdd, @Nonnull Map<Edge, RoutingPolicy> imports, @Nonnull Map<Edge, RoutingPolicy> exports,
                        @Nonnull Map<Location, Invariant> assumptions, @Nonnull Stack<Location> steps) {
            this.tbdd = tbdd;
            this.imports = ImmutableMap.copyOf(imports);
            this.exports = ImmutableMap.copyOf(exports);
            this.assumptions = ImmutableMap.copyOf(assumptions);;
            this.steps = copySteps(steps);
        }

        /// Copied the steps in path to new stack
        @VisibleForTesting
        static Stack<Location> copySteps(Stack<Location> steps) {
            Stack<Location> result = new Stack<>();
            steps.forEach(loc -> result.push(loc.copy()));
            return result;
        }

        private Builder(@Nonnull TransferBDD tbdd, @Nonnull Map<Edge, RoutingPolicy> imports, @Nonnull Map<Edge, RoutingPolicy> exports,
                        @Nonnull Map<Location, Invariant> assumptions) {
            this(tbdd,imports,exports,assumptions,new Stack<>());
        }

        /// Generates new Path.Builders corresponding to expanding this Path.Builder according to each possible step
        public Set<Builder> expand(@Nonnull Set<Edge> potentialSteps) {
            Set<Builder> result = new HashSet<>();
            for (Location step : potentialSteps) {
                Builder curr = new Builder(tbdd,imports,exports,assumptions,steps);
                if (curr.addToPath(step))
                    result.add(curr);
            }
            return result;
        }

        ///  Mainly included for testing purposes
        public String display() {
            StringBuilder builder = new StringBuilder();
            for (Location step : steps) {
                if (step instanceof Edge edge) {
                    builder.insert(0,edge);
                } else if (step instanceof Node node) {
                    builder.insert(0," [" + node + "] ");
                }
            }
            return builder.toString();
        }

        /// Adds the location to the path (going backwards from the target) if the path is valid and loop free,
        /// returns a boolean indicating if the path was updated. If this returns false, then the steps
        /// have been cleared/emptied.
        public boolean addToPath(@Nonnull Location next) {
            Location previous = steps.isEmpty() ? null : steps.peek();
            if (previous == null) {
                // first node in path
                steps.push(next.copy());
                return true;
            } else if (steps.contains(next)) {
                // if location is already within the path (prevent loops)
                steps.clear();
                return false;
            } else if (next instanceof Edge incomingToPrevious && previous instanceof Node previousNode) {
                // previous location is a node, so the next location should be the edge going into it
                if (incomingToPrevious.isDst(previousNode)) {
                    steps.push(next.copy());
                    return true;
                } // otherwise falls through to false
            } else if (next instanceof Node outgoingFromNode && previous instanceof Edge outgoingEdge) {
                // previous location is an edge, so the next location should be the node it came from
                if (outgoingEdge.isSrc(outgoingFromNode)) {
                    steps.push(next.copy());
                    return true;
                } // otherwise falls through to false
            }
            // if the path doesn't line up or there is no policy which represents that location, return false with no-op
            steps.clear();
            return false;
        }

        /// Populates path builder from a list of locations (starting with the target location at index 0),
        /// returns boolean indicating if path builder was updated (i.e. path was valid)
        public boolean fromList(@Nonnull List<Location> steps) {
            for (Location next : steps) {
                if (!this.addToPath(next)) {
                    this.steps.clear();
                    return false;
                }
            }
            return true;
        }

        /// Builds a path object according to the builder. This includes inferring the invariants, all paths
        /// go to the outside of the network. The resulting path holds the invariants that must hold at each step
        /// in order for a path to reach the target location adhering to the target property via this path.
        public Path build(@Nonnull Location location, @Nonnull Invariant target) {
            if (steps.isEmpty()) {
                return null;
            } else if (!location.equals(steps.firstElement())) {
                throw new BatfishException("Path.Builder.build() - Path does not end at target location.");
            } else if (!assumptions.containsKey(steps.peek())) {
                throw new BatfishException("Path.Builder.build() - Path does not start at an assumption.");
            }
            Location[] locations = new Location[steps.size()];
            steps.copyInto(locations);
            Invariant[] predicates = new Invariant[steps.size()];
            predicates[0] = target;
            for (int i = 1; i < locations.length; i++) {
                Location curr = locations[i];
                Location prev = locations[i-1];
                Invariant post = predicates[i-1].copy();
                RoutingPolicy policy;
                if (curr instanceof Node && prev instanceof Edge outgoing) {
                    policy = exports.getOrDefault(outgoing, null);
                } else if (curr instanceof Edge incoming && prev instanceof Node) {
                    policy = imports.getOrDefault(incoming,null);
                } else {
                    throw new BatfishException("Path.build() - Path is not valid; going from " + curr + " to " + prev);
                }
                if (policy == null) throw new BatfishException("Path.build() - No policy on record for going from " + curr + " to " + prev);
                predicates[i] = post.weakestPrecondition(policy,false);
            }
            return new Path(locations,predicates,new Context(tbdd,assumptions,imports,exports));
        }

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof Builder other && other.steps.size() == this.steps.size()) {
                for (int i = 0; i < this.steps.size(); i++) {
                    if (!this.steps.elementAt(i).equals(other.steps.elementAt(i)))
                        return false;
                }
                return true;
            } else {
                return false;
            }
        }

        /// Returns the previous step in path, if not empty
        public Optional<Location> previous() {
            return steps.isEmpty() ? Optional.empty() : Optional.of(steps.peek().copy());
        }
        @Override
        public int hashCode() {
            return Objects.hash(steps);
        }

        /// Compares path by length (intended to help sort paths in increasing order)
        @Override
        public int compareTo(Builder o) {
            return Integer.compare(this.steps.size(), o.steps.size());
        }
    }
}
