package org.batfish.minesweeper.question.liveness;

import org.batfish.common.BatfishException;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.List;
import java.util.Map;
import java.util.Stack;

public class Path {
    private final @Nonnull Location[] steps;
    private final @Nonnull Invariant[] properties;

    private Path(Location[] steps, Invariant[] properties) {
        this.steps = steps == null ? new Location[0] : steps;
        this.properties = properties == null ? new Invariant[0] : properties;
        if (this.steps.length != this.properties.length)
            throw new BatfishException("Path.constructor - " + this.steps.length +
                    " locations on the path and " + this.properties.length + " properties provided.");
    }

    public record Context(@Nonnull TransferBDD tbdd, @Nonnull Map<Location, Invariant> assumptions,
                          @Nonnull Map<Edge, RoutingPolicy> imports, @Nonnull Map<Edge, RoutingPolicy> exports) {}

    public static Builder builder(@Nonnull Context ctx) { return new Builder(ctx.tbdd(),ctx.imports(),ctx.exports(),ctx.assumptions()); }

    public static class Builder {
        private final @Nonnull TransferBDD tbdd;
        private final @Nonnull Map<Edge, RoutingPolicy> imports;
        private final @Nonnull Map<Edge, RoutingPolicy> exports;
        private final @Nonnull Stack<Location> steps;
        private final @Nonnull Map<Location, Invariant> assumptions;

        private Builder(@Nonnull TransferBDD tbdd, @Nonnull Map<Edge, RoutingPolicy> imports, @Nonnull Map<Edge, RoutingPolicy> exports,
                        @Nonnull Map<Location, Invariant> assumptions) {
            this.tbdd = tbdd;
            this.imports = imports;
            this.exports = exports;
            this.assumptions = assumptions;
            this.steps = new Stack<>();
        }

        /// Adds the location to the path (going backwards from the target) if the path is valid,
        /// returns a boolean indicating if the path was updated
        public boolean addToPath(Location next) {
            Location previous = steps.peek();
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
                if (incomingToPrevious.isDst(previousNode) && imports.containsKey(incomingToPrevious)) {
                    steps.push(next.copy());
                    return true;
                } // otherwise falls through to false
            } else if (next instanceof Node outgoingFromNode && previous instanceof Edge outgoingEdge) {
                // previous location is an edge, so the next location should be the node it came from
                if (outgoingEdge.isSrc(outgoingFromNode) && exports.containsKey(outgoingEdge)) {
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
        public boolean fromList(List<Location> steps) {
            if (steps == null) {
                this.steps.clear();
                return false;
            } else {
                for (Location next : steps) {
                    if (!this.addToPath(next)) {
                        this.steps.clear();
                        return false;
                    }
                }
                return true;
            }
        }

        /// Builds a path object according to the builder. If there is no path that can be constructed, a null is returned.
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
            Invariant initialAssumption = assumptions.getOrDefault(locations[locations.length-1],new Invariant(tbdd));
            return predicates[predicates.length-1].impliedBy(initialAssumption) ? new Path(locations,predicates) : null;
        }
    }
}
