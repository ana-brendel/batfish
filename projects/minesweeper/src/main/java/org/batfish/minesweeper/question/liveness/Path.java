package org.batfish.minesweeper.question.liveness;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableMap;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.Setup;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;

import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;
import static org.batfish.minesweeper.question.verificationutilities.NetworkInfo.getRouteExample;

public class Path {
  private final @Nonnull Context context;
  private final @Nonnull PrefixSpace prefix;
  private final @Nonnull Location[] steps;
  private final @Nonnull Invariant[] properties;

  /// Note, the only way to build a path is through a Path.Builder. This guarantees that
  /// the path is connected and invariants are inferred.
  private Path(
      Location[] steps,
      Invariant[] properties,
      @Nonnull Context context,
      @Nonnull PrefixSpace prefix) {
    this.prefix = prefix;
    this.steps = steps == null ? new Location[0] : steps;
    this.properties = properties == null ? new Invariant[0] : properties;
    this.context = context;
    if (this.steps.length != this.properties.length) {
      throw new BatfishException(
          "Path.constructor - "
              + this.steps.length
              + " locations on the path and "
              + this.properties.length
              + " properties provided.");
    }
  }

  /// Network context needed
  public record Context(
      @Nonnull TransferBDD tbdd,
      @Nonnull Map<Location, Invariant> checkedAssumptions,
      @Nonnull Map<Location, Invariant> enforcedAssumptions,
      @Nonnull Map<Edge, RoutingPolicy> imports,
      @Nonnull Map<Edge, RoutingPolicy> exports,
      @Nonnull Invariant default_assumption) {
    public BDD prefixSpaceToBDD(PrefixSpace space) {
      BDDRoute r = new BDDRoute(tbdd.getFactory(), tbdd.getConfigAtomicPredicates());
      BDDFactory factory = r.getPrefix().getFactory();
      BDD result = factory.zero();
      for (PrefixRange range : space.getPrefixRanges()) {
        BDD rangeBDD = isRelevantForDestination(r, range);
        result = result.or(rangeBDD);
      }
      return result;
    }
  }

  /// Return a path builder according to this network's context
  public static Builder builder(@Nonnull Context ctx) {
    return new Builder(
        ctx.tbdd(),
        ctx.imports(),
        ctx.exports(),
        ctx.checkedAssumptions(),
        ctx.enforcedAssumptions(),
        ctx.default_assumption());
  }

  public void freeBDDs() {
    for (Invariant inv : this.properties) {
      if (inv != null) {
        inv.free();
      }
    }
  }

  /// Returns this path if the incoming assumption satisfies the needed incoming invariant
  public boolean isGoodPath() {
    BDD initialAssumption =
        context
            .prefixSpaceToBDD(prefix)
            .andWith(
                context
                    .checkedAssumptions()
                    .getOrDefault(steps[steps.length - 1], context.default_assumption())
                    .getBDDCopy());
    Invariant initial =
        new Invariant(
            context.tbdd,
            initialAssumption.andWith(
                context.tbdd.getOriginalRoute().wellFormednessConstraints(true)));
    boolean result = !initial.isFalse() && properties[properties.length - 1].impliedBy(initial);
    initialAssumption.free();
    return result;
  }

  /// Displays the path as a string
  public String display(NetworkInfo info) {
    StringBuilder builder = new StringBuilder();
    for (Location step : steps) {
      if (step instanceof Edge edge) {
        builder.insert(0, edge);
      } else if (step instanceof Node node) {
        builder.insert(0, " [" + info.locationStr(node) + "] ");
      }
    }
    return builder.toString();
  }

  /// Displays the "bad" path as a string - assumes the path is a "bad path"
  public String displayBadPath(NetworkInfo info) {
    StringBuilder builder = new StringBuilder();
    assert steps.length == properties.length;
    for (int i = 0; i < steps.length; i++) {
      if (steps[i] instanceof Edge edge) {
        builder.insert(0, edge);
      } else if (steps[i] instanceof Node node) {
        builder.insert(0, " [" + info.locationStr(node) + "] ");
      }
      if (properties[i].isFalse()) {
        builder.insert(0, "{FALSE} ");
        return builder.toString();
      }
    }
    assert properties.length - 1 == steps.length - 1;
    // the assumptions used here should be the assumptions that we want checked
    BDD currentAssumption = info.getCheckedAssumptions().get(steps[steps.length - 1]).getBDD();
    currentAssumption.andWith(context.prefixSpaceToBDD(this.prefix));
    BDD counterBDD = currentAssumption.diffEq(properties[properties.length - 1].getBDD());
    counterBDD.andWith(context.tbdd().getOriginalRoute().wellFormednessConstraints(true));
    // we shouldn't be in this function if the path has no counterexamples
    assert !counterBDD.isZero();
    Bgpv4Route route = getRouteExample(info.tbdd, counterBDD);
    String cex = route != null ? Setup.nonDefaultRoute(route) : "{NO SAT ASSIGNMENT}";
    currentAssumption.free();
    builder.insert(0, cex + " ");
    return "Inferred Invariant: " + properties[properties.length - 1] + "\n" + builder;
  }

  public Map<Node, Invariant> reachableRoutes() {
    Invariant curr = new Invariant(context.tbdd, context.prefixSpaceToBDD(prefix));
    ImmutableMap.Builder<Node, Invariant> result = new ImmutableMap.Builder<>();
    int i = steps.length - 1;
    while (i > 0) {
      Location loc = steps[i];
      if (loc instanceof Node) {
        i--;
        continue;
      }
      Edge edge = (Edge) loc;
      if (context.checkedAssumptions.containsKey(edge)) {
        // the edge is coming from outside the network
        curr.free();
        curr = context.checkedAssumptions.get(loc);
      } else {
        // the edge is internal so do a strongest post computation
        RoutingPolicy exportPolicy = context.exports.get(edge);
        if (exportPolicy != null) {
          curr = curr.strongestPostcondition(exportPolicy);
        }
        curr = curr.postExport();
      }
      RoutingPolicy importPolicy = context.imports.get(edge);
      if (importPolicy != null) {
        curr = curr.strongestPostcondition(importPolicy);
      }
      result.put((Node) steps[i - 1], curr);
      i -= 2;
    }
    return result.build();
  }

  /// A Path.Builder represents a path which should be connected but has not had any liveness
  /// inference performed. This could be provided by user if we want the user to provide the path.
  @VisibleForTesting
  public static class Builder implements Comparable<Builder> {
    private final @Nonnull TransferBDD tbdd;
    private final @Nonnull Map<Edge, RoutingPolicy> imports;
    private final @Nonnull Map<Edge, RoutingPolicy> exports;
    /// Bottom of the stack is the target location, top of stack is the entry point
    private final @Nonnull Stack<Location> steps;
    private final @Nonnull Map<Location, Invariant> checkedAssumptions;
    private final @Nonnull Map<Location, Invariant> enforcedAssumptions;
    private final @Nonnull Invariant default_assumption;

    private Builder(
        @Nonnull TransferBDD tbdd,
        @Nonnull Map<Edge, RoutingPolicy> imports,
        @Nonnull Map<Edge, RoutingPolicy> exports,
        @Nonnull Map<Location, Invariant> checkedAssumptions,
        @Nonnull Map<Location, Invariant> enforcedAssumptions,
        @Nonnull Stack<Location> steps,
        @Nullable Invariant default_assumption) {
      this.tbdd = tbdd;
      this.imports = ImmutableMap.copyOf(imports);
      this.exports = ImmutableMap.copyOf(exports);
      this.checkedAssumptions = ImmutableMap.copyOf(checkedAssumptions);
      this.enforcedAssumptions = ImmutableMap.copyOf(enforcedAssumptions);
      this.steps = copySteps(steps);
      this.default_assumption =
          default_assumption == null ? new Invariant(tbdd) : default_assumption.copy();
    }

    /// Copied the steps in path to new stack
    @VisibleForTesting
    static Stack<Location> copySteps(Stack<Location> steps) {
      Stack<Location> result = new Stack<>();
      steps.forEach(loc -> result.push(loc.copy()));
      return result;
    }

    private Builder(
        @Nonnull TransferBDD tbdd,
        @Nonnull Map<Edge, RoutingPolicy> imports,
        @Nonnull Map<Edge, RoutingPolicy> exports,
        @Nonnull Map<Location, Invariant> checkedAssumptions,
        @Nonnull Map<Location, Invariant> enforcedAssumptions,
        @Nullable Invariant default_assumption) {
      this(
          tbdd,
          imports,
          exports,
          checkedAssumptions,
          enforcedAssumptions,
          new Stack<>(),
          default_assumption);
    }

    /// Generates new Path.Builders corresponding to expanding this Path.Builder according to each
    /// possible step
    public Set<Builder> expand(@Nonnull Set<Edge> potentialSteps) {
      Set<Builder> result = new HashSet<>();
      for (Location step : potentialSteps) {
        Builder curr =
            new Builder(
                tbdd,
                imports,
                exports,
                checkedAssumptions,
                enforcedAssumptions,
                steps,
                default_assumption);
        if (curr.addToPath(step)) {
          result.add(curr);
        }
      }
      return result;
    }

    ///  Mainly included for testing purposes
    public String display() {
      StringBuilder builder = new StringBuilder();
      for (Location step : steps) {
        if (step instanceof Edge edge) {
          builder.insert(0, edge);
        } else if (step instanceof Node node) {
          builder.insert(0, " [" + node + "] ");
        }
      }
      return builder.toString();
    }

    /// Adds the location to the path (going backwards from the target) if the path is valid and
    /// loop free, returns a boolean indicating if the path was updated. If this returns false, then
    /// the steps have been cleared/emptied.
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
        // previous location is a node, so the next location should be the edge going into it,
        // we also want to check that this edge doesn't loop back over the edge that came before
        if (incomingToPrevious.isDst(previousNode)
            && this.lastEdge()
                .map(lastEdge -> !lastEdge.flipEdge().equals(incomingToPrevious))
                .orElse(true)) {
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
      // if the path doesn't line up or there is no policy which represents that location, return
      // false with no-op
      steps.clear();
      return false;
    }

    /// Populates path builder from a list of locations (starting with the target location at index
    // 0),
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

    /// Builds a path object according to the builder. This includes inferring the invariants, all
    /// paths go to the outside of the network. The resulting path holds the invariants that must
    /// hold at each step in order for a path to reach the target location adhering to the target
    /// property via this path.
    public Path build(
        @Nonnull Location location, @Nonnull Invariant target, @Nonnull PrefixSpace prefix) {
      if (steps.isEmpty()) {
        return null;
      } else if (!location.equals(steps.firstElement())) {
        // might make sense as assert
        throw new BatfishException("Path.Builder.build() - Path does not end at target location.");
      } else if (!checkedAssumptions.containsKey(steps.peek())) {
        // might make sense as assert
        throw new BatfishException("Path.Builder.build() - Path does not start at an assumption.");
      }
      Location[] locations = new Location[steps.size()];
      steps.copyInto(locations);
      Invariant[] predicates = new Invariant[steps.size()];
      predicates[0] = target;
      for (int i = 1; i < locations.length; i++) {
        Location curr = locations[i];
        Location prev = locations[i - 1];
        Invariant post = predicates[i - 1].copy();
        RoutingPolicy policy;
        if (curr instanceof Node && prev instanceof Edge outgoing) {
          policy = exports.getOrDefault(outgoing, null);
          // if we are pushing post back through an export policy,
          // we first account for the export transformations that BGP does
          post = post.preImport();
        } else if (curr instanceof Edge incoming && prev instanceof Node) {
          policy = imports.getOrDefault(incoming, null);
        } else {
          // might make sense as assert
          throw new BatfishException(
              "Path.build() - Path is not valid; going from " + curr + " to " + prev);
        }
        if (policy == null) {
          // no policy so the weakest precondition is this post condition just pushed on
          predicates[i] = post.copy();
        } else {
          predicates[i] = post.weakestPrecondition(policy, false);
        }
        // if there is an enforced assumption at this location, make sure we include
        if (enforcedAssumptions.containsKey(curr)) {
          // and with this assumption, if false, then this assumption won't meet conditions
          predicates[i].getBDD().andWith(enforcedAssumptions.get(curr).getBDDCopy());
        }
      }
      return new Path(
          locations,
          predicates,
          new Context(
              tbdd, checkedAssumptions, enforcedAssumptions, imports, exports, default_assumption),
          prefix);
    }

    @Override
    public boolean equals(Object obj) {
      if (obj instanceof Builder other && other.steps.size() == this.steps.size()) {
        for (int i = 0; i < this.steps.size(); i++) {
          if (!this.steps.elementAt(i).equals(other.steps.elementAt(i))) {
            return false;
          }
        }
        return true;
      } else {
        return false;
      }
    }

    /// Returns the previous step in path, if not empty. When a path is done, this will get you the
    /// start of the path which leads to the start location/property
    public Optional<Location> previous() {
      return steps.isEmpty() ? Optional.empty() : Optional.of(steps.peek().copy());
    }

    /// Returns the previous step before the last step in path, if not empty. This is used to check
    /// we don't go back over an edge that we just came from
    public Optional<Edge> lastEdge() {
      if (steps.size() >= 2 && steps.elementAt(steps.size() - 2).copy() instanceof Edge e) {
        return Optional.of(e);
      } else {
        return Optional.empty();
      }
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
