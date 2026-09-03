package org.batfish.minesweeper.question.reachability;

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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

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

  public static Path create(
      Location[] steps,
      Invariant[] properties,
      @Nonnull Context context,
      @Nonnull PrefixSpace prefix) {
    return new Path(steps, properties, context, prefix);
  }

  public Map<Location, Invariant> getConstraints() {
    Map<Location, Invariant> constraints = new HashMap<>();
    for (int i = 0; i < this.steps.length - 1; i++) {
      constraints.put(this.steps[i], this.properties[i]);
    }
    return constraints;
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
  public static Builder startPath(
      @Nonnull Context ctx,
      @Nonnull Set<Location> origins,
      @Nonnull Location location,
      @Nonnull Invariant condition,
      @Nonnull PrefixSpace prefix) {
    Stack<Location> locationStack = new Stack<>();
    locationStack.push(location);
    Stack<Invariant> propertyStack = new Stack<>();
    propertyStack.push(condition);
    return new Builder(
        ctx.tbdd(),
        ctx.imports(),
        ctx.exports(),
        prefix,
        ctx.checkedAssumptions(),
        ctx.enforcedAssumptions(),
        origins,
        locationStack,
        propertyStack,
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

  public boolean isGoodPathModified() {
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
    Invariant inferredWithOutProtocolHistory =
        new Invariant(
            context.tbdd,
            properties[properties.length - 1]
                .getBDDCopy()
                .existEq(context.tbdd.getOriginalRoute().getProtocolHistory().support()));
    boolean result = !initial.isFalse() && inferredWithOutProtocolHistory.impliedBy(initial);
    initialAssumption.free();
    return result;
  }

  private String relevantAttributes() {
    BDDRoute route = context.tbdd.getOriginalRoute();
    BDD incoming = properties[properties.length - 1].getBDDCopy();
    BDD support = incoming.support();
    Set<String> attr = new HashSet<>();
    if (support.testsVars(route.getPrefix().support())) {
      attr.add("Prefix");
    }
    if (support.testsVars(route.getPrefixLength().support())) {
      attr.add("Prefix Length");
    }
    if (support.testsVars(route.getAsPathRegexAtomicPredicates().support())) {
      attr.add("AS Path");
    }
    if (support.testsVars(context.tbdd.getFactory().andAll(route.getCommunityAtomicPredicates()))) {
      attr.add("Communities");
    }
    if (support.testsVars(route.getAsPathLength().support())) {
      attr.add("AS Path Length");
    }
    if (support.testsVars(route.getNextHop().support())) {
      attr.add("Next Hop");
    }
    if (support.testsVars(route.getLocalPref().support())) {
      attr.add("Local Pref");
    }
    if (support.testsVars(route.getMed().support())) {
      attr.add("MED");
    }
    if (support.testsVars(route.getWeight().support())) {
      attr.add("Weight");
    }
    if (support.testsVars(route.getProtocolHistory().support())) {
      attr.add("Protocol History");
    }
    return "Relevant Attributes: " + String.join(", ", attr);
  }

  public String displayStartCondition() {
    Location start = steps[steps.length - 1];
    Invariant cond = properties[properties.length - 1];
    String str = cond.toString();
    String attr = relevantAttributes();
    if (str.startsWith("LIMIT")) {
      return "[" + start.toUniqueString() + "] " + attr;
    } else {
      return "[" + start.toUniqueString() + "] " + str + " (" + attr + ")";
    }
  }

  // TODO improve
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

  // TODO improve
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

    // checked assumptions should just store the origins that we want to consider
    if (!context.checkedAssumptions.containsKey(steps[steps.length - 1])) {
      throw new BatfishException(
          "Expect there to be some assumption that we can used to get counterexample, but it is not there. Current path: "
              + builder);
    }

    // the assumptions used here should be the assumptions that we want checked
    BDD currentAssumption = context.checkedAssumptions.get(steps[steps.length - 1]).getBDD();
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

  /// Returns a map from each node on the path to an invariant representing the routes that can
  /// reach the node along this path
  public Map<Node, Invariant> reachableRoutes() {
    Invariant curr = new Invariant(context.tbdd, context.prefixSpaceToBDD(prefix));
    ImmutableMap.Builder<Node, Invariant> result = new ImmutableMap.Builder<>();
    // the path is in reverse order so start at the end
    int i = steps.length - 1;
    while (i > 0) {
      Location loc = steps[i];
      if (loc instanceof Node) {
        i--;
        continue;
      }
      Edge edge = (Edge) loc;
      if (context.checkedAssumptions.containsKey(edge)) {
        // the edge is coming from outside the network so use its assumption
        curr.free();
        curr = context.checkedAssumptions.get(loc).copy().postExport(edge.isEBGP());
      } else {
        // the edge is internal so do a strongest post computation
        RoutingPolicy exportPolicy = context.exports.get(edge);
        if (exportPolicy != null) {
          curr = curr.strongestPostcondition(exportPolicy);
        }
        // we need to account for the export transformations that BGP does, to
        // convert curr to an invariant on the routes that the importer will receive
        curr = curr.postExport(edge.isEBGP());
      }
      RoutingPolicy importPolicy = context.imports.get(edge);
      if (importPolicy != null) {
        curr = curr.strongestPostcondition(importPolicy);
      }
      // store a copy: the transformations applied on the next iteration consume curr in place,
      // which would otherwise corrupt the invariant recorded for this node
      result.put((Node) steps[i - 1], curr.copy());
      // since this is an edge the previous step must be a node, so we can skip it and move to the
      // next edge
      i -= 2;
    }
    return result.build();
  }

  /// A partial path means we've inferred false somewhere (stopping traffic)
  public boolean isPartialPath() {
    for (Invariant inv : properties) {
      if (inv.isFalse()) {
        return true;
      }
    }
    return false;
  }

  private boolean failsLocalCheck(Invariant pre, Invariant post, @Nullable RoutingPolicy policy) {
    if (policy == null) {
      return !pre.implies(post);
    } else {
      Invariant wp = post.weakestPrecondition(policy, false);
      boolean check = pre.implies(wp);
      wp.free();
      return !check;
    }
  }

  public boolean sanity() {
    for (int i = 1; i < steps.length; i++) {
      Invariant post = properties[i - 1];
      Invariant pre = properties[i];
      if (steps[i - 1] instanceof Edge outgoing && steps[i] instanceof Node) {
        if (failsLocalCheck(pre, post, this.context.exports.get(outgoing))) {
          return false;
        }
      } else if (steps[i - 1] instanceof Node && steps[i] instanceof Edge incoming) {
        if (failsLocalCheck(pre, post, this.context.imports.get(incoming))) {
          return false;
        }
      }
    }
    return true;
  }

  public Location getStartingPoint() {
    return steps[steps.length - 1];
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

    private final @Nonnull Set<Location> origins;
    private final @Nonnull Stack<Invariant> properties;
    private final @Nonnull PrefixSpace prefix;

    private Builder(
        @Nonnull TransferBDD tbdd,
        @Nonnull Map<Edge, RoutingPolicy> imports,
        @Nonnull Map<Edge, RoutingPolicy> exports,
        @Nonnull PrefixSpace prefix,
        @Nonnull Map<Location, Invariant> checkedAssumptions,
        @Nonnull Map<Location, Invariant> enforcedAssumptions,
        @Nonnull Set<Location> origins,
        @Nonnull Stack<Location> steps,
        @Nonnull Stack<Invariant> properties,
        @Nullable Invariant default_assumption) {
      this.tbdd = tbdd;
      this.imports = ImmutableMap.copyOf(imports);
      this.exports = ImmutableMap.copyOf(exports);
      this.prefix = prefix;
      this.checkedAssumptions = ImmutableMap.copyOf(checkedAssumptions);
      this.enforcedAssumptions = ImmutableMap.copyOf(enforcedAssumptions);
      this.steps = new Stack<>();
      steps.forEach(loc -> this.steps.push(loc.copy()));
      // important to copy because we free up bdds
      this.properties = new Stack<>();
      properties.forEach(p -> this.properties.push(p.copy()));
      this.origins = origins.stream().map(Location::copy).collect(Collectors.toSet());
      this.default_assumption =
          default_assumption == null ? new Invariant(tbdd) : default_assumption.copy();
    }

    /// Creates a copy of this builder (used for path exploration)
    public Builder copy() {
      // constructor makes deep copies
      return new Builder(
          this.tbdd,
          this.imports,
          this.exports,
          this.prefix,
          this.checkedAssumptions,
          this.enforcedAssumptions,
          this.origins,
          this.steps,
          this.properties,
          this.default_assumption);
    }

    /// Boolean indicating if this proposed step is valid, no updates made
    private boolean canTakeStep(Location step) {
      if (steps.isEmpty()) {
        return true;
      } else {
        Location currentLocation = steps.peek();
        if (step instanceof Edge edge && currentLocation instanceof Node node) {
          // Optional<Edge> lastEdge = Optional.empty();
          // if (steps.size() >= 2 && steps.elementAt(steps.size() - 2).copy() instanceof Edge e) {
          // lastEdge = Optional.of(e);
          // }
          return edge.isDst(node) // this edge leads to this node
              && !steps.contains(edge.getSrcNode()) // not crossing back over edge
              && !steps.contains(edge); // have no previously crossed this edge
        } else if (step instanceof Node node && currentLocation instanceof Edge edge) {
          // edge came from node and we haven't visited this node yet
          return edge.isSrc(node) && !steps.contains(node);
        } else {
          // otherwise we have node -> node or edge -> edge which cannot work
          return false;
        }
      }
    }

    /// Determines if path is a dead end (i.e. recent inferred invariant is false)
    public boolean deadPath() {
      return !this.properties.isEmpty() && this.properties.peek().isFalse();
    }

    /// Creates the Path object for this builder.
    public Path build() {
      Location[] locations = new Location[steps.size()];
      steps.copyInto(locations);
      Invariant[] predicates = new Invariant[properties.size()];
      properties.copyInto((predicates));
      return new Path(
          locations,
          predicates,
          new Context(
              tbdd, checkedAssumptions, enforcedAssumptions, imports, exports, default_assumption),
          prefix);
    }

    ///  Takes the provided step, if possible (includes inference). Modifies this.
    public boolean takeStep(Location step) {
      if (this.canTakeStep(step)) {
        RoutingPolicy policy;
        if (this.previous() instanceof Edge prev && step instanceof Node) {
          policy = exports.getOrDefault(prev, null);
        } else if (this.previous() instanceof Node && step instanceof Edge next) {
          policy = imports.getOrDefault(next, null);
        } else {
          throw new BatfishException("Should be unreachable, given that canTakeStep is true.");
        }
        Invariant post = properties.peek().copy();
        steps.push(step);
        properties.push(policy == null ? post.copy() : post.weakestPrecondition(policy, false));
        return true;
      } else {
        return false;
      }
    }

    /// Returns the previous step in path, if not empty. When a path is done, this will get you the
    /// start of the path which leads to the start location/property
    public Location previous() {
      if (steps.isEmpty()) {
        throw new BatfishException(
            "This should be unreachable - a path should always have destination.");
      } else {
        return steps.peek().copy();
      }
    }

    public void free() {
      this.properties.forEach(Invariant::free);
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

  public Location[] getLocations() {
    return steps;
  }
}
