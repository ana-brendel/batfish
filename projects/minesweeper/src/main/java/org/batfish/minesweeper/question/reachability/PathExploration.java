package org.batfish.minesweeper.question.reachability;

import net.sf.javabdd.BDD;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.utils.Tuple;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class PathExploration {
  private final Path.Context context;
  private final PrefixSpace prefix;
  private final Location location;
  private final Invariant target;

  private final Set<Location> origins = new HashSet<>();

  private final Map<Tuple<String,RoutingPolicy>, List<TransferReturn>> computedPathsCache;

  private final BgpPathValidity validity;

  public PathExploration(
      Path.Context context,
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Set<Edge> ingress,
      Map<Tuple<String,RoutingPolicy>, List<TransferReturn>> computedPathsCache) {
    this.context = context;
    this.prefix = prefix;
    this.location = location;
    this.target = target;
    this.computedPathsCache = computedPathsCache;
    this.validity = new BgpPathValidity(context.imports(), context.exports());
    // automatically sets potential origins to checked assumptions
    if (ingress.isEmpty()) {
      origins.addAll(context.checkedAssumptions().keySet());
    } else {
      origins.addAll(ingress);
    }
  }

  /// NOTE -- only included for assert, only ran during testing
  private static boolean noLoops(LinkedList<Location> path) {
    LinkedList<Location> copy = new LinkedList<>(path);
    while (!copy.isEmpty()) {
      Location head = copy.remove();
      if (copy.contains(head)) {
        return false;
      }
    }
    return true;
  }

  /// Returns the first path found from the given location to the target, or an empty array if
  /// there is none
  private Location[] getPath(Location start) {
    List<Location[]> paths = searchPaths(Set.of(start));
    return paths.isEmpty() ? new Location[0] : paths.get(0);
  }

  /// A path being extended backward from the target: its locations from the target to its first
  /// node, the nodes on it, and what BGP loop prevention requires of edges that extend it
  private record PartialPath(List<Location> steps, Set<Node> nodes, BgpPathValidity.Suffix suffix) {
    Node first() {
      return (Node) steps.get(steps.size() - 1);
    }

    Location[] extendTo(Location... more) {
      Location[] path = steps.toArray(new Location[steps.size() + more.length]);
      System.arraycopy(more, 0, path, steps.size(), more.length);
      return path;
    }
  }

  /// Searches backward from the target, in order of path length, for paths that BGP's loop
  /// prevention allows (see BgpPathValidity), and returns the first path found from each of the
  /// given origins. Paths are ordered from the target back to the origin and never repeat a node.
  ///
  /// To bound the search, a path is not extended if a shorter path from the same node allows every
  /// extension it does, as far as the loop-prevention rules are concerned (see
  /// BgpPathValidity.Suffix). This can miss a path when the shorter one cannot continue only because
  /// the continuation would repeat one of its nodes. That should be rare: the repeated node's AS is
  /// usually already checked along the longer path, so loop detection rejects the continuation
  /// there too. Exceptions involve unknown ASes, allowas-in, or a router using different local ASes
  /// on different sessions, and may grow if route reflection is modeled.
  private List<Location[]> searchPaths(Set<Location> startingPoints) {
    Set<Location> remaining = new HashSet<>(startingPoints);
    List<Location[]> found = new LinkedList<>();
    Map<Node, List<BgpPathValidity.Suffix>> seen = new HashMap<>();
    Queue<PartialPath> working = new LinkedList<>();

    // the route is sent on a target edge but not imported, so the target edge is not checked as
    // a receiver
    if (this.location instanceof Edge edge) {
      if (remaining.remove(edge)) {
        found.add(new Location[] {edge});
      }
      Node src = edge.getSrcNode();
      if (src != null) {
        BgpPathValidity.Suffix suffix =
            validity.extend(BgpPathValidity.Suffix.EMPTY, edge, true);
        assert suffix != null;
        visit(working, seen, remaining, found, List.of(edge), Set.of(), src, suffix);
      }
    } else {
      assert this.location instanceof Node;
      visit(
          working,
          seen,
          remaining,
          found,
          List.of(),
          Set.of(),
          (Node) this.location,
          BgpPathValidity.Suffix.EMPTY);
    }

    while (!working.isEmpty() && !remaining.isEmpty()) {
      PartialPath current = working.remove();
      List<Edge> incoming =
          current.first().getAllIncomingEdges().stream()
              .sorted(Comparator.comparing(Edge::toUniqueString))
              .toList();
      for (Edge edge : incoming) {
        BgpPathValidity.Suffix suffix = validity.extend(current.suffix(), edge, false);
        if (suffix == null) {
          continue;
        }
        Node src = edge.getSrcNode();
        if (src != null && current.nodes().contains(src)) {
          // the edge comes from a node already on the path
          continue;
        }
        if (remaining.remove(edge)) {
          Location[] path = current.extendTo(edge);
          assert noLoops(new LinkedList<>(Arrays.asList(path)));
          found.add(path);
        }
        if (src != null) {
          List<Location> steps = new ArrayList<>(current.steps());
          steps.add(edge);
          visit(working, seen, remaining, found, steps, current.nodes(), src, suffix);
        }
      }
    }
    return found;
  }

  /// Adds the node to the front of a partial path and queues it for extension, unless a shorter
  /// path from the node already allows every extension this one does
  private static void visit(
      Queue<PartialPath> working,
      Map<Node, List<BgpPathValidity.Suffix>> seen,
      Set<Location> remaining,
      List<Location[]> found,
      List<Location> steps,
      Set<Node> nodes,
      Node node,
      BgpPathValidity.Suffix suffix) {
    List<BgpPathValidity.Suffix> seenAtNode = seen.computeIfAbsent(node, k -> new ArrayList<>());
    if (seenAtNode.stream().anyMatch(s -> s.weakerThan(suffix))) {
      return;
    }
    seenAtNode.add(suffix);
    List<Location> extended = new ArrayList<>(steps);
    extended.add(node);
    Set<Node> extendedNodes = new HashSet<>(nodes);
    extendedNodes.add(node);
    PartialPath partial = new PartialPath(extended, extendedNodes, suffix);
    if (remaining.remove(node)) {
      found.add(partial.extendTo());
    }
    working.add(partial);
  }

  private Invariant[] getPathConstraints(Location[] path) {
    Invariant[] properties = new Invariant[path.length];
    properties[0] =
        new Invariant(context.tbdd(), target.getBDDCopy().and(context.prefixSpaceToBDD(prefix)));
    for (int i = 1; i < properties.length; i++) {
      Invariant post = properties[i - 1];
      Location prev = path[i - 1];
      Location curr = path[i];
      RoutingPolicy policy = getPolicy(prev, curr);
      if (policy == null || post.isFalse()) {
        properties[i] = post.copy();
      } else {
        properties[i] = post.weakestPrecondition(policy, false, computedPathsCache);
      }
    }
    return properties;
  }

  public Pair<Path, Set<Path>> run() {
    List<Location[]> potentialPaths = searchPaths(this.origins);
    Set<Path> badPaths = new HashSet<>();
    for (Location[] steps : potentialPaths) {
      assert this.origins.contains(steps[steps.length - 1]);
      // This is where we are more generous with constraints
      Invariant[] properties = getPathConstraints(steps);
      Path path = Path.create(steps, properties, context, prefix);
      if (path.isGoodPathModified()) {
        badPaths.forEach(Path::freeBDDs);
        return Pair.of(path, Set.of());
      } else if (badPaths.size() < 5) {
        badPaths.add(path);
      } else {
        path.freeBDDs();
      }
    }
    return Pair.of(null, badPaths);
  }

  private RoutingPolicy getPolicy(Location prior, Location step) {
    if (prior instanceof Edge outgoing && step instanceof Node) {
      return context.exports().get(outgoing);
    } else if (prior instanceof Node && step instanceof Edge incoming) {
      return context.imports().get(incoming);
    } else {
      throw new BatfishException(
          "Invalid path constructed (either node followed by node or edge followed by edge)");
    }
  }

  private Set<Pair<BDD, Map<Location, Invariant>>> getReachableConditions(Node node, Edge best) {
    Set<Edge> outgoing = node.getAllOutgoingEdges();
    Set<Pair<BDD, Map<Location, Invariant>>> reachable = new HashSet<>();
    for (Edge step : outgoing) {
      if (!step.equals(best)) {
        // get the shortest path taking this edge
        Location[] alt_path = getPath(step);
        if (alt_path.length > 0) {
          // infer the weakest conditions along this path
          Invariant[] constraints = getPathConstraints(alt_path);
          // get the reachable constraint that this edge reaches and satisfies
          Invariant edgeReaches = constraints[constraints.length - 1].copy();
          // compute the weakest precondition that this node satisfies that
          RoutingPolicy policy = getPolicy(step, node);
          if (!edgeReaches.isFalse()) {
            if (policy == null) {
              Map<Location, Invariant> requiredForReachableNonInterference = new HashMap<>();
              for (int i = 1; i < constraints.length; i++) {
                requiredForReachableNonInterference.put(alt_path[i], constraints[i]);
              }
              requiredForReachableNonInterference.put(node, edgeReaches.copy());
              reachable.add(Pair.of(edgeReaches.getBDDCopy(), requiredForReachableNonInterference));
            } else {
              Invariant nodeReaches =
                  edgeReaches.weakestPrecondition(policy, false, computedPathsCache);
              if (!nodeReaches.isFalse()) {
                Map<Location, Invariant> requiredForReachableNonInterference = new HashMap<>();
                for (int i = 1; i < constraints.length; i++) {
                  requiredForReachableNonInterference.put(alt_path[i], constraints[i]);
                }
                requiredForReachableNonInterference.put(node, nodeReaches.copy());
                reachable.add(
                    Pair.of(nodeReaches.getBDDCopy(), requiredForReachableNonInterference));
              }
              nodeReaches.free();
            }
          }
          edgeReaches.free();
        }
      }
    }
    return reachable;
  }

  /// New addition after initial paper submission to weaken path constraints to improve interference
  /// checks
  public Pair<Path, Map<Location, BDD>> weakenConstraints(Location[] steps) {
    Invariant[] weakened = new Invariant[steps.length];
    Map<Location, BDD> auxiliaryRequirements = new HashMap<>();
    weakened[0] =
        new Invariant(context.tbdd(), target.getBDDCopy().and(context.prefixSpaceToBDD(prefix)));
    for (int i = 1; i < steps.length; i++) {
      RoutingPolicy policy = getPolicy(steps[i - 1], steps[i]);
      Invariant wp = weakened[i - 1].copy();
      if (policy != null && !weakened[i - 1].isFalse()) {
        wp = weakened[i - 1].weakestPrecondition(policy, false, computedPathsCache);
      }
      if (steps[i] instanceof Node node && steps[i - 1] instanceof Edge edge) {
        BDD constraint = wp.getBDD();
        Set<Pair<BDD, Map<Location, Invariant>>> otherWaysToReach =
            getReachableConditions(node, edge);
        for (Pair<BDD, Map<Location, Invariant>> temp : otherWaysToReach) {
          BDD existing = constraint.id();
          constraint.orWith(temp.getLeft());
          // only add the auxiliary path constraints if this path actually weakened the constraint
          if (!existing.equals(constraint)) {
            for (Location step : temp.getRight().keySet()) {
              if (auxiliaryRequirements.containsKey(step)) {
                auxiliaryRequirements.get(step).andWith(temp.getRight().get(step).getBDD());
              } else {
                auxiliaryRequirements.put(step, temp.getRight().get(step).getBDD());
              }
            }
          }
        }
        weakened[i] = new Invariant(context.tbdd(), constraint);
      } else {
        assert steps[i] instanceof Edge && steps[i - 1] instanceof Node : "Invalid Path";
        weakened[i] = wp;
      }
    }
    return Pair.of(Path.create(steps, weakened, context, prefix), auxiliaryRequirements);
  }
}
