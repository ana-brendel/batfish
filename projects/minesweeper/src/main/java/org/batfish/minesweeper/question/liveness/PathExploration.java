package org.batfish.minesweeper.question.liveness;

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

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class PathExploration {
  private final Map<Node, Pair<Edge, Integer>> shortest = new HashMap<>();

  private final Path.Context context;
  private final PrefixSpace prefix;
  private final Location location;
  private final Invariant target;

  private final Set<Location> origins = new HashSet<>();

  private final Map<RoutingPolicy, List<TransferReturn>> computedPathsCache;

  public PathExploration(
      Path.Context context,
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Set<Edge> ingress,
      Map<RoutingPolicy, List<TransferReturn>> computedPathsCache) {
    this.context = context;
    this.prefix = prefix;
    this.location = location;
    this.target = target;
    this.computedPathsCache = computedPathsCache;
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

  private Location[] getPath(Location start) {
    LinkedList<Location> path = new LinkedList<>();
    Node origin = null;
    Node nextNode;
    if (start instanceof Edge edge) {
      path.addFirst(edge);
      nextNode = edge.getDstNode();
      origin = edge.getSrcNode();
    } else {
      assert start instanceof Node;
      nextNode = (Node) start;
    }
    if (nextNode == null) {
      return new Location[0];
    }
    Pair<Edge, Integer> next = shortest.get(nextNode);
    while (next.getValue() > 0) {
      if (nextNode.equals(origin)) {
        // if there is some loop detected from starting point, disregard
        return new Location[0];
      }
      assert next.getKey().hasSrcNode();
      path.addFirst(next.getKey().getSrcNode());
      path.addFirst(next.getKey());
      nextNode = next.getKey().getDstNode();
      assert nextNode != null;
      next = shortest.get(nextNode);
    }
    path.addFirst(nextNode);
    if (next.getKey() != null) {
      path.addFirst(next.getKey());
    }
    assert noLoops(path);
    if (!path.isEmpty() && path.getFirst().equals(this.location)) {
      Location[] arr = new Location[path.size()];
      return path.toArray(arr);
    } else {
      // returns null if no topological path to target
      return new Location[0];
    }
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

  private List<Location[]> populateShortestPaths() {
    List<Location[]> potentialPaths = new LinkedList<>();
    Queue<Location> working = new LinkedList<>();
    // populate the target destination
    if (this.location instanceof Edge edge) {
      Node src = edge.getSrcNode();
      working.add(src);
      shortest.put(src, Pair.of(edge, 0));
    } else {
      assert this.location instanceof Node;
      working.add(this.location);
      shortest.put((Node) this.location, Pair.of(null, 0));
    }
    // start working through all locations
    Set<Location> startingPoints = new HashSet<>(this.origins);
    while (!working.isEmpty()) {
      Location current = working.remove();
      if (startingPoints.contains(current)) {
        // we remove from starting points to only ever consider each start once
        startingPoints.remove(current);
        Location[] steps = getPath(current);
        if (steps.length > 0) {
          potentialPaths.add(steps);
        }
      }
      if (current instanceof Edge edge && edge.getSrcNode() != null) {
        Node last = edge.getDstNode();
        Pair<Edge, Integer> lastShortest = shortest.get(last);
        assert lastShortest != null;
        Node next = edge.getSrcNode();
        Pair<Edge, Integer> nextShortest = shortest.get(next);
        if (nextShortest == null || lastShortest.getValue() + 1 < nextShortest.getValue()) {
          shortest.put(next, Pair.of(edge, lastShortest.getValue() + 1));
          if (!working.contains(next)) {
            working.add(next);
          }
        }
      } else if (current instanceof Node node) {
        working.addAll(node.getAllIncomingEdges());
      }
    }
    return potentialPaths;
  }

  public Pair<Path, Set<Path>> run() {
    // populates shortest paths and gets potential paths
    List<Location[]> potentialPaths = populateShortestPaths();
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
