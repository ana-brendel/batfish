package org.batfish.minesweeper.question.liveness;

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

  private Location[] getPath(Location start) {
    LinkedList<Location> path = new LinkedList<>();
    Node nextNode;
    if (start instanceof Edge edge) {
      path.addFirst(edge);
      nextNode = edge.getDstNode();
    } else {
      assert start instanceof Node;
      nextNode = (Node) start;
    }
    Pair<Edge, Integer> next = shortest.get(nextNode);
    while (next.getValue() > 0) {
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
    assert path.getFirst().equals(this.location);
    assert this.origins.contains(path.getLast());
    Location[] arr = new Location[path.size()];
    return path.toArray(arr);
  }

  private Invariant[] getPathConstraints(Location[] path) {
    Invariant[] properties = new Invariant[path.length];
    properties[0] =
        new Invariant(context.tbdd(), target.getBDDCopy().and(context.prefixSpaceToBDD(prefix)));
    for (int i = 1; i < properties.length; i++) {
      Invariant post = properties[i - 1];
      Location prev = path[i - 1];
      Location curr = path[i];
      RoutingPolicy policy;
      if (prev instanceof Edge outgoing && curr instanceof Node node) {
        assert node.equals(outgoing.getSrcNode());
        policy = context.exports().get(outgoing);
      } else if (prev instanceof Node node && curr instanceof Edge incoming) {
        assert node.equals(incoming.getDstNode());
        policy = context.imports().get(incoming);
      } else {
        throw new BatfishException("Path is poorly constructed.");
      }
      if (policy == null || post.isFalse()) {
        properties[i] = post.copy();
      } else {
        properties[i] = post.weakestPrecondition(policy, false, computedPathsCache);
      }
    }
    return properties;
  }

  public Pair<Path, Set<Path>> run() {
    Set<Path> badPaths = new HashSet<>();
    Queue<Location> working = new LinkedList<>();
    if (this.location instanceof Edge edge) {
      Node src = edge.getSrcNode();
      working.add(src);
      shortest.put(src, Pair.of(edge, 0));
    } else {
      assert this.location instanceof Node;
      working.add(this.location);
      shortest.put((Node) this.location, Pair.of(null, 0));
    }
    Set<Location> startingPoints = new HashSet<>(this.origins);
    while (!working.isEmpty()) {
      Location current = working.remove();
      if (startingPoints.isEmpty()) {
        break;
      } else if (startingPoints.contains(current)) {
        startingPoints.remove(current);
        Location[] steps = getPath(current);
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
      } else if (current instanceof Edge edge && edge.getSrcNode() != null) {
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
    return Pair.of(null, badPaths);
  }
}
