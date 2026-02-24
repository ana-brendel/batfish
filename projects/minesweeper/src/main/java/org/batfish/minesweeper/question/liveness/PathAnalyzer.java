package org.batfish.minesweeper.question.liveness;

import org.apache.commons.lang3.tuple.Pair;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;

public class PathAnalyzer {
  private final Path.Context context;

  private final PrefixSpace prefix;
  private final Location location;
  private final Invariant target;

  private final Map<Ip, Node> nodes;
  private final Map<Node, Set<Edge>> edgesByDestination;

  public PathAnalyzer(
      @Nonnull Path.Context context,
      @Nonnull PrefixSpace prefix,
      @Nonnull Location location,
      @Nonnull Invariant target,
      @Nonnull Map<Ip, Node> nodes,
      @Nonnull Map<Node, Set<Edge>> edgesByDestination) {
    this.context = context;
    this.prefix = prefix;
    this.location = location;
    this.target = target;
    this.nodes = nodes;
    this.edgesByDestination = edgesByDestination;
  }

  /// Based on potential paths provided, see if there is at least one which satisfies the liveness
  // property (is a good path)
  private Pair<Optional<Path>, List<Path>> generateGoodPaths(
      @Nonnull List<Path.Builder> potentialPaths, Edge ingress) {
    if (prefix.isEmpty()) {
      throw new BatfishException(
          "PathAnalyzer.generateGoodPaths() - Prefix space is empty, cannot perform liveness analysis.");
    }
    Invariant condition =
        new Invariant(context.tbdd(), target.getBDDCopy().and(context.prefixSpaceToBDD(prefix)));

    if (condition.isFalse()) {
      // no possible route exists that matches the prefix and target property
      return Pair.of(Optional.empty(), List.of());
    }

    List<Path> badPaths = new LinkedList<>();
    for (Path.Builder builder : potentialPaths) {
      // if there is an ingress node provided, we only want to try paths which start from there
      if (ingress == null || builder.previous().map(ingress::equals).orElse(false)) {
        Path path = builder.build(location, condition.copy(), this.prefix);
        if (path != null && path.isGoodPath()) {
          // can free the BDDs in the bad paths
          badPaths.forEach(Path::freeBDDs);
          return Pair.of(Optional.of(path), List.of());
        } else if (path != null && badPaths.size() < 5) {
          // only keep up to the 5 shortest possible paths to report
          badPaths.add(path);
        } else if (path != null) {
          // can free the BDDs in any leftover bad paths
          path.freeBDDs();
        }
      }
    }
    return Pair.of(Optional.empty(), badPaths);
  }

  /// Returns set of possible paths from ingress node to the target properties location
  private List<Path.Builder> generatePathBuilders() {
    Set<Path.Builder> paths = new HashSet<>();
    Queue<Path.Builder> working = new LinkedList<>();
    Path.Builder starter = Path.builder(context);
    starter.addToPath(location.copy());
    working.add(starter);
    while (!working.isEmpty()) {
      Path.Builder curr = working.remove();
      Optional<Location> prev = curr.previous();
      if (prev.isEmpty()) {
        throw new BatfishException(
            "PathAnalyzer.generatePathBuilders() - This should be unreachable.");
      } else if (context.assumptions().containsKey(prev.get())) {
        paths.add(curr);
      } else if (prev.get() instanceof Edge edge && nodes.containsKey(edge.getSrc())) {
        // source node of edge is still in network so we just there, if valid path
        if (curr.addToPath(nodes.get(edge.getSrc()))) {
          working.add(curr);
        }
      } else if (prev.get() instanceof Edge) {
        // this means this edge comes from outside, so we've reach edge of network so add to result
        paths.add(curr);
      } else if (prev.get() instanceof Node node) {
        // this means we are at a node, so we need to expand outwards
        Set<Edge> potentialSteps = edgesByDestination.get(node);
        working.addAll(curr.expand(potentialSteps));
      }
    }
    // filters out any paths which don't start at an assumption and then sorts by the length of the
    // path
    return paths.stream()
        .filter(
            p -> p.previous().isPresent() && context.assumptions().containsKey(p.previous().get()))
        .sorted()
        .toList();
  }

  /// Returns (if it exists) a good path that satisfies the liveness property in question. Note,
  /// this is a Path object so the necessary invariants have been inferred, and we've checked that
  /// the ingress assumptions satisfies the inferred ingress invariant.
  public Pair<Optional<Path>, List<Path>> run() {
    return this.run(null);
  }

  public Pair<Optional<Path>, List<Path>> run(Edge ingress) {
    List<Path.Builder> potentialPaths = this.generatePathBuilders();
    return this.generateGoodPaths(potentialPaths, ingress);
  }
}
