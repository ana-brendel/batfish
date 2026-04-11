package org.batfish.minesweeper.question.liveness;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

public class PathAnalyzer {
  private static final Logger LOGGER = LogManager.getLogger(PathAnalyzer.class);

  private final Path.Context context;
  private final PrefixSpace prefix;
  private final Location location;
  private final Invariant target;

  private final Set<Location> origins = new HashSet<>();

  public PathAnalyzer(
      @Nonnull Path.Context context,
      @Nonnull PrefixSpace prefix,
      @Nonnull Location location,
      @Nonnull Invariant target) {
    this.context = context;
    this.prefix = prefix;
    this.location = location;
    this.target = target;
    // automatically sets potential origins to checked assumptions
    origins.addAll(context.checkedAssumptions().keySet());
  }

  /**
   * Returns a pair where at most one of the arguments is present. The first element in the pair is
   * an optional path, that if present corresponds to a good path that traffic can take to each the
   * target location and satisfy the liveness property. If this path is empty, then there are no
   * good paths, and there should be some incomplete or interfering path returned. (Only returns
   * incomplete paths/paths that inferred false if no interfering/complete paths.)
   *
   * @return a good path or list of interfering/incomplete paths
   */
  public Pair<Optional<Path>, List<Path>> run() {
    return this.run(Set.of());
  }

  /**
   * Returns a pair where at most one of the arguments is present. The first element in the pair is
   * an optional path, that if present corresponds to a good path that traffic can take to each the
   * target location and satisfy the liveness property. If this path is empty, then there are no
   * good paths, and there should be some incomplete or interfering path returned. (Only returns
   * incomplete paths/paths that inferred false if no interfering/complete paths.)
   *
   * @param ingress Potential starting points for path (default if empty is any incoming edge)
   * @return a good path or list of interfering/incomplete paths
   */
  public Pair<Optional<Path>, List<Path>> run(@Nonnull Set<Edge> ingress) {
    // if ingress locations specified, make sure the origin is updated
    if (!ingress.isEmpty()) {
      this.origins.clear();
      this.origins.addAll(ingress);
    }

    LOGGER.info("Ingress locations: {}", this.origins.toString());

    // should not happen, but if no prefix, report issue
    if (prefix.isEmpty()) {
      throw new BatfishException(
          "PathAnalyzer.generateGoodPaths() - Prefix space is empty, cannot perform liveness analysis.");
    }

    // determine the set of good paths (incorporating the prefix)
    Invariant goodPathCondition =
        new Invariant(context.tbdd(), target.getBDDCopy().and(context.prefixSpaceToBDD(prefix)));

    // if this is unsatisfiable, no need to run inference
    if (goodPathCondition.isFalse()) {
      // no possible route exists that matches the prefix and target property
      return Pair.of(Optional.empty(), List.of());
    }

    // search for good path
    List<Path> interferingPaths = new LinkedList<>();
    List<Path> incompletePaths = new LinkedList<>();
    Path.Builder starter =
        Path.startPath(
            this.context, this.origins, this.location.copy(), goodPathCondition, this.prefix);
    Queue<Path.Builder> working = new Queue<>(starter);
    while (!working.isEmpty()) {
      Path.Builder curr = working.pull();
      Location prev = curr.previous();
      LOGGER.info("Currently at: {}", prev);
      if (this.origins.contains(prev)) {
        Optional<Path> update = atOrigin(curr, interferingPaths, incompletePaths);
        if (update.isPresent()) {
          return Pair.of(update, List.of());
        }
      } else if (prev instanceof Edge edge && edge.hasSrcNode()) {
        // we only want to continue the path if there is a node within network, otherwise it should
        // be starting point -- only one next step, so no need to make a copy
        if (curr.takeStep(edge.getSrcNode())) {
          // this means that the curr path was modified and we took step
          if (curr.deadPath()) {
            // inferred false, meaning cannot reach through this path
            Path dead = curr.build();
            assert dead.isPartialPath();
            incompletePaths.add(dead);
          } else if (this.closerToOrigin(curr.previous())) {
            // we can keep exploring this path, add to front if closer to origin (simple check)
            working.queueToFront(curr);
          } else {
            working.queue(curr);
          }
        } else {
          // cannot continue, so we can free
          curr.free();
        }
      } else if (prev instanceof Node node) {
        Set<Edge> potentialSteps = new HashSet<>();
        LOGGER.info("Incoming edges: {}", node.getAllIncomingEdges());
        for (Edge edge : node.getAllIncomingEdges()) {
          if (this.origins.contains(edge)) {
            // need to copy to update because there are potential multiple next steps
            Path.Builder toUpdate = curr.copy();
            // we are at a starting point, so we should check we can make step
            if (toUpdate.takeStep(edge)) {
              // we can take step, so we update accordingly
              Optional<Path> update = atOrigin(toUpdate, interferingPaths, incompletePaths);
              if (update.isPresent()) {
                // TODO maybe keep interfering paths as sources of interference to check
                return Pair.of(update, List.of());
              }
            } else {
              // we can't take step, so we can free
              toUpdate.free();
            }
          } else {
            // deprioritize these steps, do after checking if any are at origin
            potentialSteps.add(edge);
          }
        }
        // we went through the loop, found no complete paths
        potentialSteps.forEach(
            edge -> {
              Path.Builder toUpdate = curr.copy();
              if (toUpdate.takeStep(edge)) {
                // we could take step, so check if dead
                if (toUpdate.deadPath()) {
                  // if inferred false, add to partial paths
                  Path dead = toUpdate.build();
                  assert dead.isPartialPath();
                  if (incompletePaths.size() < 5) {
                    incompletePaths.add(dead);
                  } else {
                    dead.freeBDDs();
                  }
                } else if (this.closerToOrigin(toUpdate.previous())) {
                  // we can keep exploring this path, add to front if closer to origin (simple
                  // check)
                  working.queueToFront(toUpdate);
                } else {
                  working.queue(toUpdate);
                }
              } else {
                // step didn't work, so we can free
                toUpdate.free();
              }
            });
        // can free because we've made copies of the BDDs
        curr.free();
      } else {
        // this is an edge that we do not have a config for its source, nor is it a potential
        // starting point, so it is dead end
        continue;
      }
    }
    // exited while loop with no good path
    if (interferingPaths.isEmpty()) {
      return Pair.of(Optional.empty(), incompletePaths);
    } else {
      incompletePaths.forEach(Path::freeBDDs);
      return Pair.of(Optional.empty(), interferingPaths);
    }
  }

  ///  Handles checking when path is at an origin, assumes this has been checked before called
  private Optional<Path> atOrigin(
      Path.Builder builder, List<Path> interferingPaths, List<Path> incompletePaths) {
    assert this.origins.contains(builder.previous());
    // if this path starts at an origin, we check if it is good
    Path path = builder.build();
    if (path.isGoodPath()) {
      // clear used BDDs, return good path
      // TODO maybe keep interfering paths, because these could be sources of interference to check
      interferingPaths.forEach(Path::freeBDDs);
      incompletePaths.forEach(Path::freeBDDs);
      return Optional.of(path);
    } else if (path.isPartialPath() && incompletePaths.size() < 5) {
      // add partial path to list, if there are less than 5 saved
      incompletePaths.add(path);
    } else if (!path.isPartialPath() && interferingPaths.size() < 5) {
      // add bad path to list, if there are less than 5 saved
      interferingPaths.add(path);
    } else {
      path.freeBDDs();
    }
    return Optional.empty();
  }

  private boolean closerToOrigin(Location step) {
    if (this.origins.contains(step)) {
      return true;
    } else if (step instanceof Node node) {
      return node.getAllIncomingEdges().stream().anyMatch(this.origins::contains);
    } else if (step instanceof Edge edge && edge.getSrcNode() != null) {
      return this.origins.contains(edge.getSrcNode())
          || edge.getSrcNode().getAllIncomingEdges().stream().anyMatch(this.origins::contains);
    } else {
      return false;
    }
  }

  private static class Queue<T> {
    private final LinkedList<T> elements = new LinkedList<>();

    private Queue(T start) {
      elements.add(start);
    }

    public void queue(T element) {
      elements.addLast(element);
    }

    public void queueToFront(T element) {
      LOGGER.info("Adding front to queue: {}", element);
      elements.addFirst(element);
    }

    public T pull() {
      return elements.removeFirst();
    }

    public boolean isEmpty() {
      return elements.isEmpty();
    }
  }
}
