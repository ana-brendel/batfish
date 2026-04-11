package org.batfish.minesweeper.question.liveness;

import net.sf.javabdd.BDD;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

public class UpdatedPathAnalyzer extends PathAnalyzer {
  // private static final Logger LOGGER = LogManager.getLogger(UpdatedPathAnalyzer.class);

  private final Path.Context context;
  private final PrefixSpace prefix;
  private final Location location;

  private final Map<Location, Invariant> origins = new HashMap<>();
  private final Map<Location, Map<Invariant, Steps>> paths = new HashMap<>();
  private final Set<Steps> interferingPaths = new HashSet<>();
  private final Set<Steps> incompletePaths = new HashSet<>();

  public UpdatedPathAnalyzer(
      @Nonnull Path.Context context,
      @Nonnull PrefixSpace prefix,
      @Nonnull Location location,
      @Nonnull Invariant target) {
    super(context, prefix, location, target);
    this.context = context;
    this.prefix = prefix;
    this.location = location;
    context
        .checkedAssumptions()
        .keySet()
        .forEach(l -> origins.put(l, initializeOriginAssumptions(l)));
    paths.computeIfAbsent(location, k -> new HashMap<>()).put(target, new Steps());
  }

  @Override
  public Pair<Optional<Path>, List<Path>> run(@Nonnull Set<Edge> ingress) {
    // if ingress locations specified, make sure the origin is updated
    if (!ingress.isEmpty()) {
      this.origins.clear();
      ingress.forEach(edge -> origins.put(edge, initializeOriginAssumptions(edge)));
    }
    return this.run();
  }

  @Override
  public Pair<Optional<Path>, List<Path>> run() {
    Path.Context updateContext =
        new Path.Context(
            this.context.tbdd(),
            this.origins, // This is what is updated so that we check the correct locations
            this.context.enforcedAssumptions(),
            this.context.imports(),
            this.context.exports(),
            this.context.default_assumption());
    Optional<Path> good =
        this.find().map(steps -> steps.createPath(updateContext, this.prefix, this.paths));
    if (good.isPresent()) {
      return Pair.of(good, List.of());
    } else if (!interferingPaths.isEmpty()) {
      return Pair.of(
          good,
          interferingPaths.stream()
              .map(steps -> steps.createPath(updateContext, this.prefix, this.paths))
              .toList());
    } else {
      return Pair.of(
          good,
          incompletePaths.stream()
              .map(steps -> steps.createPath(updateContext, this.prefix, this.paths))
              .toList());
    }
  }

  private Invariant initializeOriginAssumptions(Location origin) {
    BDD initialAssumption =
        context
            .prefixSpaceToBDD(prefix)
            .andWith(
                context
                    .checkedAssumptions()
                    .getOrDefault(origin, context.default_assumption())
                    .getBDDCopy());
    return new Invariant(
        context.tbdd(),
        initialAssumption.andWith(
            context.tbdd().getOriginalRoute().wellFormednessConstraints(true)));
  }

  private Optional<Steps> find() {
    Queue<Location> working = new LinkedList<>();
    working.add(this.location);
    while (!working.isEmpty()) {
      Location loc = working.remove();
      if (this.origins.containsKey(loc)) {
        Set<Invariant> toRemove = new HashSet<>();
        for (Invariant pathCondition : this.paths.get(loc).keySet()) {
          // if the invariant inferred is implied by the assumption, we found good path
          // TODO figure out the protocol history - Do we care if it is subset of BGP protocols?
          Invariant removeProtocolHistory =
              new Invariant(
                  this.context.tbdd(),
                  pathCondition
                      .getBDDCopy()
                      .existEq(
                          this.context.tbdd().getOriginalRoute().getProtocolHistory().support()));
          if (removeProtocolHistory.impliedBy(this.origins.get(loc))) {
            return Optional.of(this.paths.get(loc).get(pathCondition).addStepEq(loc));
          } else {
            // if this invariant is not implied by the assumption, we can remove
            toRemove.add(pathCondition);
          }
        }
        toRemove.forEach(
            inv -> {
              if (interferingPaths.size() < 5) {
                interferingPaths.add(this.paths.get(loc).get(inv));
              }
              this.paths.get(loc).remove(inv);
            });
      } else {
        // we are not at an origin, so we keep looking
        Map<Location, RoutingPolicy> nextSteps = new HashMap<>();
        if (loc instanceof Edge edge && edge.getSrcNode() != null) {
          nextSteps.put(edge.getSrcNode(), this.context.exports().get(edge));
        } else if (loc instanceof Node node) {
          for (Edge nextStep : node.getAllIncomingEdges()) {
            nextSteps.put(nextStep, this.context.imports().get(nextStep));
          }
        }

        for (Location nextStep : nextSteps.keySet()) {
          boolean addToWorkingQueue = false;
          RoutingPolicy policy = nextSteps.get(nextStep);
          for (Invariant pathCondition : this.paths.get(loc).keySet()) {
            Steps newPath = this.paths.get(loc).get(pathCondition).addStep(loc);
            if (this.updatePathStores(nextStep, policy, pathCondition, newPath)) {
              addToWorkingQueue = true;
            }
          }
          if (addToWorkingQueue && !working.contains(nextStep)) {
            working.add(nextStep);
          }
        }
      }
    }
    return Optional.empty();
  }

  /// Maintains the invariant that for a given location `step`, if a route satisfying the invariant
  /// `inv` is at the location `step`, then it can reach the target by taking the path
  /// `paths[step][inv]`
  private boolean updatePathStores(
      Location step, RoutingPolicy policy, Invariant post, Steps path) {
    if (path.canTakeStep(step)) {
      Invariant wp = policy == null ? post.copy() : post.weakestPrecondition(policy, false);
      if (wp.isFalse() && !this.origins.containsKey(step)) {
        // inferred false pre-emptively along the way
        if (incompletePaths.size() < 5) {
          incompletePaths.add(path.addStep(step));
        }
        return false;
      } else if (wp.isFalse()) {
        // at origin but we inferred false, we don't need to update paths, but this is interfering
        assert this.origins.containsKey(step);
        if (interferingPaths.size() < 5) {
          interferingPaths.add(path.addStep(step));
        }
        return false;
      } else {
        Set<Invariant> impliesThisCondition = new HashSet<>();
        for (Invariant pathCondition :
            this.paths.computeIfAbsent(step, k -> new HashMap<>()).keySet()) {
          if (wp.implies(pathCondition)) {
            // if this path can reach the target, so can the existing path
            return false;
          } else if (pathCondition.implies(wp)) {
            impliesThisCondition.add(pathCondition);
          }
        }
        paths.get(step).put(wp, path);
        impliesThisCondition.forEach(inv -> paths.get(step).remove(inv));
        return true;
      }
    } else {
      return false;
    }
  }

  private static class Steps {
    private final LinkedList<Location> steps = new LinkedList<>();

    private Steps() {}

    private Steps(LinkedList<Location> steps) {
      this.steps.addAll(steps);
    }

    private Steps addStepEq(Location next) {
      // assumes step is valid
      steps.addFirst(next);
      return this;
    }

    private Steps addStep(Location next) {
      Steps ret = new Steps(this.steps);
      return ret.addStepEq(next);
    }

    ///  No updates or modifications, just checks if we can take step (topologically)
    private boolean canTakeStep(Location step) {
      if (steps.isEmpty()) {
        return true;
      } else {
        Location currentLocation = steps.peek();
        if (step instanceof Edge edge && currentLocation instanceof Node node) {
          Optional<Edge> lastEdge = Optional.empty();
          if (steps.size() >= 2 && steps.get(1).copy() instanceof Edge e) {
            // steps = [this edge] + currentLocation, edge, ....
            lastEdge = Optional.of(e);
          }
          return edge.isDst(node) // this edge leads to this node
              && (lastEdge.isEmpty() || !lastEdge.get().equals(edge)) // not crossing back over edge
              && !steps.contains(edge) // have not previously crossed this edge (check node next)
              && (edge.getSrcNode() == null || !steps.contains(edge.getSrcNode()));
        } else if (step instanceof Node node && currentLocation instanceof Edge edge) {
          // edge came from node and we haven't visited this node yet
          return edge.isSrc(node) && !steps.contains(node);
        } else {
          // otherwise we have node -> node or edge -> edge which cannot work
          return false;
        }
      }
    }

    public Path createPath(
        Path.Context context, PrefixSpace prefix, Map<Location, Map<Invariant, Steps>> paths) {
      Location[] locationArr = new Location[steps.size()];
      AtomicInteger index = new AtomicInteger(locationArr.length - 1);
      steps
          .iterator()
          .forEachRemaining(
              step -> {
                locationArr[index.get()] = step;
                index.addAndGet(-1);
              });

      Invariant[] propertyArr = new Invariant[steps.size()];
      LinkedList<Location> togo = new LinkedList<>(steps);
      int i = propertyArr.length - 1;
      while (!togo.isEmpty()) {
        Location step = togo.remove();
        assert locationArr[i].equals(step) : "Inaccurately reconstructing path";
        // find what the invariant is based on which remaining path matches
        propertyArr[i] = null;
        for (Map.Entry<Invariant, Steps> condition : paths.get(step).entrySet()) {
          if (condition.getValue().steps.equals(togo)) {
            propertyArr[i] = condition.getKey();
            break;
          }
        }
        // if there is no condition matching the path, that means that it is a dead end
        if (propertyArr[i] == null) {
          propertyArr[i] = Invariant.getFalse(context.tbdd());
        }
        i -= 1;
      }

      // sanity check
      for (int j = 0; j < propertyArr.length - 2; j++) {
        assert !propertyArr[j].isFalse() || propertyArr[j + 1].isFalse();
      }

      return Path.create(locationArr, propertyArr, context, prefix);
    }
  }
}
