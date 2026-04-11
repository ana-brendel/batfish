package org.batfish.minesweeper.question.verificationutilities;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class InferenceLoopQueue {
  private final LinkedList<Location> queue = new LinkedList<>();
  private final Map<Location, Boolean> inQueue = new HashMap<>();
  private final Map<Location, List<Location>> predecessors = new HashMap<>();

  public InferenceLoopQueue() {}

  // Adds element to end of queue (only if not in queue) and sets the flag in the `inQueue` map to
  // true. If the location that should be prioritized over it is not set, set that.
  /// Add location to the queue.
  public void add(@Nonnull Location location) {
    // set what the predecessors of the different locations
    if (location instanceof Edge edge && !predecessors.containsKey(edge)) {
      Node dst = edge.getDstNode();
      if (dst != null) {
        predecessors.put(edge, List.of(dst));
      }
    } else if (location instanceof Node node && !predecessors.containsKey(node)) {
      predecessors.put(node, node.getAllOutgoingEdges().stream().map(e -> (Location) e).toList());
    }
    // if this location is not already in the queue, add to queue and set `inQueue` flag to true
    if (!this.contains(location)) {
      inQueue.put(location, true);
      queue.add(location);
    }
  }

  // Sets the element to not be in queue and return. Does not modify the queue.
  private Location setInQueueFalse(Location location) {
    inQueue.put(location, false);
    return location;
  }

  /// Remove the next element from the queue. If there is a location later in the queue that will
  /// potentially affect the inferred invariant at the head of the queue, then we remove that more
  /// preferred element (leaving the head of the queue the same).
  public Location remove() {
    Location peek = queue.peek();
    if (this.contains(peek)) {
      Location next = null;
      for (Location higherPriority : predecessors.getOrDefault(peek, List.of())) {
        if (this.contains(higherPriority)) {
          if (next == null) {
            next = higherPriority;
          } else {
            queue.addFirst(higherPriority);
          }
        }
      }
      if (next != null) {
        return this.setInQueueFalse(next);
      } else {
        return this.setInQueueFalse(queue.remove());
      }
    } else {
      // head of queue was pre-emptively removed
      queue.remove();
      return this.remove();
    }
  }

  /// Returns if the queue is empty
  public boolean isEmpty() {
    return queue.isEmpty();
  }

  /// Checks if this element is in the queue
  public boolean contains(Location location) {
    return location != null && inQueue.getOrDefault(location, false);
  }

  /// Empty the queue
  public void clear() {
    this.queue.clear();
    this.inQueue.clear();
    this.predecessors.clear();
  }
}
