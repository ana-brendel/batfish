package org.batfish.minesweeper.question.verificationutilities;

import org.batfish.datamodel.routing_policy.RoutingPolicy;

import java.util.AbstractMap;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

public class Lightyear {
  private final Map<Edge, RoutingPolicy> imports;
  private final Map<Edge, RoutingPolicy> exports;

  public Lightyear(Map<Edge, RoutingPolicy> imports, Map<Edge, RoutingPolicy> exports) {
    this.imports = imports;
    this.exports = exports;
  }

  private boolean completeCheck(Invariant pre, Invariant post, RoutingPolicy policy) {
    if (policy == null) {
      return pre.implies(post);
    } else {
      Invariant wp = post.weakestPrecondition(policy);
      return pre.implies(wp);
    }
    //    Invariant negatedPost = post.negate();
    //    Invariant weakestConditionForNegation =
    //        policy == null ? negatedPost.copy() : negatedPost.weakestPrecondition(policy, false);
    //    // we want the precondition to imply the condition need for the post to hold
    //    return !pre.implies(weakestConditionForNegation);
  }

  public Optional<Map.Entry<Location, Location>> check(Map<Location, Invariant> invariants) {
    Map<Map.Entry<Location, Location>, Boolean> checkResults = new HashMap<>();
    for (Location location : invariants.keySet()) {
      Invariant precondition = invariants.get(location);
      // we only check precondition / postcondition agreement if the postcondition is in the network
      if (location instanceof Edge edge && edge.hasDstNode()) {
        assert invariants.containsKey(edge.getDstNode());
        Invariant postcondition = invariants.get(edge.getDstNode());
        Map.Entry<Location, Location> evaluated =
            new AbstractMap.SimpleEntry<>(edge, edge.getDstNode());
        checkResults.put(evaluated, completeCheck(precondition, postcondition, imports.get(edge)));
        if (!checkResults.get(evaluated)) {
          return Optional.of(evaluated);
        }
      } else if (location instanceof Node node) {
        for (Location e : invariants.keySet()) {
          if (e instanceof Edge edge && edge.isSrc(node)) {
            assert invariants.containsKey(edge);
            Invariant postcondition = invariants.get(edge);
            Map.Entry<Location, Location> evaluated = new AbstractMap.SimpleEntry<>(node, edge);
            checkResults.put(
                evaluated, completeCheck(precondition, postcondition, exports.get(edge)));
            if (!checkResults.get(evaluated)) {
              return Optional.of(evaluated);
            }
          }
        }
      }
    }
    assert checkResults.values().stream().allMatch(b -> b);
    return Optional.empty();
  }
}
