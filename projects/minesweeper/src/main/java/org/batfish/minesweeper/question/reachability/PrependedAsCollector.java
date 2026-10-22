package org.batfish.minesweeper.question.reachability;

import com.google.common.collect.ImmutableSet;
import java.util.Set;
import javax.annotation.ParametersAreNonnullByDefault;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.routing_policy.expr.AsExpr;
import org.batfish.datamodel.routing_policy.expr.AsPathListExpr;
import org.batfish.datamodel.routing_policy.expr.LiteralAsList;
import org.batfish.datamodel.routing_policy.expr.MultipliedAs;
import org.batfish.datamodel.routing_policy.statement.PrependAsPath;
import org.batfish.minesweeper.aspath.RoutingPolicyCollector;
import org.batfish.minesweeper.utils.Tuple;

/// Collects the AS expressions that a routing policy may prepend to a route's AS path, across all
/// branches of the policy and the policies it calls. Expressions such as LocalAs are kept
/// symbolic, since their value depends on the BGP session the policy is applied to.
@ParametersAreNonnullByDefault
public class PrependedAsCollector extends RoutingPolicyCollector<AsExpr> {
  @Override
  public Set<AsExpr> visitPrependAsPath(
      PrependAsPath prependAsPath, Tuple<Set<String>, Configuration> arg) {
    AsPathListExpr expr = prependAsPath.getExpr();
    if (expr instanceof LiteralAsList literal) {
      return ImmutableSet.copyOf(literal.getList());
    } else if (expr instanceof MultipliedAs multiplied) {
      return ImmutableSet.of(multiplied.getExpr());
    } else {
      throw new UnsupportedOperationException(expr.toString());
    }
  }
}
