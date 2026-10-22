package org.batfish.minesweeper.question.reachability;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.AsExpr;
import org.batfish.datamodel.routing_policy.expr.AutoAs;
import org.batfish.datamodel.routing_policy.expr.ExplicitAs;
import org.batfish.datamodel.routing_policy.expr.LocalAs;
import org.batfish.datamodel.routing_policy.expr.RemoteAs;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.utils.Tuple;

/// Decides whether a path through the BGP topology is ruled out by BGP's loop prevention, so that
/// path exploration does not use it to verify reachability. Two rules are checked:
///
/// - iBGP: a node does not advertise a route it learned over iBGP to another iBGP peer.
/// - AS-path loop detection: a node rejects a route whose AS path contains its local AS for the
///   session, unless the session allows it (allowas-in). The AS path grows by the sender's AS on
///   each eBGP hop and by any AS a policy along the path may prepend.
///
/// A path is rejected only when these rules show that no route can take it, apart from the
/// approximations below. A path that is kept may still be unusable for some routes, which is a
/// potential source of unsoundness for reachability verification:
///
/// - The AS path of the route entering the network is unknown and treated as empty. If it already
///   contains the AS of a node on the path, that node drops the route, but the path is kept. A
///   future fix could add the condition "the AS path contains none of the ASes on the path" to
///   the origin's constraint, which TransferBDD's AS-path regexes can express.
/// - An edge whose ASes are unknown (null; see Edge.setSessionAsInfo) contributes nothing to the
///   AS path and is not checked as a receiver.
/// - Prepends of a VarAs, and AS-path rewrites (ExcludeAsPath, ReplaceAsesInAsSequence, as-override,
///   remove-private-as, replace-as) are not modeled. Confederations are not modeled.
/// - Sender-side loop detection (Batfish's allowRemoteAsOut) is not modeled, since the standard
///   does not require it. It only matters when the target is an edge, whose receiver is not
///   checked: on platforms that do it, the route may not be advertised on the target edge.
///
/// Other approximations reject paths that may be usable, which only makes the analysis less
/// complete:
///
/// - Route reflection is not modeled, so every iBGP hop followed by another iBGP hop is rejected,
///   including those a route reflector would allow.
/// - Every AS a policy may prepend, on any branch, is treated as prepended.
public class BgpPathValidity {
  private final Map<Edge, RoutingPolicy> imports;
  private final Map<Edge, RoutingPolicy> exports;

  /// The AS expressions each policy may prepend
  private final Map<RoutingPolicy, Set<AsExpr>> prependCache = new HashMap<>();

  public BgpPathValidity(
      @Nonnull Map<Edge, RoutingPolicy> imports, @Nonnull Map<Edge, RoutingPolicy> exports) {
    this.imports = imports;
    this.exports = exports;
  }

  /// Checks a path as built by PathExploration: alternating nodes and edges, ordered from the
  /// target (index 0) back to the origin.
  public boolean isValid(@Nonnull Location[] targetFirstPath) {
    List<Edge> edges = new ArrayList<>();
    for (int i = targetFirstPath.length - 1; i >= 0; i--) {
      if (targetFirstPath[i] instanceof Edge edge) {
        edges.add(edge);
      }
    }
    boolean endsAtEdge = targetFirstPath.length > 0 && targetFirstPath[0] instanceof Edge;
    return isValid(edges, endsAtEdge);
  }

  /// Checks the path that traverses the given edges in order, from the origin to the target. If
  /// endsAtEdge is true, the target is the last edge itself: the route is sent on it but not yet
  /// imported by its receiver, so the receiver's checks do not apply.
  public boolean isValid(@Nonnull List<Edge> edges, boolean endsAtEdge) {
    for (int k = 1; k < edges.size(); k++) {
      if (!edges.get(k - 1).isEBGP() && !edges.get(k).isEBGP()) {
        return false;
      }
    }
    // the ASes that may be in the route's AS path so far
    Set<Long> asPath = new HashSet<>();
    for (int k = 0; k < edges.size(); k++) {
      Edge edge = edges.get(k);
      // the sender's export policy, then the sender's AS on an eBGP session
      addPrepended(asPath, exports.get(edge), edge, true);
      Long senderAs = senderAs(edge);
      if (edge.isEBGP() && senderAs != null) {
        asPath.add(senderAs);
      }
      if (endsAtEdge && k == edges.size() - 1) {
        break;
      }
      // the receiver's loop check, which happens before its import policy
      Long receiverAs = edge.getDstAs();
      if (receiverAs != null && !edge.dstAllowsLocalAsIn() && asPath.contains(receiverAs)) {
        return false;
      }
      addPrepended(asPath, imports.get(edge), edge, false);
    }
    return true;
  }

  /// The AS the sender uses on the session, which is what it prepends on eBGP. If the sender is in
  /// the network, this is the local AS in its own config, found on the reverse edge; otherwise it
  /// is the remote AS configured at the receiver.
  private static @Nullable Long senderAs(Edge edge) {
    Node sender = edge.getSrcNode();
    if (sender != null) {
      Long local =
          sender.getIncoming(edge.getDst(), edge.getSrc()).map(Edge::getDstAs).orElse(null);
      if (local != null) {
        return local;
      }
    }
    return edge.getSrcAs();
  }

  /// The AS the receiver expects of the sender: the remote AS in the sender's config, found on the
  /// reverse edge if the sender is in the network, or else the receiver's local AS.
  private static @Nullable Long receiverAsAtSender(Edge edge) {
    Node sender = edge.getSrcNode();
    if (sender != null) {
      Long remote =
          sender.getIncoming(edge.getDst(), edge.getSrc()).map(Edge::getSrcAs).orElse(null);
      if (remote != null) {
        return remote;
      }
    }
    return edge.getDstAs();
  }

  /// Adds the ASes the policy may prepend when applied to the given edge, as the sender's export
  /// policy or as the receiver's import policy
  private void addPrepended(
      Set<Long> asPath, @Nullable RoutingPolicy policy, Edge edge, boolean export) {
    if (policy == null) {
      return;
    }
    for (AsExpr expr : prepended(policy)) {
      Long as = resolve(expr, edge, export);
      if (as != null) {
        asPath.add(as);
      }
    }
  }

  private Set<AsExpr> prepended(RoutingPolicy policy) {
    return prependCache.computeIfAbsent(
        policy,
        p ->
            new PrependedAsCollector()
                .visitAll(p.getStatements(), new Tuple<>(new HashSet<>(), p.getOwner())));
  }

  /// The AS a prepended expression denotes on the given edge, or null if it adds no AS that is not
  /// already in the AS path, or cannot be determined
  private static @Nullable Long resolve(AsExpr expr, Edge edge, boolean export) {
    if (expr instanceof ExplicitAs explicit) {
      return explicit.getAs();
    } else if (expr instanceof LocalAs) {
      return export ? senderAs(edge) : edge.getDstAs();
    } else if (expr instanceof RemoteAs) {
      return export ? receiverAsAtSender(edge) : edge.getSrcAs();
    } else if (expr instanceof AutoAs) {
      // outbound this is the local AS; inbound it is the last AS of the route, already present
      return export ? senderAs(edge) : null;
    } else {
      // LastAs repeats an AS already in the path; VarAs cannot be evaluated
      return null;
    }
  }
}
