package org.batfish.minesweeper.question.reachability;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import org.batfish.datamodel.bgp.BgpTopologyUtils.ConfedSessionType;
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
/// path exploration does not use it to verify reachability. The rules follow Batfish's BGP
/// simulation (BgpProtocolHelper):
///
/// - iBGP and route reflection: a node does not advertise a route it learned over iBGP to another
///   iBGP peer, unless it reflects the route. A route reflector reflects a route learned from one
///   of its clients to its non-clients, and to its other clients if client-to-client reflection
///   is on; it reflects a route learned from a non-client to its clients only.
/// - Cluster lists: a reflector adds the cluster ID it uses on the outgoing session to the route's
///   cluster list, and a node rejects a route whose cluster list contains one of its own cluster
///   IDs (those it uses on any session). The cluster list is cleared whenever the route is sent
///   over eBGP, so it only grows along a run of iBGP hops.
/// - AS-path loop detection: a node rejects a route whose AS path contains its local AS for the
///   session, unless the session allows it (allowas-in). The AS path grows by the sender's AS on
///   each eBGP hop and by any AS a policy along the path may prepend.
/// - Confederations: a node in a confederation uses its member AS on sessions within the
///   confederation, which are eBGP between member ASes, and the confederation's AS number on
///   sessions across its border. Between member ASes, the sender adds its member AS as a
///   confederation segment of the AS path; across the border, the sender removes the confederation
///   segments before adding the confederation's AS number. A node checks its AS against every
///   segment. A session is within a confederation when both ends are in the same one (see
///   NetworkInfo.finishConfederations). A session across the border with a router whose AS is the
///   confederation's AS number is iBGP, so as in Batfish, no AS is added and the confederation
///   segments are kept. RFC 5065 instead has a member remove them before sending a route to any
///   non-member.
///
/// A path is rejected only when these rules show that no route can take it, apart from the
/// approximations below. A path that is kept may still be unusable for some routes, which is a
/// potential source of unsoundness for reachability verification:
///
/// - The AS path of the route entering the network is unknown and treated as empty. If it already
///   contains the AS of a node on the path, that node drops the route, but the path is kept. A
///   future fix could add the condition "the AS path contains none of the ASes on the path" to
///   the origin's constraint, which TransferBDD's AS-path regexes can express. Likewise, the
///   cluster list of a route entering over iBGP is treated as empty.
/// - An edge whose ASes are unknown (null; see Edge.setSessionAsInfo) contributes nothing to the
///   AS path and is not checked as a receiver. If the receiver's AS is unknown, the edge is not
///   treated as iBGP, although NetworkInfo marks it so. Note that a null local AS or an empty set
///   of remote ASes in a peer's config is not really unknown: Batfish never establishes such a
///   session (see BgpTopologyUtils), so no route crosses it, but NetworkInfo still creates an edge
///   for it and paths over that edge are kept. A null sender AS can also come from a remote AS
///   given as a range (e.g. FRR "remote-as external"), where the session is established and only
///   the sender's AS is unknown.
/// - A session without a cluster ID adds nothing to the cluster list, as in Batfish.
/// - The originator ID is not checked: a node rejects a route that it injected into iBGP itself.
///   Paths never repeat a node, so this only matters if two nodes share a router ID.
/// - Prepends of a VarAs, and AS-path rewrites (ExcludeAsPath, ReplaceAsesInAsSequence,
///   as-override, remove-private-as, replace-as) are not modeled.
/// - For a session with a neighbor that has no config, whether it is within the receiver's
///   confederation is judged from the receiver's member ASes, which some platforms (e.g. FRR) list
///   only partially, so the session can be misjudged either way.
/// - Sender-side loop detection (Batfish's allowRemoteAsOut) is not modeled, since the standard
///   does not require it. It only matters when the target is an edge, whose receiver is not
///   checked: on platforms that do it, the route may not be advertised on the target edge. For
///   the same reason, the cluster list is checked at the receiver, as the standard says, although
///   Batfish checks it before sending the route.
///
/// Other approximations reject paths that may be usable, which only makes the analysis less
/// complete:
///
/// - Every AS a policy may prepend, on any branch, is treated as prepended.
/// - A node's cluster IDs are those it uses on any of its sessions, as in Batfish; some platforms
///   check fewer.
/// - If a sender has no configured session back toward the receiver, it is taken to treat the
///   receiver as a non-client, which only matters for reflection. Batfish does not establish such
///   a session anyway.
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
  /// imported by its receiver, so the receiver's checks and import policy do not apply.
  public boolean isValid(@Nonnull List<Edge> edges, boolean endsAtEdge) {
    Suffix suffix = Suffix.EMPTY;
    for (int k = edges.size() - 1; k >= 0; k--) {
      suffix = extend(suffix, edges.get(k), endsAtEdge && k == edges.size() - 1);
      if (suffix == null) {
        return false;
      }
    }
    return true;
  }

  /// What a valid path suffix, running from some node to the target, requires of the edges that
  /// extend it backward into that node:
  ///
  /// - allowsIbgpFromClient and allowsIbgpFromNonClient: whether the edge may be an iBGP session
  ///   from one of the node's route-reflector clients, or from a non-client. If the suffix starts
  ///   with an iBGP edge, the node would be reflecting the route.
  /// - ibgpRunClusterIds: the cluster IDs of the receivers along the suffix's initial run of iBGP
  ///   edges, which reject a route whose cluster list contains one of them.
  /// - checkedAses: the ASes of the receivers along the suffix that check for AS-path loops.
  /// - checkedConfedAses: the ASes of those receivers before the suffix's first crossing of a
  ///   confederation border, which removes the member ASes from the AS path; only these receivers
  ///   see a member AS added before the suffix.
  ///
  /// Two suffixes with equal requirements allow the same extensions.
  public record Suffix(
      boolean allowsIbgpFromClient,
      boolean allowsIbgpFromNonClient,
      @Nonnull Set<Long> ibgpRunClusterIds,
      @Nonnull Set<Long> checkedAses,
      @Nonnull Set<Long> checkedConfedAses) {
    public static final Suffix EMPTY = new Suffix(true, true, Set.of(), Set.of(), Set.of());

    /// Whether every extension that the other suffix allows is also allowed by this one
    public boolean weakerThan(@Nonnull Suffix other) {
      return (allowsIbgpFromClient || !other.allowsIbgpFromClient)
          && (allowsIbgpFromNonClient || !other.allowsIbgpFromNonClient)
          && other.ibgpRunClusterIds.containsAll(ibgpRunClusterIds)
          && other.checkedAses.containsAll(checkedAses)
          && other.checkedConfedAses.containsAll(checkedConfedAses);
    }
  }

  /// Extends the suffix backward by an edge into its first node, returning null if the longer
  /// suffix is ruled out. If isTarget is true, the edge is the target itself, so the suffix is
  /// empty and the edge's receiver is not checked.
  public @Nullable Suffix extend(@Nonnull Suffix suffix, @Nonnull Edge edge, boolean isTarget) {
    // a session whose local AS is unknown is marked iBGP by NetworkInfo, but its type is unknown
    boolean ibgp = !edge.isEBGP() && edge.getDstAs() != null;
    if (ibgp
        && !(edge.dstTreatsSrcAsClient()
            ? suffix.allowsIbgpFromClient()
            : suffix.allowsIbgpFromNonClient())) {
      return null;
    }
    // the ASes added by the sender's export policy and, on an eBGP session, the sender's AS,
    // which within a confederation is its member AS, added as a confederation segment
    ConfedSessionType confedType = confedType(edge);
    Set<Long> sent = new HashSet<>();
    addPrepended(sent, exports.get(edge), edge, true);
    Long senderAs = senderAs(edge);
    Long sentMemberAs = null;
    if (edge.isEBGP() && senderAs != null) {
      if (confedType == ConfedSessionType.WITHIN_CONFED) {
        sentMemberAs = senderAs;
      } else {
        sent.add(senderAs);
      }
    }
    // the receiver's loop check happens before its import policy, so it sees only the sent ASes
    Set<Long> checkedAses = new HashSet<>(suffix.checkedAses());
    Set<Long> checkedConfedAses = new HashSet<>(suffix.checkedConfedAses());
    Long receiverAs = edge.getDstAs();
    if (!isTarget && receiverAs != null && !edge.dstAllowsLocalAsIn()) {
      checkedAses.add(receiverAs);
      checkedConfedAses.add(receiverAs);
    }
    if (sent.stream().anyMatch(checkedAses::contains)
        || (sentMemberAs != null && checkedConfedAses.contains(sentMemberAs))) {
      return null;
    }
    // crossing a confederation border over eBGP removes the member ASes added before this edge, so
    // no receiver from here on sees them; as in Batfish, an iBGP session across the border (with a
    // router whose AS is the confederation's AS number) keeps them
    if (confedType == ConfedSessionType.ACROSS_CONFED_BORDER && edge.isEBGP()) {
      checkedConfedAses.clear();
    }
    if (!isTarget) {
      Set<Long> imported = new HashSet<>();
      addPrepended(imported, imports.get(edge), edge, false);
      if (imported.stream().anyMatch(suffix.checkedAses()::contains)) {
        return null;
      }
    }
    // the cluster IDs of the receivers along the run of iBGP edges that starts with this one
    Set<Long> ibgpRunClusterIds = new HashSet<>();
    if (ibgp) {
      ibgpRunClusterIds.addAll(suffix.ibgpRunClusterIds());
      if (!isTarget && edge.getDstNode() != null) {
        ibgpRunClusterIds.addAll(edge.getDstNode().getClusterIds());
      }
    }
    // if the sender learned the route over iBGP, it is reflecting the route onto this edge
    boolean allowsIbgpFromClient = true;
    boolean allowsIbgpFromNonClient = true;
    Node sender = edge.getSrcNode();
    if (ibgp && sender != null) {
      // the sender's settings for this session, from the reverse edge
      Optional<Edge> reverse = sender.getIncoming(edge.getDst(), edge.getSrc());
      boolean toClient = reverse.map(Edge::dstTreatsSrcAsClient).orElse(false);
      Long clusterId = reverse.map(Edge::getDstClusterId).orElse(null);
      // a receiver along the run would reject the cluster ID the sender adds
      boolean clusterLoop = clusterId != null && ibgpRunClusterIds.contains(clusterId);
      allowsIbgpFromClient = !clusterLoop && (!toClient || sender.clientToClientReflection());
      allowsIbgpFromNonClient = !clusterLoop && toClient;
    }
    return new Suffix(
        allowsIbgpFromClient,
        allowsIbgpFromNonClient,
        Set.copyOf(ibgpRunClusterIds),
        Set.copyOf(checkedAses),
        Set.copyOf(checkedConfedAses));
  }

  /// Whether the session is within a confederation or across its border, as configured at the
  /// receiver if it is in a confederation, and otherwise at the sender, found on the reverse edge
  private static ConfedSessionType confedType(Edge edge) {
    ConfedSessionType type = edge.getDstConfed().type();
    Node sender = edge.getSrcNode();
    if (type == ConfedSessionType.NO_CONFED && sender != null) {
      type =
          sender
              .getIncoming(edge.getDst(), edge.getSrc())
              .map(reverse -> reverse.getDstConfed().type())
              .orElse(ConfedSessionType.NO_CONFED);
    }
    return type;
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
