package org.batfish.minesweeper.question.verificationutilities;

import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Objects;
import java.util.Set;

public class Edge extends Location {
  private final @Nonnull Ip src;
  private @Nullable Node srcNode;
  private final @Nonnull Ip dst;
  private @Nullable Node dstNode;

  private final boolean eBGP;

  /// AS numbers and allowas-in setting of the BGP session this edge represents, as configured at
  /// the receiving end (see setSessionAsInfo). A null AS means it is unknown.
  private @Nullable Long srcAs;
  private @Nullable Long dstAs;
  private boolean srcAllowsLocalAsIn;
  private boolean dstAllowsLocalAsIn;

  /// Route-reflection settings of the session, as configured at the receiving end (see
  /// setRouteReflectionInfo): whether the receiver treats the sender as a route-reflector client,
  /// and the cluster ID the receiver uses on the session (null if none)
  private boolean srcTreatsDstAsClient;
  private boolean dstTreatsSrcAsClient;
  private @Nullable Long srcClusterId;
  private @Nullable Long dstClusterId;

  public Edge(@Nonnull Ip src, @Nonnull Ip dst, boolean eBGP) {
    assert !src.equals(dst);
    assert !src.equals(Ip.ZERO) && !dst.equals(Ip.ZERO);
    this.src = src;
    this.dst = dst;
    this.eBGP = eBGP;
  }

  public Edge(@Nonnull Ip src, @Nonnull Ip dst) {
    this(src, dst, false);
  }

  public Edge(@Nonnull String src, @Nonnull String dst) {
    this(Ip.parse(src), Ip.parse(dst));
  }

  /// Will throw error if the nodes provided have more than Ip address, need to provide the explicit
  /// connection represented by this edge. References provided nodes (no copy)
  public Edge(@Nonnull Node src, @Nonnull Node dst) {
    this.srcNode = src;
    this.dstNode = dst;
    assert !src.equals(dst);
    this.src = Ip.create(src.getSingleIp().asLong());
    this.dst = Ip.create(dst.getSingleIp().asLong());
    assert !this.src.equals(Ip.ZERO) && !this.dst.equals(Ip.ZERO);
    this.eBGP = false;
  }

  private Edge(
      @Nonnull Ip src,
      @Nonnull Ip dst,
      boolean eBGP,
      @Nullable Node srcNode,
      @Nullable Node dstNode,
      @Nullable Long srcAs,
      @Nullable Long dstAs,
      boolean srcAllowsLocalAsIn,
      boolean dstAllowsLocalAsIn,
      boolean srcTreatsDstAsClient,
      boolean dstTreatsSrcAsClient,
      @Nullable Long srcClusterId,
      @Nullable Long dstClusterId) {
    this.src = src;
    this.dst = dst;
    this.eBGP = eBGP;
    this.srcNode = srcNode;
    this.dstNode = dstNode;
    this.srcAs = srcAs;
    this.dstAs = dstAs;
    this.srcAllowsLocalAsIn = srcAllowsLocalAsIn;
    this.dstAllowsLocalAsIn = dstAllowsLocalAsIn;
    this.srcTreatsDstAsClient = srcTreatsDstAsClient;
    this.dstTreatsSrcAsClient = dstTreatsSrcAsClient;
    this.srcClusterId = srcClusterId;
    this.dstClusterId = dstClusterId;
  }

  @Nonnull
  public Ip getSrc() {
    return src;
  }

  @Nonnull
  public Ip getDst() {
    return dst;
  }

  @Nullable
  public Node getSrcNode() {
    return srcNode;
  }

  @Nullable
  public Node getDstNode() {
    return dstNode;
  }

  public boolean isEBGP() {
    return eBGP;
  }

  /// The AS the sender uses on this session, which it prepends when advertising over eBGP
  @Nullable
  public Long getSrcAs() {
    return srcAs;
  }

  /// The receiver's local AS on this session, which its BGP loop detection checks for
  @Nullable
  public Long getDstAs() {
    return dstAs;
  }

  /// Whether the receiver accepts routes whose AS path already contains its local AS (allowas-in)
  public boolean dstAllowsLocalAsIn() {
    return dstAllowsLocalAsIn;
  }

  /// Records the session's AS numbers, as configured at the receiving end of this edge: srcAs is
  /// the configured remote AS (null if not a single AS), dstAs is the local AS (null if unknown).
  public void setSessionAsInfo(
      @Nullable Long srcAs, @Nullable Long dstAs, boolean dstAllowsLocalAsIn) {
    this.srcAs = srcAs;
    this.dstAs = dstAs;
    this.dstAllowsLocalAsIn = dstAllowsLocalAsIn;
  }

  /// Whether the receiver treats the sender as a route-reflector client on this session
  public boolean dstTreatsSrcAsClient() {
    return dstTreatsSrcAsClient;
  }

  /// The cluster ID the receiver uses on this session, which it adds to the cluster list of a
  /// route it reflects to the sender; null if none is configured
  @Nullable
  public Long getDstClusterId() {
    return dstClusterId;
  }

  /// Records the session's route-reflection settings, as configured at the receiving end
  public void setRouteReflectionInfo(boolean dstTreatsSrcAsClient, @Nullable Long dstClusterId) {
    this.dstTreatsSrcAsClient = dstTreatsSrcAsClient;
    this.dstClusterId = dstClusterId;
  }

  @Nonnull
  public Edge flipEdge() {
    return new Edge(
        dst,
        src,
        eBGP,
        dstNode,
        srcNode,
        dstAs,
        srcAs,
        dstAllowsLocalAsIn,
        srcAllowsLocalAsIn,
        dstTreatsSrcAsClient,
        srcTreatsDstAsClient,
        dstClusterId,
        srcClusterId);
  }

  public void setSrcNode(Node src) {
    if (this.hasSrcNode()) {
      throw new BatfishException("ERROR cannot reset the source node of an edge once set");
    } else {
      this.srcNode = src;
    }
  }

  public boolean hasSrcNode() {
    return this.srcNode != null;
  }

  public void setDstNode(Node dst) {
    if (this.hasDstNode()) {
      throw new BatfishException("ERROR cannot reset the destination node of an edge once set");
    } else {
      this.dstNode = dst;
    }
  }

  public boolean hasDstNode() {
    return this.dstNode != null;
  }

  public boolean isSrc(@Nonnull Node node) {
    if (this.hasSrcNode()) {
      return node.equals(this.srcNode);
    } else {
      return node.outgoing(this);
    }
  }

  public boolean isDst(@Nonnull Node node) {
    if (this.hasDstNode()) {
      return node.equals(this.dstNode);
    } else {
      return node.incoming(this);
    }
  }

  @Override
  public Edge copy() {
    return new Edge(
        Ip.create(src.asLong()),
        Ip.create(dst.asLong()),
        eBGP,
        srcNode,
        dstNode,
        srcAs,
        dstAs,
        srcAllowsLocalAsIn,
        dstAllowsLocalAsIn,
        srcTreatsDstAsClient,
        dstTreatsSrcAsClient,
        srcClusterId,
        dstClusterId);
  }

  @Override
  public Set<Location> predecessors() {
    return this.srcNode == null ? Set.of() : Set.of(this.srcNode);
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    } else if (this.getClass() == obj.getClass()) {
      Edge edge = (Edge) obj;
      return edge.src.equals(this.src)
          && edge.dst.equals(this.dst)
          && (edge.getSrcNode() == null ? "" : edge.getSrcNode().getName())
              .equals(srcNode == null ? "" : srcNode.getName())
          && (edge.getDstNode() == null ? "" : edge.getDstNode().getName())
              .equals(dstNode == null ? "" : dstNode.getName());
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return Objects.hash(
        src,
        dst,
        srcNode == null ? "" : srcNode.getName(),
        dstNode == null ? "" : dstNode.getName());
  }

  @Override
  public String toString() {
    String srcStr = this.srcNode != null ? this.srcNode.getName() : this.src.toString();
    String dstStr = this.dstNode != null ? this.dstNode.getName() : this.dst.toString();
    return srcStr + " -> " + dstStr;
  }

  @Override
  public String toUniqueString() {
    String srcStr = this.srcNode != null ? "(" + this.srcNode.getName() + ") " : "";
    String dstStr = this.dstNode != null ? " (" + this.dstNode.getName() + ")" : "";
    return srcStr + src + " -> " + dst + dstStr;
  }

  @Override
  public int compareTo(@Nonnull Location location) {
    if (location instanceof Edge edge) {
      if (edge.src.equals(this.src)) {
        return this.dst.compareTo(edge.dst);
      } else {
        return this.src.compareTo(edge.src);
      }
    } else if (location instanceof Node node) {
      if (node.outgoing(this)) {
        return 1; // this is an edge coming out of provided node, so edges should follow
      } else {
        // use the single ip, so that comparisons can remain consistent
        return node.getRepresentativeIp().map(this.src::compareTo).orElse(1);
      }
    } else {
      throw new BatfishException(
          "Edge.compareTo() - Only two handled implementations of Location, should never reach here.");
    }
  }
}
