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
      @Nullable Node dstNode) {
    this.src = src;
    this.dst = dst;
    this.eBGP = eBGP;
    this.srcNode = srcNode;
    this.dstNode = dstNode;
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

  @Nonnull
  public Edge flipEdge() {
    return new Edge(dst, src, eBGP, dstNode, srcNode);
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
    return new Edge(Ip.create(src.asLong()), Ip.create(dst.asLong()), eBGP, srcNode, dstNode);
  }

  @Override
  public Set<Location> predecessors() {
    return this.srcNode == null ? Set.of() : Set.of(this.srcNode);
  }

  @Override
  public boolean equals(Object obj) {
    if (this.getClass() == obj.getClass()) {
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
