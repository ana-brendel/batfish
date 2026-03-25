package org.batfish.minesweeper.question.verificationutilities;

import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import java.util.Map;
import java.util.Objects;

public class Edge extends Location {
  private final @Nonnull Ip src;
  private final @Nonnull Ip dst;

  private final boolean eBGP;

  public Edge(@Nonnull Ip src, @Nonnull Ip dst, boolean eBGP) {
    assert !src.equals(dst);
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
  /// connection represented by this edge
  public Edge(@Nonnull Node src, @Nonnull Node dst) {
    this(Ip.create(src.getSingleIp().asLong()), Ip.create(dst.getSingleIp().asLong()));
  }

  @Nonnull
  public Ip getSrc() {
    return src;
  }

  @Nonnull
  public Ip getDst() {
    return dst;
  }

  public boolean isEBGP() {
    return eBGP;
  }

  @Nonnull
  public Edge flipEdge() {
    return new Edge(dst, src, eBGP);
  }

  public boolean isSrc(@Nonnull Node node) {
    return node.getIps().stream().anyMatch(ip -> ip.equals(src));
  }

  public boolean isDst(@Nonnull Node node) {
    return node.getIps().stream().anyMatch(ip -> ip.equals(dst));
  }

  @Override
  public Edge copy() {
    return new Edge(Ip.create(src.asLong()), Ip.create(dst.asLong()), eBGP);
  }

  @Override
  public String contextString(Map<Ip, Node> nodes) {
    String srcStr = nodes.containsKey(src) ? nodes.get(src).getName() : src.toString();
    String dstStr = nodes.containsKey(dst) ? nodes.get(dst).getName() : dst.toString();
    return srcStr + " -> " + dstStr;
  }

  @Override
  public boolean equals(Object obj) {
    if (this.getClass() == obj.getClass()) {
      Edge edge = (Edge) obj;
      return edge.src.equals(this.src) && edge.dst.equals(this.dst);
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return Objects.hash(src, dst);
  }

  @Override
  public String toString() {
    return src + " -> " + dst;
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
      if (node.getIps().contains(this.src)) {
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
