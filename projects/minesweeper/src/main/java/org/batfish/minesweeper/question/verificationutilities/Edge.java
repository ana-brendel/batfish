package org.batfish.minesweeper.question.verificationutilities;

import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import java.util.Objects;

public class Edge extends Location {
    private final Ip src;
    private final Ip dst;

    public Edge(@Nonnull Ip src, @Nonnull Ip dst) {
        assert !src.equals(dst);
        this.src = src;
        this.dst = dst;
    }

    public Edge(@Nonnull String src, @Nonnull String dst) {
        assert !src.equals(dst);
        this.src = Ip.parse(src);
        this.dst = Ip.parse(dst);
    }

    public Edge(@Nonnull Node src, @Nonnull Node dst) {
        assert !src.equals(dst);
        this.src = Ip.create(src.getSingleIp().asLong());
        this.dst = Ip.create(dst.getSingleIp().asLong());
    }

    public Ip getSrc() {
        return src;
    }

    public Ip getDst() {
        return dst;
    }

    public Edge flipEdge() {
        return new Edge(dst,src);
    }

    public boolean isSrc(Node node) {
        return node.getIps().stream().anyMatch(ip -> ip.equals(src));
    }

    public boolean isDst(Node node){
        return node.getIps().stream().anyMatch(ip -> ip.equals(dst));
    }

    @Override
    public Edge copy() {
        return new Edge(Ip.create(src.asLong()),Ip.create(dst.asLong()));
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
            if (edge.src.equals(this.src))
                return this.dst.compareTo(edge.dst);
            else
                return this.src.compareTo(edge.src);
        } else if (location instanceof Node node) {
            if (node.getIps().contains(this.src))
                return 1; // this is an edge coming out of provided node, so edges should follow
            else
                // use the single ip, so that comparisons can remain consistent
                return node.getRepresentativeIp().map(this.src::compareTo).orElse(1);
        } else {
            throw new BatfishException("Edge.compareTo() - Only two implementations of Location, should never reach here.");
        }
    }
}
