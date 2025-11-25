package org.batfish.minesweeper.question.verify;

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
        this.src = Ip.create(src.getIp().asLong());
        this.dst = Ip.create(dst.getIp().asLong());
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
        return src.equals(node.getIp());
    }

    public boolean isDst(Node node) {
        return dst.equals(node.getIp());
    }

    @Override
    Edge copy() {
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
}
