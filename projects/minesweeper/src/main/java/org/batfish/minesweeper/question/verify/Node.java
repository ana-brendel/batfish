package org.batfish.minesweeper.question.verify;

import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import java.util.Objects;

public class Node extends Location{
    private final Ip ip;
    private final String name;

    public Node(@Nonnull Ip ip, @Nonnull String name) {
        this.ip = ip;
        this.name = name;
    }

    public Node(@Nonnull String ip, @Nonnull String name) {
        this.ip = Ip.parse(ip);
        this.name = name;
    }

    public Ip getIp() {
        return ip;
    }

    public String getName() {
        return name;
    }

    public boolean outgoing(Edge edge) {
        return edge.getSrc().equals(ip);
    }

    public boolean incoming(Edge edge) {
        return edge.getDst().equals(ip);
    }

    @Override
    Node copy() {
        return new Node(Ip.create(ip.asLong()), name);
    }

    @Override
    public boolean equals(Object obj) {
        if (this.getClass() == obj.getClass()) {
            Node node = (Node) obj;
            return node.ip.asLong() == (this.ip.asLong());
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return Objects.hash(ip);
    }

    @Override
    public String toString() {
        return ip + " (" + name + ")";
    }
}
