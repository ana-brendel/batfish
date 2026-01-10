package org.batfish.minesweeper.question.verify;

import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class Node extends Location {
    private final List<Ip> ips;
    private final String name;

    public Node(@Nonnull Ip ip, @Nonnull String name) {
        this.ips = List.of(ip);
        this.name = name;
    }

    public Node(@Nonnull String ip, @Nonnull String name) {
        this.ips = List.of(Ip.parse(ip));
        this.name = name;
    }

    public Node(@Nonnull Collection<Ip> ips, @Nonnull String name) {
        this.ips = ips.stream().sorted().collect(Collectors.toList());
        this.name = name;
    }

    public Ip getSingleIp() {
        if (ips.size() != 1)
            throw new BatfishException("Node.getIp() - Trying to get distinct Ip address from node with multiple.");
        return Ip.create(ips.get(0).asLong());
    }

    public Collection<Ip> getIps() {
        return new ArrayList<>(ips);
    }

    public String getName() {
        return name;
    }

    /// Returns true if the provided edge is outgoing from this node
    public boolean outgoing(Edge edge) {
        return ips.stream().anyMatch(ip -> ip.equals(edge.getSrc()));
    }

    /// Returns true if the provided edge is incoming to this node
    public boolean incoming(Edge edge) {
        return ips.stream().anyMatch(ip -> ip.equals(edge.getDst()));
    }

    @Override
    Node copy() {
        return new Node(ips, name);
    }

    @Override
    public boolean equals(Object obj) {
        if (this.getClass() == obj.getClass()) {
            Node node = (Node) obj;
            // equality for ips compares the longs
            return node.ips.equals(this.ips);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return Objects.hash(ips);
    }

    @Override
    public String toString() {
        return name + " (" + String.join(",",ips.stream().map(Ip::toString).collect(Collectors.toSet())) + ")";
    }

    @Override
    public int compareTo(@Nonnull Location location) {
        if (location instanceof Edge edge) {
            if (this.getIps().contains(edge.getSrc()))
                return -1; // this is an edge coming out of provided node, so edges should follow
            else
                // use the single ip, so that comparisons can remain consistent
                return this.getSingleIp().compareTo(edge.getSrc());
        } else if (location instanceof Node node) {
            // use the single ip, so that comparisons can remain consistent
            return this.getSingleIp().compareTo(node.getSingleIp());
        } else {
            throw new BatfishException("Node.compareTo() - Only two implementations of Location, should never reach here.");
        }
    }
}
