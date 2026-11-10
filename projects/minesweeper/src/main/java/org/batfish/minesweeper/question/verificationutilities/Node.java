package org.batfish.minesweeper.question.verificationutilities;

import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class Node extends Location {
  /// neighbor map: neighbor ip -> edge incoming into this node
  private final @Nonnull Map<Ip, Map<Ip, Edge>> neighbors = new HashMap<>();
  private final @Nonnull String name;
  /// Included for sorting purposes only
  private @Nullable Ip representativeIp;

  /// Route-reflection settings of this node's BGP process (see setRouteReflectionInfo)
  private boolean clientToClientReflection = true;
  private @Nonnull Set<Long> clusterIds = Set.of();

  /// The router ID of this node's BGP process, null if unknown
  private @Nullable Ip routerId;

  public Node(@Nonnull Set<Edge> incomingEdges, @Nonnull String name) {
    this.name = name.toLowerCase();
    this.resetNeighbors(incomingEdges);
  }

  public Node(@Nonnull String name) {
    this.name = name.toLowerCase();
  }

  public boolean addIncomingNeighbor(@Nonnull Edge incoming) {
    if (this.representativeIp == null || incoming.getDst().compareTo(this.representativeIp) < 0) {
      this.representativeIp = incoming.getDst();
    }
    Map<Ip, Edge> interfaces =
        this.neighbors.computeIfAbsent(incoming.getSrc(), k -> new HashMap<>());
    Edge prev = interfaces.put(incoming.getDst(), incoming);
    return prev != null;
  }

  public void resetNeighbors(@Nonnull Set<Edge> incomingEdges) {
    incomingEdges.forEach(
        incoming -> {
          Map<Ip, Edge> interfaces =
              this.neighbors.computeIfAbsent(incoming.getSrc(), k -> new HashMap<>());
          assert !interfaces.containsKey(incoming.getDst());
          interfaces.put(incoming.getDst(), incoming);
        });
    this.representativeIp =
        incomingEdges.isEmpty()
            ? null
            : this.neighbors.values().stream()
                .flatMap(map -> map.values().stream())
                .map(Edge::getDst)
                .sorted()
                .toList()
                .get(0);
  }

  /// This should only be used for comparison (sorting) purposes
  @Nonnull
  public Optional<Ip> getRepresentativeIp() {
    return this.representativeIp == null ? Optional.empty() : Optional.of(this.representativeIp);
  }

  @Nonnull
  public Ip getSingleIp() {
    // used mainly for testing and edge creation - in edge creation, we want to know which explicit
    // ip addresses are connected
    Set<Ip> reps =
        this.neighbors.values().stream()
            .flatMap(map -> map.values().stream())
            .map(Edge::getDst)
            .collect(Collectors.toSet());
    if (this.representativeIp != null && reps.size() == 1) {
      return Ip.create(this.representativeIp.asLong());
    } else {
      throw new BatfishException(
          "Node.getIp() - Trying to get distinct Ip address from node with multiple.");
    }
  }

  /// Whether this node reflects routes learned from route-reflector clients to other clients
  public boolean clientToClientReflection() {
    return clientToClientReflection;
  }

  /// The cluster IDs this node uses on any of its sessions; it rejects a route whose cluster list
  /// contains one of them
  @Nonnull
  public Set<Long> getClusterIds() {
    return clusterIds;
  }

  /// Records the route-reflection settings of this node's BGP process
  public void setRouteReflectionInfo(
      boolean clientToClientReflection, @Nonnull Set<Long> clusterIds) {
    this.clientToClientReflection = clientToClientReflection;
    this.clusterIds = Set.copyOf(clusterIds);
  }

  /// The router ID of this node's BGP process, which BGP uses as the originator ID of the routes
  /// it injects into iBGP; null if unknown
  @Nullable
  public Ip getRouterId() {
    return routerId;
  }

  public void setRouterId(@Nullable Ip routerId) {
    this.routerId = routerId;
  }

  @Nonnull
  public String getName() {
    return name;
  }

  public Optional<Edge> getIncoming(Ip neighbor, Ip inter) {
    if (neighbors.containsKey(neighbor) && neighbors.get(neighbor).containsKey(inter)) {
      return Optional.of(neighbors.get(neighbor).get(inter));
    }
    return Optional.empty();
  }

  /// Returns true if the provided edge is outgoing from this node
  public boolean outgoing(@Nonnull Edge edge) {
    return this.neighbors.containsKey(edge.getDst())
        && this.neighbors.get(edge.getDst()).equals(edge.flipEdge());
  }

  /// Returns true if the provided edge is incoming to this node
  public boolean incoming(@Nonnull Edge edge) {
    return this.neighbors.containsKey(edge.getSrc())
        && this.neighbors.get(edge.getDst()).equals(edge);
  }

  public boolean tiedToIp(Ip ip) {
    for (Map<Ip, Edge> incomingEdges : neighbors.values()) {
      if (incomingEdges.containsKey(ip)) {
        return true;
      }
    }
    return false;
  }

  public Optional<Edge> getIncomingFrom(Node src) {
    for (Map<Ip, Edge> incomingEdges : neighbors.values()) {
      for (Edge incoming : incomingEdges.values()) {
        if (incoming.isSrc(src)) {
          return Optional.of(incoming);
        }
      }
    }
    return Optional.empty();
  }

  /// Returns empty if there are multiple nodes incoming from Ip
  public Optional<Edge> getIncomingFrom(Ip src) {
    if (neighbors.containsKey(src) && neighbors.get(src).size() == 1) {
      assert neighbors.get(src).values().stream().findFirst().isPresent();
      return Optional.of(neighbors.get(src).values().stream().findFirst().get());
    } else {
      return Optional.empty();
    }
  }

  public Set<Edge> getAllIncomingEdges() {
    return neighbors.values().stream()
        .flatMap(map -> map.values().stream())
        .collect(Collectors.toSet());
  }

  public Set<Edge> getAllOutgoingEdges() {
    return neighbors.values().stream()
        .flatMap(map -> map.values().stream())
        .map(Edge::flipEdge)
        .collect(Collectors.toSet());
  }

  @Override
  public Node copy() {
    Node copy =
        new Node(
            neighbors.values().stream()
                .flatMap(map -> map.values().stream())
                .map(Edge::copy)
                .collect(Collectors.toSet()),
            name);
    copy.setRouteReflectionInfo(clientToClientReflection, clusterIds);
    copy.setRouterId(routerId);
    return copy;
  }

  @Override
  public Set<Location> predecessors() {
    return this.getAllIncomingEdges().stream().map(e -> (Location) e).collect(Collectors.toSet());
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    } else if (this.getClass() == obj.getClass()) {
      Node node = (Node) obj;
      // equality for ips compares the longs
      return node.name.equals(this.name)
          && node.neighbors.keySet().equals(this.neighbors.keySet())
          && node.neighbors.keySet().stream()
              .allMatch(
                  neighbor ->
                      this.neighbors.containsKey(neighbor)
                          && node.neighbors.get(neighbor).equals(this.neighbors.get(neighbor)));
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return Objects.hash(neighbors);
  }

  @Override
  public String toString() {
    return name
        + " ("
        + String.join(
            ",",
            neighbors.values().stream()
                .flatMap(map -> map.values().stream())
                .sorted()
                .map(e -> e.getDst().toString())
                .collect(Collectors.toSet()))
        + ")";
  }

  @Override
  public int compareTo(@Nonnull Location location) {
    if (location instanceof Edge edge) {
      if (this.outgoing(edge)) {
        return -1; // this is an edge coming out of provided node, so edges should follow
      } else {
        // use the single ip, so that comparisons can remain consistent
        return this.getRepresentativeIp().map(edge.getSrc()::compareTo).orElse(1);
      }
    } else if (location instanceof Node node) {
      // use the single ip, so that comparisons can remain consistent
      Optional<Ip> thisRep = this.getRepresentativeIp();
      Optional<Ip> otherRep = node.getRepresentativeIp();
      return thisRep.isPresent() && otherRep.isPresent()
          ? thisRep.get().compareTo(otherRep.get())
          : thisRep.isPresent() ? -1 : otherRep.isPresent() ? 1 : this.name.compareTo(node.name);
    } else {
      throw new BatfishException(
          "Node.compareTo() - Only two implementations of Location, should never reach here.");
    }
  }
}
