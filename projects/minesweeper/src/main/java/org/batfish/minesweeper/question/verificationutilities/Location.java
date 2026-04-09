package org.batfish.minesweeper.question.verificationutilities;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public abstract class Location implements Comparable<Location> {
  public abstract Location copy();

  /// Builder for location to take in the location independent of the network info
  public static class Builder {
    private final String PROP_SRC = "source";
    private final String PROP_DST = "destination";
    private final String PROP_NODE = "nodeName";

    public final String _head;
    public final String _tail;

    @JsonCreator
    public Builder(
        @JsonProperty(PROP_SRC) @Nullable String src,
        @JsonProperty(PROP_DST) @Nullable String dst,
        @JsonProperty(PROP_NODE) @Nullable String node) {
      if (node != null) {
        _head = node.toLowerCase();
        _tail = null;
      } else if (src != null && dst != null) {
        _head = src.toLowerCase();
        _tail = dst.toLowerCase();
      } else {
        _head = src;
        _tail = dst;
      }
    }

    @JsonCreator
    @VisibleForTesting
    static Builder forValue(String value) {
      String[] splits = value.trim().split("->");
      if (splits.length == 1) {
        return new Builder(null, null, value.trim());
      } else if (splits.length == 2) {
        return new Builder(splits[0].trim(), splits[1].trim(), null);
      } else {
        throw new BatfishException(
            "String parsing into location (NetworkLocation) failed. "
                + "An edge should be 'src -> dst' and a node should just be 'nodeName' or 'ipAddress'. "
                + "Ip addresses or node names can be used for edge specification when appropriate.");
      }
    }

    /// Gets the Location based on the Verifier (which is based on Network Snapshot)
    /// -- maybe change to only succeed if provided with IPs
    public Set<Location> instantiate(NetworkInfo info) {
      assert _head != null : "Expect non-null 'head' field for Location.Builder.";
      if (_tail != null && _head.equals("*")) {
        Optional<Node> dst = info.getNodeByName(_tail);
        if (dst.isEmpty()) {
          Optional<Ip> tailIp = Ip.tryParse(_tail);
          if (tailIp.isPresent()) {
            Set<Location> incoming = info.getEdgesByDstIp(tailIp.get());
            if (!incoming.isEmpty()) {
              return incoming;
            } else {
              throw new BatfishException(
                  "Location.instantiate() - Destination of abstract edge ("
                      + _tail
                      + ") not within network. Connection doesn't exist.");
            }
          } else {
            throw new BatfishException(
                "Location.instantiate() - Destination of abstract edge ("
                    + _tail
                    + ") not valid Ip address.");
          }
        }
        Set<Location> incoming =
            dst.get().getAllIncomingEdges().stream()
                .map(e -> (Location) e)
                .collect(Collectors.toSet());
        if (incoming.isEmpty()) {
          throw new BatfishException(
              "Location.instantiate() - Destination of abstract edge ("
                  + _head
                  + ") has no sources.");
        } else {
          return incoming;
        }
      } else if (_tail != null && _tail.equals("*")) {
        Optional<Node> src = info.getNodeByName(_head);
        if (src.isEmpty()) {
          Optional<Ip> srcIp = Ip.tryParse(_head);
          if (srcIp.isPresent()) {
            Set<Location> outgoing = info.getEdgesBySrcIp(srcIp.get());
            if (!outgoing.isEmpty()) {
              return outgoing;
            } else {
              throw new BatfishException(
                  "Location.instantiate() - Source of abstract edge ("
                      + _head
                      + ") not within network. Connection doesn't exist.");
            }
          } else {
            throw new BatfishException(
                "Location.instantiate() - Source of abstract edge ("
                    + _head
                    + ") not valid Ip address.");
          }
        } else {
          Set<Location> outgoing =
              src.get().getAllOutgoingEdges().stream()
                  .map(e -> (Location) e)
                  .collect(Collectors.toSet());
          if (outgoing.isEmpty()) {
            throw new BatfishException(
                "Location.instantiate() - Source of abstract edge ("
                    + _head
                    + ") has no destinations.");
          } else {
            return outgoing;
          }
        }
      } else if (_tail != null) {
        Optional<Node> headNode = info.getNodeByName(_head);
        Optional<Node> tailNode = info.getNodeByName(_tail);
        Optional<Ip> headIp = Ip.tryParse(_head);
        Optional<Ip> tailIp = Ip.tryParse(_tail);
        if ((headNode.isEmpty() && headIp.isEmpty()) || (tailNode.isEmpty() && tailIp.isEmpty())) {
          throw new BatfishException(
              "Location.instantiate() - Unable to find edge corresponding to input ("
                  + _head
                  + " -> "
                  + _tail
                  + ") within network. Make sure to either use the node names or that the Ip addresses are correct for the connection you care about");
        } else {
          // look for edge in location set to get correct IP connection (regardless of node names)
          Optional<Edge> edge;
          if (tailNode.isPresent()) {
            if (headIp.isPresent()) {
              edge = tailNode.get().getIncomingFrom(headIp.get());
            } else {
              edge = tailNode.get().getIncomingFrom(headNode.get());
            }
          } else if (headNode.isPresent()) {
            // edge might exist if added already, but this case should only occur when edge is
            // outgoing (i.e. there is no node associated with the destination)
            edge = info.getOutgoingEdgeIfNeighborExists(headNode.get(), tailIp.get());
          } else {
            edge = info.checkForEdgeViaIps(headIp.get(), tailIp.get());
          }
          if (edge.isPresent()) {
            return Set.of(edge.get());
          } else {
            throw new BatfishException(
                "Location.instantiate() - Unable to find single edge corresponding to ("
                    + _head
                    + " -> "
                    + _tail
                    + ") in network. No config/node detected for either Ip address.");
          }
        }
      } else if (_head.equals("all-outgoing")) {
        return info.allEdgesLeavingNetwork();
      } else {
        Optional<Node> node = info.getNodeByName(_head);
        if (node.isEmpty()) {
          Optional<Ip> ip = Ip.tryParse(_head);
          if (ip.isPresent()) {
            Set<Location> associatedNodes = info.getNodesLinkedToIp(ip.get());
            if (associatedNodes.size() == 1) {
              return associatedNodes;
            } else {
              throw new BatfishException(
                  "Location.instantiate() - Unable to find single node for ip address ("
                      + _head
                      + ") in network. Found "
                      + associatedNodes.size()
                      + " nodes with ip address provided.");
            }
          } else {
            throw new BatfishException(
                "Location.instantiate() - Unable to find node or ip address corresponding to ("
                    + _head
                    + ") in network.");
          }
        } else {
          return Set.of(node.get());
        }
      }
    }
  }

  /// Builder for a list of locations (specifically, a list of Location.Builders from string)
  public static class Builders {
    private final String PROP_LOCATIONS = "locations";
    public final @Nonnull List<Builder> _builders;

    @JsonCreator
    public Builders(@JsonProperty(PROP_LOCATIONS) @Nullable java.util.List<Builder> builders) {
      _builders = builders == null ? List.of() : builders;
    }

    @JsonCreator
    @VisibleForTesting
    static Builders forValue(String value) {
      String[] splits = value.trim().split(",");
      ImmutableList.Builder<Builder> builders = ImmutableList.builder();
      for (String location : splits) {
        if (!location.trim().isEmpty()) {
          builders.add(Builder.forValue(location.trim()));
        }
      }
      return new Builders(builders.build());
    }

    public List<Location> instantiate(NetworkInfo info) {
      ImmutableList.Builder<Location> builder = ImmutableList.builder();
      _builders.forEach(loc -> builder.addAll(loc.instantiate(info)));
      return builder.build();
    }

    @Nonnull
    public List<Builder> get_builders() {
      return _builders;
    }
  }
}
