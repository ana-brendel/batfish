package org.batfish.minesweeper.question.verificationutilities;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

public abstract class Location implements Comparable<Location> {
  public abstract Location copy();

  public abstract String contextString(Map<Ip, Node> nodes);

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
        _head = node;
        _tail = null;
      } else {
        assert src != null && dst != null;
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
                + "An edge should be 'src -> dst' and a node should just be 'nodeName'.");
      }
    }

    /// Gets the Location based on the Verifier (which is based on Network Snapshot)
    /// -- maybe change to only succeed if provided with IPs
    public Location instantiate(NetworkInfo info) {
      if (_head != null && _tail != null) {
        Collection<Ip> heads =
            info.ipsFromNodeName(_head)
                .orElse(Ip.tryParse(_head).<Collection<Ip>>map(Set::of).orElse(null));
        Collection<Ip> tails =
            info.ipsFromNodeName(_tail)
                .orElse(Ip.tryParse(_tail).<Collection<Ip>>map(Set::of).orElse(null));
        if (heads == null || tails == null || heads.isEmpty() || tails.isEmpty()) {
          throw new BatfishException(
              "Location.instantiate() - Unable to find edge corresponding to input ("
                  + _head
                  + " -> "
                  + _tail
                  + ") within network.");
        } else {
          // look for edge in location set to guarantee ips used are correct (specifically, when
          // just provided with node's name)
          Optional<Edge> edge =
              heads.stream()
                  .flatMap(head -> tails.stream().map(tail -> new Edge(head, tail)))
                  .filter(info::containsPolicy)
                  .findFirst();
          if (edge.isEmpty()) {
            // if there is no policies found for provided edge, we can do best guess (might throw
            // error)
            Ip head =
                Ip.tryParse(_head)
                    .orElse(
                        info.ipsFromNodeName(_head).orElse(Set.of()).stream()
                            .findFirst()
                            .orElse(null));
            Ip tail =
                Ip.tryParse(_tail)
                    .orElse(
                        info.ipsFromNodeName(_tail).orElse(Set.of()).stream()
                            .findFirst()
                            .orElse(null));
            assert head != null && tail != null;
            return new Edge(head, tail);
          } else {
            return edge.get();
          }
        }
      } else {
        assert _head != null;
        Collection<Ip> ips =
            info.ipsFromNodeName(_head)
                .orElse(Ip.tryParse(_head).<Collection<Ip>>map(Set::of).orElse(null));
        if (ips == null || ips.isEmpty()) {
          throw new BatfishException(
              "Location.instantiate() - Unable to find node corresponding to ("
                  + _head
                  + ") in network.");
        } else {
          return new Node(ips, _head);
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
        builders.add(Builder.forValue(location.trim()));
      }
      return new Builders(builders.build());
    }

    public List<Location> instantiate(NetworkInfo info) {
      ImmutableList.Builder<Location> builder = ImmutableList.builder();
      _builders.forEach(loc -> builder.add(loc.instantiate(info)));
      return builder.build();
    }

    @Nonnull
    public List<Builder> get_builders() {
      return _builders;
    }
  }
}
