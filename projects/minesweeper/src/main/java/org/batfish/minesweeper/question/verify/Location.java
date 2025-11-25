package org.batfish.minesweeper.question.verify;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.List;

public abstract class Location {
    abstract Location copy();

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
                return new Builder(null,null,value.trim());
            } else if (splits.length == 2) {
                return new Builder(splits[0].trim(),splits[1].trim(),null);
            } else {
                throw new BatfishException("String parsing into location (NetworkLocation) failed. " +
                        "An edge should be 'src -> dst' and a node should just be 'nodeName'.");
            }
        }

        /// Gets the Location based on the Verifier (which is based on Network Snapshot)
        /// -- maybe change to only succeed if provided with IPs
        public Location instantiate(Verifier v) {
            if (_head != null && _tail != null) {
                Ip head = Ip.tryParse(_head).orElseGet(() -> v.ipFromNodeName(_head).orElse(null));
                Ip tail = Ip.tryParse(_tail).orElseGet(() -> v.ipFromNodeName(_tail).orElse(null));
                assert head != null && tail != null;
                return new Edge(head,tail);
            } else {
                assert _head != null;
                Ip head = Ip.tryParse(_head).orElseGet(() -> v.ipFromNodeName(_head).orElse(null));
                assert head != null;
                return new Node(head,_head);
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

        public List<Location> instantiate(Verifier v) {
            ImmutableList.Builder<Location> builder = ImmutableList.builder();
            _builders.forEach(loc -> builder.add(loc.instantiate(v)));
            return builder.build();
        }

        @Nonnull
        public List<Builder> get_builders() {
            return _builders;
        }
    }
}
