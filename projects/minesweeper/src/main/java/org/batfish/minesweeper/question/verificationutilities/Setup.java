package org.batfish.minesweeper.question.verificationutilities;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.datamodel.BgpPeerConfig;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.BgpRoute;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.OriginMechanism;
import org.batfish.datamodel.ReceivedFromSelf;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.ColumnMetadata;
import org.batfish.datamodel.table.TableMetadata;
import org.batfish.minesweeper.BgpLoopTracking;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.communities.CommunityMatchExprVarCollector;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.batfish.datamodel.answers.Schema.STRING;

public class Setup {
  private static final Logger LOGGER = LogManager.getLogger(Setup.class);

  /// Used to get any extra regexes from configs for creating the atomic predicates...
  /// I believe the line that gets the community from the configs is redundant based on how we
  // process the configs
  private static Set<CommunityVar> getCommunityVars(
      Set<RegexConstraint> communityRegexes, Collection<Configuration> configs) {
    Set<CommunityVar> communityVars = new HashSet<>();
    for (RegexConstraint rc : communityRegexes) {
      String regex = rc.getRegex();
      switch (rc.getRegexType()) {
        case REGEX -> communityVars.addAll(ImmutableList.of(CommunityVar.from(regex)));
        case STRUCTURE_NAME ->
            configs.forEach(
                config -> {
                  if (config.getCommunityMatchExprs().containsKey(regex)) {
                    communityVars.addAll(
                        config
                            .getCommunityMatchExprs()
                            .get(regex)
                            .accept(new CommunityMatchExprVarCollector(), config));
                  }
                });
      }
    }
    return communityVars;
  }

  /// Returns relevant ConfigAtomicPredicates for all policies in all configs
  public static ConfigAtomicPredicates getConfigAtomicPredicates(
      Set<RegexConstraint> communityRegexes,
      Set<RegexConstraint> asPathRegexes,
      Collection<Configuration> configs) {
    int policyCount =
        configs.stream().map(c -> c.getRoutingPolicies().size()).reduce(0, Integer::sum);
    LOGGER.info("Policies in all configs: {}", policyCount);
    Map<Configuration, Collection<RoutingPolicy>> configAndPolicies = new HashMap<>();
    configs.forEach(config -> configAndPolicies.put(config, config.getRoutingPolicies().values()));
    return getConfigAtomicPredicates(communityRegexes, asPathRegexes, configAndPolicies);
  }

  /// Returns relevant ConfigAtomicPredicates for the policies present in the map
  public static ConfigAtomicPredicates getConfigAtomicPredicates(
      Set<RegexConstraint> communityRegexes,
      Set<RegexConstraint> asPathRegexes,
      Map<Configuration, Collection<RoutingPolicy>> configAndPolicies) {
    int policyCount =
        configAndPolicies.values().stream().map(Collection::size).reduce(0, Integer::sum);
    LOGGER.info("Policies in relevant configs: {}", policyCount);
    return new ConfigAtomicPredicates(
        configAndPolicies.entrySet().stream().toList(),
        getCommunityVars(communityRegexes, configAndPolicies.keySet()),
        asPathRegexes.stream()
            .map(RegexConstraint::getRegex)
            .collect(ImmutableSet.toImmutableSet()),
        loopTracking(configAndPolicies.keySet()));
  }

  /// The BGP loop-prevention state that symbolic routes track for the given configs:
  ///
  /// - every local AS and confederation AS number configured on a BGP session, since a receiver's
  ///   AS-path loop check looks for the AS it uses on the session, which is one of these;
  /// - every local AS configured on a session of a router in a confederation, which is the member
  ///   AS that the router adds as a confederation segment;
  /// - every cluster ID of a BGP process that has a route-reflector client. A router adds a cluster
  ///   ID to a route only when it reflects the route, which needs a client, so the cluster IDs of
  ///   other routers are never in a route's cluster list as far as the model knows;
  /// - every BGP process's router ID, which its originator check looks for, if some process has a
  ///   route-reflector client. Without reflection a route never comes back over iBGP to the router
  ///   that injected it.
  ///
  /// The loop-prevention excuses only ever allow routes for which this state is set, so state that
  /// nothing in the model sets cannot change a verdict: it can only be set on a route entering the
  /// network, which must satisfy its requirement whatever that state is.
  ///
  /// That relies on assumptions about incoming routes saying nothing about this state, as is the
  /// case today. If an assumption could say, for example, that the routes from some neighbor have a
  /// given cluster ID in their cluster list, or a given originator ID, then the routers that check
  /// it would drop those routes, and the cluster ID or router ID would have to be tracked even if
  /// nothing in the network sets it. Otherwise the excuse is lost. That cannot make the analysis
  /// unsound, since pruning only ever removes excuses, but it can add false positives.
  private static BgpLoopTracking loopTracking(Collection<Configuration> configs) {
    Set<Long> ases = new TreeSet<>();
    Set<Long> confedAses = new TreeSet<>();
    Set<Long> clusterIds = new TreeSet<>();
    Set<Ip> routerIds = new TreeSet<>();
    boolean reflection = false;
    for (Configuration config : configs) {
      if (config.getDefaultVrf() == null || config.getDefaultVrf().getBgpProcess() == null) {
        continue;
      }
      BgpProcess process = config.getDefaultVrf().getBgpProcess();
      for (BgpPeerConfig peer : process.getActiveNeighbors().values()) {
        if (peer.getLocalAs() != null) {
          ases.add(peer.getLocalAs());
        }
        if (peer.getConfederationAsn() != null) {
          ases.add(peer.getConfederationAsn());
          if (peer.getLocalAs() != null) {
            confedAses.add(peer.getLocalAs());
          }
        }
      }
      boolean hasClient =
          process.getActiveNeighbors().values().stream()
              .anyMatch(
                  peer ->
                      peer.getIpv4UnicastAddressFamily() != null
                          && peer.getIpv4UnicastAddressFamily().getRouteReflectorClient());
      if (hasClient) {
        reflection = true;
        clusterIds.addAll(process.getClusterIds());
      }
      if (process.getRouterId() != null) {
        routerIds.add(process.getRouterId());
      }
    }
    return new BgpLoopTracking(
        ImmutableList.copyOf(ases),
        ImmutableList.copyOf(confedAses),
        ImmutableList.copyOf(clusterIds),
        reflection ? ImmutableList.copyOf(routerIds) : ImmutableList.of());
  }

  /// This function takes the provided invariants and builds them in the context of the current
  /// network and tbdd
  public static Map.Entry<Location, Invariant> buildTargetLocationInvariant(
      NetworkInfo info, boolean wpQuery, Map.Entry<Location.Builder, Invariant.Builder> entry) {
    Set<Location> locations = entry.getKey().instantiate(info);
    assert locations.size() == 1;
    Location location = locations.stream().findFirst().get();
    Invariant invariant = info.buildInvariant(location, entry.getValue(), wpQuery, false);
    return Pair.of(location, invariant);
  }

  /// In cases where there is some counterexample, format counterexample in a more readable manner
  /// (There might be some oversimplification or inaccurate simplifications - always include IP.)
  public static String nonDefaultRoute(Bgpv4Route route) {
    ImmutableList.Builder<String> features = ImmutableList.builder();
    // Always include the IP address
    features.add("network=" + route.getNetwork());
    if (route.getAdministrativeCost() != 0) {
      features.add("admin=" + route.getAdministrativeCost());
    }
    if (route.getTag() != 0) {
      features.add("tag=" + route.getTag());
    }
    if (route.getAsPath().length() != 0) {
      features.add("asPath=" + route.getAsPath());
    }
    if (!route.getClusterList().isEmpty()) {
      features.add("clusterList=" + route.getClusterList());
    }
    if (!route.getCommunities().getCommunities().isEmpty()) {
      features.add("communities=" + route.getCommunities());
    }
    if (route.getLocalPreference() != BgpRoute.DEFAULT_LOCAL_PREFERENCE) {
      features.add("localPreference=" + route.getLocalPreference());
    }
    if (route.getMetric() != 0) {
      features.add("med=" + route.getMetric());
    }
    // if (route.getNextHop() != ...)
    // features.add("nextHop=" + route.getNextHop());
    if (!route.getOriginatorIp().equals(Ip.ZERO)) {
      features.add("originatorIp=" + route.getOriginatorIp());
    }
    if (route.getOriginMechanism() != OriginMechanism.LEARNED) {
      features.add("originMechanism=" + route.getOriginMechanism().name());
    }
    // if (route.getOriginType() != OriginType.INCOMPLETE)
    // features.add("originType=" + route.getOriginType().name());
    if (route.getProtocol() != RoutingProtocol.BGP) {
      features.add("srcProtocol=" + route.getProtocol().name());
    }
    if (route.getReceivedFrom() != ReceivedFromSelf.instance()) {
      features.add("receivedFrom=" + route.getReceivedFrom());
    }
    if (route.getReceivedFromRouteReflectorClient()) {
      features.add("receivedFromRouteReflectorClient=" + true);
    }
    // features.add("srcProtocol=" + route.getSrcProtocol().name());
    if (route.getWeight() != 0) {
      features.add("weight=" + route.getWeight());
    }
    return "Bgpv4Route{" + String.join(", ", features.build()) + "}";
  }

  // columns for displaying safety results
  public static final String LOCATION_RELEVANCE_COL = "Location_Relevance";
  public static final String PROVIDED_INVARIANT_COL = "Provided_Invariant";
  public static final String LOCATIONS_COL = "Network_Locations";
  public static final String INFERRED_INVARIANTS_COL = "Inferred_Invariant";
  public static final String COUNTEREXAMPLE_COL = "Counterexample";

  // columns for displaying liveness results
  public static final String RESULT_LABEL_COL = "Result_Label";
  public static final String RESULT_VALUE_COL = "Result";
  public static final String OVERALL_RESULT = "Liveness Property Verified?";
  public static final String GOOD_PATH_LABEL = "Good Path";
  public static final String BAD_PATH_LABEL = "Failed Path";
  public static final String SOURCE_OF_INTERFERENCE = "Potential Interference from ";

  // columns for just displaying the locations
  public static final String NODES_COL = "Nodes";
  public static final String CONNECTION_TYPE_COL = "Connection_Type";
  public static final String DESTINATION_COL = "Local_Ip";
  public static final String NEIGHBORS_COL = "Remote_Ips";

  /// TableMetadata for safety property which displays target properties and assumptions and any
  /// counterexamples
  public static TableMetadata metadata_safety() {
    List<ColumnMetadata> columnMetadata =
        ImmutableList.of(
            new ColumnMetadata(LOCATION_RELEVANCE_COL, STRING, "InDev", true, false),
            new ColumnMetadata(PROVIDED_INVARIANT_COL, STRING, "InDev", true, false),
            new ColumnMetadata(LOCATIONS_COL, STRING, "InDev", true, false),
            new ColumnMetadata(INFERRED_INVARIANTS_COL, STRING, "InDev", true, false),
            new ColumnMetadata(COUNTEREXAMPLE_COL, STRING, "InDev", true, false));
    return new TableMetadata(columnMetadata, "Invariant Inference and Verification Results");
  }

  public static TableMetadata metadata_liveness() {
    List<ColumnMetadata> columnMetadata =
        ImmutableList.of(
            new ColumnMetadata(RESULT_LABEL_COL, STRING, "InDev", true, false),
            new ColumnMetadata(RESULT_VALUE_COL, STRING, "InDev", true, false));
    return new TableMetadata(columnMetadata, "Liveness Verification Results");
  }

  /// TableMetadata for displaying just the locations within the network
  public static TableMetadata metadata_locations() {
    List<ColumnMetadata> columnMetadata =
        ImmutableList.of(
            new ColumnMetadata(NODES_COL, STRING, "InDev", true, false),
            new ColumnMetadata(CONNECTION_TYPE_COL, STRING, "InDev", true, false),
            new ColumnMetadata(DESTINATION_COL, STRING, "InDev", true, false),
            new ColumnMetadata(NEIGHBORS_COL, STRING, "InDev", true, false));
    return new TableMetadata(columnMetadata, "Invariant Inference and Verification Results");
  }
}
