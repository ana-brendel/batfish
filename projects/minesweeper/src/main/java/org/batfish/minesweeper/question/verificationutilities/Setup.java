package org.batfish.minesweeper.question.verificationutilities;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.batfish.common.BatfishException;
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
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.communities.CommunityMatchExprVarCollector;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;

import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.batfish.datamodel.answers.Schema.STRING;

public class Setup {

    /// Used to get any extra regexes from configs for creating the atomic predicates...
    /// I believe the line that gets the community from the configs is redundant based on how we process the configs
    private static Set<CommunityVar> getCommunityVars(Set<RegexConstraint> communityRegexes, Collection<Configuration> configs) {
        Set<CommunityVar> communityVars = new HashSet<>();
        for (RegexConstraint rc : communityRegexes) {
            String regex = rc.getRegex();
            switch (rc.getRegexType()) {
                case REGEX -> communityVars.addAll(ImmutableList.of(CommunityVar.from(regex)));
                case STRUCTURE_NAME ->
                        configs.forEach(config -> {
                            if (config.getCommunityMatchExprs().containsKey(regex)) {
                                communityVars.addAll(config.getCommunityMatchExprs()
                                        .get(regex)
                                        .accept(new CommunityMatchExprVarCollector(), config));
                            }
                        });
            }
        }
        return communityVars;
    }

    /// Returns relevant ConfigAtomicPredicates (code copied from SearchRoutePoliciesAnswerer and modified)
    public static ConfigAtomicPredicates getConfigAtomicPredicates(
            Set<RegexConstraint> communityRegexes, Set<RegexConstraint> asPathRegexes, Collection<Configuration> configs) {
        return new ConfigAtomicPredicates(
                configs.stream().map(config -> {
                    Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                    // need to create variables to adhere to types
                    return (Map.Entry<Configuration, Collection<RoutingPolicy>>) new AbstractMap.SimpleImmutableEntry<>(config, policies);
                } ).toList(),
                getCommunityVars(communityRegexes,configs), // need to add atomic predicates for communities exclusive to the provided properties
                asPathRegexes.stream().map(RegexConstraint::getRegex).collect(ImmutableSet.toImmutableSet())); // should be empty, not handling as path yet
    }

    /// This function takes the provided invariants and builds them in the context of the current network and tbdd
    public static Map.Entry<Location, Invariant> buildInvariant(NetworkInfo info, boolean wpQuery, Map.Entry<Location.Builder, Invariant.Builder> entry) {
        RoutingPolicy policy;
        Location location = entry.getKey().instantiate(info);
        boolean getImportPolicy = (location instanceof Edge) != wpQuery;
        if (location instanceof Edge edge) {
            policy = info.getPolicy(edge,getImportPolicy);
        } else if (location instanceof Node node) {
            policy = info.getPolicy(info.getAnyIncomingEdge(node),getImportPolicy);
        } else {
            throw new BatfishException("This should be unreachable.");
        }
        return new AbstractMap.SimpleEntry<>(entry.getKey().instantiate(info),entry.getValue().build(info.tbdd,policy));
    }

    /// In cases where there is some counterexample, format counterexample in a more readable manner
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

    // Constants for metadata definitions
    public static final String LOCATION_COL = "Network_Location";
    public static final String ASSUMPTION_COL = "Initial_Assumption";
    public static final String TARGET_COL = "Target_Property";
    public static final String INFERRED_INVARIANTS_COL = "Inferred_Invariant";
    public static final String VERIFICATION_VIOLATION_COL = "Verification_Violation";
    public static final String LOCATION_RELEVANCE_COL = "Location_Relevance";
    public static final String PROVIDED_INVARIANT_COL = "Provided_Invariant";
    public static final String COUNTEREXAMPLE_COL = "Counterexample";

    /// TableMetadata for safety property which displays all invariants inferred across network
    public static TableMetadata metadata_safety() {
        List<ColumnMetadata> columnMetadata =
                ImmutableList.of(
                        new ColumnMetadata(LOCATION_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(ASSUMPTION_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(TARGET_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(INFERRED_INVARIANTS_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(VERIFICATION_VIOLATION_COL, STRING, "InDev", true, false));
        return new TableMetadata(
                columnMetadata, "Invariant Inference and Verification Results");
    }

    /// TableMetadata for safety property which displays target properties and assumptions and any counterexamples
    public static TableMetadata metadata_safety_limited() {
        List<ColumnMetadata> columnMetadata =
                ImmutableList.of(
                        new ColumnMetadata(LOCATION_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(LOCATION_RELEVANCE_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(PROVIDED_INVARIANT_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(INFERRED_INVARIANTS_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(COUNTEREXAMPLE_COL, STRING, "InDev", true, false));
        return new TableMetadata(
                columnMetadata, "Invariant Inference and Verification Results");
    }

    /// TableMetadata for displaying just the locations within the network
    public static TableMetadata metadata_locations() {
        List<ColumnMetadata> columnMetadata =
                ImmutableList.of(new ColumnMetadata(LOCATION_COL, STRING, "InDev", true, false));
        return new TableMetadata(
                columnMetadata, "Invariant Inference and Verification Results");
    }
}
