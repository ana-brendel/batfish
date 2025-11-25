package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.BgpRoute;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.OriginMechanism;
import org.batfish.datamodel.ReceivedFromSelf;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.ColumnMetadata;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.datamodel.table.TableMetadata;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.communities.CommunityMatchExprVarCollector;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.batfish.datamodel.answers.Schema.STRING;

public final class VerifierAnswerer extends Answerer {
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets;
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions;
    private final @Nonnull Set<RegexConstraint> _communityRegexes;
    private final @Nonnull Set<RegexConstraint> _asPathRegexes;
    private final boolean _readable;

    public VerifierAnswerer(VerifierQuestion question, IBatfish batfish) {
        super(question, batfish);
        _readable = question.get_readable();
        _targets = question.get_targets();

        // this is added because the assumptions are taken as two lists with corresponding inputs
        List<Invariant.Builder> invAssumptions = question.get_assumptions().isPresent() ?
                question.get_assumptions().get().get_builders() : List.of();
        List<Location.Builder> locAssumptions = question.get_assumption_locations().isPresent() ?
                question.get_assumption_locations().get().get_builders() : List.of();
        assert invAssumptions.size() == locAssumptions.size() ;
        _assumptions = new HashMap<>();
        for (int i = 0; i < invAssumptions.size(); i++) {
            _assumptions.put(locAssumptions.get(i),invAssumptions.get(i));
        }

        _communityRegexes = new HashSet<>();
        _asPathRegexes = new HashSet<>(); // not included in the NetworkClause nor Invariant class yet
        _targets.values().forEach(clauses -> clauses.getClauses()
                .forEach(c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints())));
    }

    /// Used to get any extra regexes from configs for creating the atomic predicates...
    ///  this might be redundant based on how we get the first argument for the ConfigAtomicPredicate constructor
    private Set<CommunityVar> getCommunityVars(Collection<Configuration> configs) {
        Set<CommunityVar> communityVars = new HashSet<>();
        for (RegexConstraint rc : _communityRegexes) {
            String regex = rc.getRegex();
            switch (rc.getRegexType()) {
                case REGEX -> communityVars.addAll(ImmutableList.of(CommunityVar.from(regex)));
                case STRUCTURE_NAME ->
                        configs.forEach(config -> {
                            if (config.getCommunityMatchExprs().containsKey(regex))
                                communityVars.addAll(config.getCommunityMatchExprs()
                                    .get(regex)
                                    .accept(new CommunityMatchExprVarCollector(), config));
                        });
            };
        }
        return communityVars;
    }

    // code copied from SearchRoutePoliciesAnswerer and modified
    private ConfigAtomicPredicates getConfigAtomicPredicates(Collection<Configuration> configs) {
        return new ConfigAtomicPredicates(
                configs.stream().map(config -> {
                    Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                    return (Map.Entry<Configuration, Collection<RoutingPolicy>>) new AbstractMap.SimpleImmutableEntry<Configuration, Collection<RoutingPolicy>>(config, policies); // need to create variables to adhere to types
                } ).toList(),
                getCommunityVars(configs),
                _asPathRegexes.stream().map(RegexConstraint::getRegex).collect(ImmutableSet.toImmutableSet()));
    }

    private Map.Entry<Location, Invariant> buildInvariant(Verifier verifier, boolean wpQuery, Map.Entry<Location.Builder, Invariant.Builder> entry) {
        RoutingPolicy policy;
        Location location = entry.getKey().instantiate(verifier);
        if (location instanceof Edge edge) {
            policy = verifier.getPolicy(edge,!wpQuery);
        } else if (location instanceof Node node) {
            policy = verifier.getPolicy(verifier.getAnyIncomingEdge(node),wpQuery);
        } else {
            throw new BatfishException("This should be unreachable.");
        }
        return new AbstractMap.SimpleEntry<>(entry.getKey().instantiate(verifier),entry.getValue().build(verifier.getTBDD(),policy));
    }

    private static TableMetadata metadata() {
        List<ColumnMetadata> columnMetadata =
                ImmutableList.of(
                        new ColumnMetadata("Assumption_Location", STRING, "InDev", true, false),
                        new ColumnMetadata("Assumption", STRING, "InDev", true, false),
                        new ColumnMetadata("Overall_Verification_Result", STRING, "InDev", true, false),
                        new ColumnMetadata("Assumption_Verification_Result", STRING, "InDev", true, false),
                        new ColumnMetadata("Assumption_Violation", STRING, "InDev", true, false));
        return new TableMetadata(
                columnMetadata, String.format("Results for route ${%s}", "Network_Locations"));
    }

    private static String nonDefaultRoute(Bgpv4Route route) {
        ImmutableList.Builder<String> features = ImmutableList.builder();
        // Always include the IP address
        features.add("network=" + route.getNetwork());
        if (route.getAdministrativeCost() != 0)
            features.add("admin=" + route.getAdministrativeCost());
        if (route.getTag() != 0)
            features.add("tag=" + route.getTag());
        if (route.getAsPath().length() != 0)
            features.add("asPath=" + route.getAsPath());
        if (!route.getClusterList().isEmpty())
            features.add("clusterList=" + route.getClusterList());
        if (!route.getCommunities().getCommunities().isEmpty())
            features.add("communities=" + route.getCommunities());
        if (route.getLocalPreference() != BgpRoute.DEFAULT_LOCAL_PREFERENCE)
            features.add("localPreference=" + route.getLocalPreference());
        if (route.getMetric() != 0)
            features.add("med=" + route.getMetric());
        //if (route.getNextHop() != ...)
            //features.add("nextHop=" + route.getNextHop());
        if (!route.getOriginatorIp().equals(Ip.ZERO))
             features.add("originatorIp=" + route.getOriginatorIp());
        if (route.getOriginMechanism() != OriginMechanism.LEARNED)
            features.add("originMechanism=" + route.getOriginMechanism().name());
        //if (route.getOriginType() != OriginType.INCOMPLETE)
            //features.add("originType=" + route.getOriginType().name());
        if (route.getProtocol() != RoutingProtocol.BGP)
            features.add("srcProtocol=" + route.getProtocol().name());
        if (route.getReceivedFrom() != ReceivedFromSelf.instance())
            features.add("receivedFrom=" + route.getReceivedFrom());
        if (route.getReceivedFromRouteReflectorClient())
            features.add("receivedFromRouteReflectorClient=" + true);
        //features.add("srcProtocol=" + route.getSrcProtocol().name());
        if (route.getWeight() != 0)
            features.add("weight=" + route.getWeight());
        return "Bgpv4Route{" + String.join(", ", features.build()) + "}";
    }

    private TableAnswerElement getAnswerElement(List<String> prefixesForDisplay, Verifier.Result result, Verifier verifier) {
        TableAnswerElement tae = new TableAnswerElement(metadata());
        verifier.getAssumptions().forEach((loc,prop) -> tae.addRow(Row.builder()
                .put("Assumption_Location", loc.toString())
                .put("Assumption", _readable ? prop.weakDisplay(prefixesForDisplay) : prop.str)
                .put("Overall_Verification_Result", result.verified())
                .put("Assumption_Verification_Result", result.checks().get(loc).isEmpty())
                .put("Assumption_Violation", _readable ? result.invariants().get(loc).weakDisplay(prefixesForDisplay) :
                        result.checks().get(loc).isPresent() ?  nonDefaultRoute(result.checks().get(loc).get()) : "").build()));
        return tae;
    }

    // Related to the weak display
    private static List<String> getPrefixesConsideredForDisplay(Collection<Configuration> configs) {
        ImmutableList.Builder<String> builder = ImmutableList.builder();
        configs.forEach(config -> config.getRouteFilterLists().values()
                .forEach(rfl -> rfl.getLines()
                        .forEach(line -> builder.add(line.getIpWildcard().toString()))));
        return builder.build();
    }

    @Override
    public AnswerElement answer(NetworkSnapshot snapshot) {
        SpecifierContext context = _batfish.specifierContext(snapshot);
        Map<String, Configuration> configs = context.getConfigs();
        List<String> prefixesForDisplay = _readable ? getPrefixesConsideredForDisplay(configs.values()) : List.of();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values());
        TransferBDD tbdd = new TransferBDD(configAPs);
        Verifier verifier = new Verifier(tbdd,configs);
        _targets.entrySet().stream()
                .map(e -> buildInvariant(verifier,true,e))
                .forEach(e -> verifier.addProperty(e.getKey(),e.getValue()));
        _assumptions.forEach(verifier::addAssumption);
        Verifier.Result result = verifier.run();
        return getAnswerElement(prefixesForDisplay,result,verifier);
    }
}
