package org.batfish.minesweeper.question.safety;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
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
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.batfish.datamodel.answers.Schema.STRING;

// Currently the question takes in a single target location-invariant pair whereas the assumptions might be a list
public final class SafetyAnswerer extends Answerer {
    private static final Logger LOGGER = LogManager.getLogger(SafetyAnswerer.class);

    private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets;
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions;
    private final @Nonnull Set<RegexConstraint> _communityRegexes;
    private final @Nonnull Set<RegexConstraint> _asPathRegexes;
    private final boolean _readable;

    public SafetyAnswerer(SafetyQuestion question, IBatfish batfish) {
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
        invAssumptions.forEach(clauses -> clauses.getClauses()
                .forEach(c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints())));
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
                    // need to create variables to adhere to types
                    return (Map.Entry<Configuration, Collection<RoutingPolicy>>) new AbstractMap.SimpleImmutableEntry<Configuration, Collection<RoutingPolicy>>(config, policies);
                } ).toList(),
                getCommunityVars(configs), // need to add atomic predicates for communities exclusive to the provided properties
                _asPathRegexes.stream().map(RegexConstraint::getRegex).collect(ImmutableSet.toImmutableSet())); // should be empty, not handling as path yet
    }

    /// This function takes the provided invariants and builds them in the context of the current network and tbdd
    private Map.Entry<Location, Invariant> buildInvariant(Infer verifier, boolean wpQuery, Map.Entry<Location.Builder, Invariant.Builder> entry) {
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

    private static final String LOCATION_COL = "Network_Location";
    private static final String ASSUMPTION_COL = "Initial_Assumption";
    private static final String TARGET_COL = "Target_Property";
    private static final String INFERRED_INVARIANTS_COL = "Inferred_Invariant";
    private static final String OVERALL_VERIFICATION_COL = "Overall_Verification_Result";
    private static final String LOCAL_VERIFICATION_COL = "Local_Verification_Result";
    private static final String ASSUMPTION_VIOLATION_COL = "Assumption_Violation";

    private static TableMetadata metadata() {
        List<ColumnMetadata> columnMetadata =
                ImmutableList.of(
                        new ColumnMetadata(LOCATION_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(ASSUMPTION_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(TARGET_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(INFERRED_INVARIANTS_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(OVERALL_VERIFICATION_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(LOCAL_VERIFICATION_COL, STRING, "InDev", true, false),
                        new ColumnMetadata(ASSUMPTION_VIOLATION_COL, STRING, "InDev", true, false));
        return new TableMetadata(
                columnMetadata, "Invariant Inference and Verification Results");
    }

    /// In cases where there is some counterexample, format counterexample in a more readable manner
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

    /// Gather the answer element needed for a question return
    private TableAnswerElement getAnswerElement(
            boolean refinementOccurred, Map<Location, Optional<Bgpv4Route>> checks, Refine.Result refinement, Infer verifier) {
        Map<Location,Invariant> results = refinement.refined();
        Map<Location,String> result_str = new HashMap<>(results.size());
        Map<BDD,String> cache = new HashMap<>();
        if (_readable) {
            results.forEach((l, i) -> result_str.put(l, i.toString(refinementOccurred,verifier.shortcuts, cache)));
        } else {
            // we only get strings for the targets and assumptions, or if true or false (saves time)
            results.forEach((l, i) -> {
                if (verifier.getTargets().containsKey(l) || verifier.getAssumptions().containsKey(l) || i.isFalse() || i.isTrue())
                    result_str.put(l, i.toString(refinementOccurred,verifier.shortcuts, cache));
                else
                    result_str.put(l,"...");
            });
        }
        TableAnswerElement tae = new TableAnswerElement(metadata());
        results.keySet().stream().sorted()
                .forEach(loc -> tae.addRow(Row.builder()
                .put(LOCATION_COL, loc.toString())
                .put(ASSUMPTION_COL, verifier.getAssumptions().containsKey(loc) ?
                        verifier.getAssumptions().get(loc).toString(refinementOccurred,verifier.shortcuts,cache) : "-")
                .put(TARGET_COL, verifier.getTargets().containsKey(loc) ?
                        verifier.getTargets().get(loc).toString(refinementOccurred,verifier.shortcuts,cache) : "-")
                .put(INFERRED_INVARIANTS_COL, result_str.containsKey(loc) && result_str.get(loc).isEmpty() ?
                        "STRING OF BDD ERROR" : result_str.get(loc))
                .put(OVERALL_VERIFICATION_COL, refinement.verified())
                .put(LOCAL_VERIFICATION_COL, checks.containsKey(loc) ? checks.get(loc).isEmpty() : "")
                .put(ASSUMPTION_VIOLATION_COL, checks.containsKey(loc) && checks.get(loc).isPresent()
                        ? nonDefaultRoute(checks.get(loc).get()) : "").build()));
        return tae;
    }

    @Override
    public AnswerElement answer(NetworkSnapshot snapshot) {
        LOGGER.info("Within the answerer for verification.");
        SpecifierContext context = _batfish.specifierContext(snapshot);
        Map<String, Configuration> configs = context.getConfigs();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values());
        TransferBDD tbdd = new TransferBDD(configAPs);
        Infer verifier = new Infer(tbdd,configs);
        LOGGER.info(verifier.displayNodes());
        _targets.entrySet().stream()
                .map(e -> buildInvariant(verifier,true,e))
                .forEach(e -> verifier.addProperty(e.getKey(),e.getValue()));
        _assumptions.forEach(verifier::addAssumption);
        Infer.Result result = verifier.run();
        Refine.Result refined;
        boolean refinementOccurred = true;
        // we only want to refine if the inference did not yield any falses
        if (result.counter().isPresent()) {
            refinementOccurred = false;
            refined = verifier.refiner().noRefinement();
        } else {
            refined = verifier.refiner().refine();
        }
        assert result.verified() == refined.verified();
        return getAnswerElement(refinementOccurred,result.checks(),refined,verifier);
    }
}
