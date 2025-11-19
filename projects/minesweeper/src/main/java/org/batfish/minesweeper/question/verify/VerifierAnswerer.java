package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.communities.CommunityMatchExprVarCollector;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import java.util.AbstractMap;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

public final class VerifierAnswerer extends Answerer {
    private final @Nonnull Map<Location, Invariant.Builder> _targets;
    private final @Nonnull Set<Location> _assumptions;
    private final @Nonnull Set<Map.Entry<Configuration,RegexConstraint>> _communityRegexes;
    private final @Nonnull Set<Map.Entry<Configuration,RegexConstraint>> _asPathRegexes;

    public VerifierAnswerer(VerifierQuestion question, IBatfish batfish) {
        super(question, batfish);
        _targets = question.getTargets();
        _assumptions = question.getAssumptions();
        _communityRegexes = question.getCommunityRegexes();
        _asPathRegexes = question.getAsPathRegexes();
    }

    // code copied from SearchRoutePoliciesAnswerer
    public ConfigAtomicPredicates getConfigAtomicPredicates(Collection<Configuration> configs) {
        return new ConfigAtomicPredicates(
                configs.stream().map(config -> {
                    Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                    return (Map.Entry<Configuration, Collection<RoutingPolicy>>) new AbstractMap.SimpleImmutableEntry<Configuration, Collection<RoutingPolicy>>(config, policies); // need to create variables to adhere to types
                } ).toList(),
                _communityRegexes.stream()
                        .flatMap(
                                entry -> {
                                    String regex = entry.getValue().getRegex();
                                    return switch (entry.getValue().getRegexType()) {
                                        case REGEX -> ImmutableList.of(CommunityVar.from(regex)).stream();
                                        case STRUCTURE_NAME ->
                                                entry.getKey()
                                                        .getCommunityMatchExprs()
                                                        .get(regex)
                                                        .accept(new CommunityMatchExprVarCollector(), entry.getKey())
                                                        .stream();
                                    };
                                })
                        .collect(ImmutableSet.toImmutableSet()),
                _asPathRegexes.stream().map(Map.Entry::getValue)
                        .map(RegexConstraint::getRegex)
                        .collect(ImmutableSet.toImmutableSet()));
    }

    public Map.Entry<Location, Invariant> buildInvariant(Verifier verifier, boolean wpQuery, Map.Entry<Location, Invariant.Builder> entry) {
        RoutingPolicy policy;
        if (entry.getKey() instanceof Edge edge) {
            policy = verifier.getPolicy(edge,!wpQuery);
        } else if (entry.getKey() instanceof Node node) {
            policy = verifier.getPolicy(verifier.getAnyIncomingEdge(node),wpQuery);
        } else {
            throw new BatfishException("This should be unreachable.");
        }
        return new AbstractMap.SimpleEntry<>(entry.getKey(), entry.getValue().build(verifier.getTBDD(),policy));
    }

    @Override
    public AnswerElement answer(NetworkSnapshot snapshot) {
        SpecifierContext context = _batfish.specifierContext(snapshot);
        Map<String, Configuration> configs = context.getConfigs();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values());
        TransferBDD tbdd = new TransferBDD(configAPs);
        Verifier verifier = new Verifier(tbdd,configs);
        _targets.entrySet().stream().map(e -> buildInvariant(verifier,true,e))
                .forEach(e -> verifier.addProperty(e.getKey(),e.getValue()));
        _assumptions.forEach(verifier::addAnchor);
        return null;
    }
}
