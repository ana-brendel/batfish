package org.batfish.minesweeper.question.liveness;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.batfish.minesweeper.question.verificationutilities.Setup.buildInvariant;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;

public class LivenessAnswerer extends Answerer {
    private static final Logger LOGGER = LogManager.getLogger(LivenessAnswerer.class);

    private final @Nonnull PrefixSpace _prefix;
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets;
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions;
    private final @Nonnull Set<RegexConstraint> _communityRegexes;
    private final @Nonnull Set<RegexConstraint> _asPathRegexes;
    private final boolean _showAll;

    public LivenessAnswerer(LivenessQuestion question, IBatfish batfish) {
        super(question, batfish);
        _showAll = question.get_show_all();
        _prefix = question.get_prefix();
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

    public record Result(Optional<Path> goodPath, Optional<Map<Location, Bgpv4Route>> potentialInterferences) {}

    /**
     * Completes liveness verification of the target property for the provided prefix at the given location, based
     * on the network described by the info object provided.
     * @param info network information
     * @param prefix prefix considered for liveness property
     * @param location location liveness property should hold
     * @param target target liveness property to verify
     * @return LivenessAnswerer.Result object storing corresponding verification result
     */
    public static Result run(NetworkInfo info, PrefixSpace prefix, Location location, Invariant target) {
        PathAnalyzer analyzer = info.toPathAnalyzer(prefix,location,target);
        InterferenceCheck interferenceCheck = info.toInterferenceCheck(prefix,location,target);

        Optional<Path> goodPath = analyzer.run();

        return goodPath.isPresent() ?
                new Result(goodPath,interferenceCheck.run()) : new Result(goodPath, Optional.empty());
    }

    @Override
    public AnswerElement answer(NetworkSnapshot snapshot) {
        // Gathering and formatting information from snapshot
        SpecifierContext context = _batfish.specifierContext(snapshot);
        Map<String, Configuration> configs = context.getConfigs();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(_communityRegexes,_asPathRegexes,configs.values());
        TransferBDD tbdd = new TransferBDD(configAPs);
        NetworkInfo info = new NetworkInfo(tbdd,configs);
        _assumptions.forEach(info::addAssumption);

        if (_targets.entrySet().stream().findFirst().isEmpty())
            throw new BatfishException("LivenessAnswerer.answer() - No target property provided.");
        Map.Entry<Location, Invariant> target = buildInvariant(info,true,_targets.entrySet().stream().findFirst().get());

        Result result = run(info,_prefix,target.getKey(),target.getValue());

        return null;
    }
}
