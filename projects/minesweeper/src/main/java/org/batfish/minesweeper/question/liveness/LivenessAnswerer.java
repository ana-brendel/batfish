package org.batfish.minesweeper.question.liveness;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.minesweeper.question.safety.SafetyAnswerer;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class LivenessAnswerer extends Answerer {
    private static final Logger LOGGER = LogManager.getLogger(LivenessAnswerer.class);

    private final @Nonnull PrefixSpace _prefix;
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets;
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions;
    private final @Nonnull Set<RegexConstraint> _communityRegexes;
    private final @Nonnull Set<RegexConstraint> _asPathRegexes;
    private final boolean _readable;

    public LivenessAnswerer(LivenessQuestion question, IBatfish batfish) {
        super(question, batfish);
        _readable = question.get_readable();
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
    @Override
    public AnswerElement answer(NetworkSnapshot snapshot) {
        return null;
    }
}
