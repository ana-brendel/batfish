package org.batfish.minesweeper.question.verify;

import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.questions.Question;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class VerifierQuestion extends Question {
    private final @Nonnull Map<Location, Invariant.Builder> _targets = new HashMap<>();
    private final @Nonnull Set<Location> _assumptions = new HashSet<>();
    private final Set<Map.Entry<Configuration,RegexConstraint>> _communityRegexes = new HashSet<>();
    private final Set<Map.Entry<Configuration,RegexConstraint>> _asPathRegexes = new HashSet<>();

    public Map<Location, Invariant.Builder> getTargets() { return _targets; }

    public Set<Location> getAssumptions() { return _assumptions; }

    public Set<Map.Entry<Configuration,RegexConstraint>> getCommunityRegexes() { return _communityRegexes; }

    public Set<Map.Entry<Configuration,RegexConstraint>> getAsPathRegexes() { return _asPathRegexes; }

    @Override
    public boolean getDataPlane() {
        return false;
    }

    @Override
    public String getName() {
        return "";
    }
}
