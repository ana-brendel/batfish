package org.batfish.minesweeper.question.verify;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import org.batfish.datamodel.questions.Question;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.HashMap;
import java.util.Map;

@ParametersAreNonnullByDefault
public final class VerifierQuestion extends Question {
    private static final String PROP_PROPERTY = "target";
    private static final String PROP_LOCATION = "location";
    private static final String PROP_ASSUMPTION_LOCATIONS = "assumption_locations";
    private static final String PROP_ASSUMPTIONS = "assumptions";
    private static final String PROP_READABLE = "readable";

    private final @Nonnull Map<Location.Builder,  Invariant.Builder> _targets = new HashMap<>();
    private final Location.Builders _assumption_locations;
    private final Invariant.Builders _assumptions;
    private final boolean _readable;

   public VerifierQuestion() { this(null,null,null,null,false); }

    private VerifierQuestion(
            @Nullable Invariant.Builder target,
            @Nullable Location.Builder location,
            @Nullable Location.Builders assumptions_locations,
            @Nullable Invariant.Builders assumptions,
            boolean readable) {
        if (target != null && location != null) {
            _targets.put(location,target);
        }
        _assumption_locations = assumptions_locations;
        _assumptions = assumptions;
        _readable = readable;
    }

    @JsonCreator
    private static VerifierQuestion jsonCreator(
            @JsonProperty(PROP_PROPERTY) Invariant.Builder target,
            @JsonProperty(PROP_LOCATION) Location.Builder location,
            @JsonProperty(PROP_ASSUMPTION_LOCATIONS) @Nullable Location.Builders assumption_locations,
            @JsonProperty(PROP_ASSUMPTIONS) @Nullable Invariant.Builders assumptions,
            @JsonProperty(PROP_READABLE) @Nullable Boolean readable
    ) {
       // default for display is false (as it is not efficient)
       return new VerifierQuestion(target,location,assumption_locations,assumptions, readable != null && readable);
    }

    @Nonnull
    public Map<Location.Builder, Invariant.Builder> get_targets() { return _targets; }
    public Location.Builders get_assumption_locations() { return _assumption_locations; }
    public Invariant.Builders get_assumptions() { return _assumptions; }
    public boolean get_readable() { return _readable; }

    @JsonIgnore
    @Override
    public boolean getDataPlane() {
        return false;
    }

    @JsonIgnore
    @Override
    public String getName() {
        return "verify";
    }
}
