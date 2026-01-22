package org.batfish.minesweeper.question.safety;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import org.batfish.datamodel.questions.Question;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

@ParametersAreNonnullByDefault
public final class SafetyQuestion extends Question {
    private static final String PROP_PROPERTY = "target";
    private static final String PROP_LOCATION = "location";
    private static final String PROP_ASSUMPTION_LOCATIONS = "assumption_locations";
    private static final String PROP_ASSUMPTIONS = "assumptions";
    private static final String PROP_READABLE = "readable";

    private final @Nonnull Map<Location.Builder,  Invariant.Builder> _targets = new HashMap<>();
    private final Location.Builders _assumption_locations;
    private final Invariant.Builders _assumptions;
    private final boolean _readable;

   public SafetyQuestion() { this(null,null,null,null,false); }

    private SafetyQuestion(
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
    private static SafetyQuestion jsonCreator(
            @JsonProperty(PROP_PROPERTY) Invariant.Builder target,
            @JsonProperty(PROP_LOCATION) Location.Builder location,
            @JsonProperty(PROP_ASSUMPTION_LOCATIONS) @Nullable Location.Builders assumption_locations,
            @JsonProperty(PROP_ASSUMPTIONS) @Nullable Invariant.Builders assumptions,
            @JsonProperty(PROP_READABLE) @Nullable Boolean readable
    ) {
       // default for display is false (as it is not efficient)
       return new SafetyQuestion(target,location,assumption_locations,assumptions, readable != null && readable);
    }

    @Nonnull
    public Map<Location.Builder, Invariant.Builder> get_targets() { return _targets; }
    public boolean get_readable() { return _readable; }

    public Optional<Location.Builders> get_assumption_locations() {
        return _assumption_locations == null ? Optional.empty() : Optional.of(_assumption_locations);
    }
    public Optional<Invariant.Builders> get_assumptions() {
       return _assumptions == null ? Optional.empty() : Optional.of(_assumptions);
   }

    @JsonIgnore
    @Override
    public boolean getDataPlane() {
        return false;
    }

    @JsonIgnore
    @Override
    public String getName() {
        return "safety";
    }
}
