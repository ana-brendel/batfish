package org.batfish.minesweeper.question.liveness;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
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
public final class LivenessQuestion extends Question {
  private static final PrefixSpace DEFAULT_PREFIX =
      new PrefixSpace(PrefixRange.fromString("10.0.0.0/8"));

  private static final String PROP_PREFIX = "prefix";
  private static final String PROP_PROPERTY = "target";
  private static final String PROP_LOCATION = "location";
  private static final String PROP_ASSUMPTION_LOCATIONS = "assumption_locations";
  private static final String PROP_ASSUMPTIONS = "assumptions";
  private static final String PROP_SHOW_ALL = "show_all";

  private final @Nonnull PrefixSpace _prefix;
  private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets = new HashMap<>();
  private final Location.Builders _assumption_locations;
  private final Invariant.Builders _assumptions;
  private final boolean _showAll;

  public LivenessQuestion() {
    this(DEFAULT_PREFIX, null, null, null, null, false);
  }

  private LivenessQuestion(
      PrefixSpace prefix,
      @Nullable Invariant.Builder target,
      @Nullable Location.Builder location,
      @Nullable Location.Builders assumptions_locations,
      @Nullable Invariant.Builders assumptions,
      boolean showAll) {
    if (target != null && location != null) {
      _targets.put(location, target);
    }
    _prefix = prefix;
    _assumption_locations = assumptions_locations;
    _assumptions = assumptions;
    _showAll = showAll;
  }

  @JsonCreator
  private static LivenessQuestion jsonCreator(
      @JsonProperty(PROP_PREFIX) PrefixSpace prefix,
      @JsonProperty(PROP_PROPERTY) Invariant.Builder target,
      @JsonProperty(PROP_LOCATION) Location.Builder location,
      @JsonProperty(PROP_ASSUMPTION_LOCATIONS) @Nullable Location.Builders assumption_locations,
      @JsonProperty(PROP_ASSUMPTIONS) @Nullable Invariant.Builders assumptions,
      @JsonProperty(PROP_SHOW_ALL) @Nullable Boolean showAll) {
    // default for display is false (as it is not efficient)
    return new LivenessQuestion(
        prefix, target, location, assumption_locations, assumptions, showAll != null && showAll);
  }

  @Nonnull
  public PrefixSpace get_prefix() {
    return _prefix;
  }

  @Nonnull
  public Map<Location.Builder, Invariant.Builder> get_targets() {
    return _targets;
  }

  public boolean get_show_all() {
    return _showAll;
  }

  @Nonnull
  public Optional<Location.Builders> get_assumption_locations() {
    return _assumption_locations == null ? Optional.empty() : Optional.of(_assumption_locations);
  }

  @Nonnull
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
    return "liveness";
  }
}
