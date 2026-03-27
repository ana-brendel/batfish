package org.batfish.minesweeper.question.liveness;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import org.apache.commons.lang3.tuple.Pair;
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
  private static final PrefixRange DEFAULT_PREFIX = PrefixRange.fromString("10.0.0.0/8");

  private static final String PROP_PREFIX = "prefix";
  private static final String PROP_PROPERTY = "target";
  private static final String PROP_LOCATION = "location";
  private static final String PROP_ASSUMPTION_LOCATIONS = "assumption_locations";
  private static final String PROP_ASSUMPTIONS = "assumptions";
  private static final String PROP_DEFAULT_ASSUMPTION = "default_assumption";
  private static final String PROP_INGRESS = "ingress";

  private final @Nonnull PrefixSpace _prefix;
  private final @Nonnull Map<Location.Builder, Invariant.Builder> _target = new HashMap<>();
  private final Location.Builders _assumption_locations;
  private final Invariant.Builders _assumptions;
  private final Invariant.Builder _default_assumption;
  private final Location.Builders _ingress;

  public LivenessQuestion() {
    this(DEFAULT_PREFIX, null, null, null, null, null, null);
  }

  private LivenessQuestion(
      @Nullable PrefixRange prefix,
      @Nullable Invariant.Builder target,
      @Nullable Location.Builder location,
      @Nullable Location.Builders assumptions_locations,
      @Nullable Invariant.Builders assumptions,
      @Nullable Invariant.Builder default_assumption,
      @Nullable Location.Builders ingress) {
    if (target != null && location != null) {
      _target.put(location, target);
    }
    _prefix = prefix == null ? new PrefixSpace() : new PrefixSpace(prefix);
    _assumption_locations = assumptions_locations;
    _assumptions = assumptions;
    _default_assumption = default_assumption;
    _ingress = ingress;
  }

  @JsonCreator
  private static LivenessQuestion jsonCreator(
      @JsonProperty(PROP_PREFIX) PrefixRange prefix,
      @JsonProperty(PROP_PROPERTY) Invariant.Builder target,
      @JsonProperty(PROP_LOCATION) Location.Builder location,
      @JsonProperty(PROP_ASSUMPTION_LOCATIONS) @Nullable Location.Builders assumption_locations,
      @JsonProperty(PROP_ASSUMPTIONS) @Nullable Invariant.Builders assumptions,
      @JsonProperty(PROP_DEFAULT_ASSUMPTION) Invariant.Builder default_assumption,
      @JsonProperty(PROP_INGRESS) Location.Builders ingress) {
    return new LivenessQuestion(
        prefix, target, location, assumption_locations, assumptions, default_assumption, ingress);
  }

  @Nonnull
  public PrefixSpace get_prefix() {
    return _prefix;
  }

  @Nullable
  public Pair<Location.Builder, Invariant.Builder> get_target() {
    return _target.entrySet().stream()
        .findFirst()
        .map(e -> Pair.of(e.getKey(), e.getValue()))
        .orElse(null);
  }

  @Nonnull
  public Optional<Location.Builders> get_assumption_locations() {
    return _assumption_locations == null ? Optional.empty() : Optional.of(_assumption_locations);
  }

  @Nonnull
  public Optional<Invariant.Builders> get_assumptions() {
    return _assumptions == null ? Optional.empty() : Optional.of(_assumptions);
  }

  @Nullable
  public Invariant.Builder get_default_assumption() {
    return _default_assumption;
  }

  @Nullable
  public Location.Builders get_ingress() {
    return _ingress;
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
