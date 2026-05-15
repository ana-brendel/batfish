package org.batfish.minesweeper.question.isolation;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import org.batfish.datamodel.questions.Question;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkArgument;

@ParametersAreNonnullByDefault
public final class IsolationQuestion extends Question {
  private static final String PROP_PROPERTIES = "target";
  private static final String PROP_LOCATIONS = "location";
  private static final String PROP_ASSUMPTION_LOCATIONS = "assumption_locations";
  private static final String PROP_ASSUMPTIONS = "assumptions";
  private static final String PROP_DEFAULT_ASSUMPTION = "default_assumption";
  private static final String PROP_ISOLATE_VIOLATIONS = "isolate_violations";
  private static final String PROP_COMPUTE_DATA_PLANE = "compute_data_plane";
  private static final String PROP_EXACT_COMM = "exact_communities";

  //  private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets = new HashMap<>();
  private final Location.Builders _location;
  private final Invariant.Builders _target;
  private final Location.Builders _assumption_locations;
  private final Invariant.Builders _assumptions;
  private final Invariant.Builder _default_assumption;
  private final boolean _isolate_violations;
  private final boolean _compute_data_plane;
  private final boolean _exact_communities;

  public IsolationQuestion() {
    this(null, null, null, null, null, false, false, false);
  }

  public IsolationQuestion(
      @Nullable Invariant.Builders target,
      @Nullable Location.Builders location,
      @Nullable Location.Builders assumptions_locations,
      @Nullable Invariant.Builders assumptions,
      @Nullable Invariant.Builder default_assumption,
      boolean isolate_violations,
      boolean compute_data_plane,
      boolean exact_communities) {
    checkArgument(
        location == null
            ? target == null
            : target != null && (location.get_builders().size() == target.get_builders().size()),
        "Must have the same number of targets and locations");
    _target = target;
    _location = location;

    checkArgument(
        assumptions_locations == null
            ? assumptions == null
            : assumptions != null
                && (assumptions_locations.get_builders().size()
                    == assumptions.get_builders().size()),
        "Must have the same number of assumptions and assumption locations");

    _assumption_locations = assumptions_locations;
    _assumptions = assumptions;

    _default_assumption = default_assumption;
    _isolate_violations = isolate_violations;
    _compute_data_plane = compute_data_plane;
    _exact_communities = exact_communities;
  }

  @JsonCreator
  private static IsolationQuestion jsonCreator(
      @JsonProperty(PROP_PROPERTIES) Invariant.Builders target,
      @JsonProperty(PROP_LOCATIONS) Location.Builders location,
      @JsonProperty(PROP_ASSUMPTION_LOCATIONS) @Nullable Location.Builders assumption_locations,
      @JsonProperty(PROP_ASSUMPTIONS) @Nullable Invariant.Builders assumptions,
      @JsonProperty(PROP_DEFAULT_ASSUMPTION) @Nullable Invariant.Builder default_assumption,
      @JsonProperty(PROP_EXACT_COMM) @Nullable Boolean exact_communities,
      @JsonProperty(PROP_ISOLATE_VIOLATIONS) @Nullable Boolean isolate_violations,
      @JsonProperty(PROP_COMPUTE_DATA_PLANE) @Nullable Boolean compute_data_plane) {
    // default for show_all and refine is false (to run faster in default case)
    return new IsolationQuestion(
        target,
        location,
        assumption_locations,
        assumptions,
        default_assumption,
        isolate_violations != null && isolate_violations,
        compute_data_plane != null && compute_data_plane,
        exact_communities != null && exact_communities);
  }

  @Nonnull
  public Optional<Location.Builders> get_location() {
    return _location == null ? Optional.empty() : Optional.of(_location);
  }

  @Nonnull
  public Optional<Invariant.Builders> get_target() {
    return _target == null ? Optional.empty() : Optional.of(_target);
  }

  public boolean get_isolate_violations() {
    return _isolate_violations;
  }

  public boolean get_compute_data_plane() {
    return _compute_data_plane;
  }

  public boolean get_exact_communities() {
    return _exact_communities;
  }

  @Nonnull
  public Optional<Location.Builders> get_assumption_locations() {
    return _assumption_locations == null ? Optional.empty() : Optional.of(_assumption_locations);
  }

  @Nonnull
  public Optional<Invariant.Builders> get_assumptions() {
    return _assumptions == null ? Optional.empty() : Optional.of(_assumptions);
  }

  @Nonnull
  public Optional<Invariant.Builder> get_default_assumption() {
    return _default_assumption == null ? Optional.empty() : Optional.of(_default_assumption);
  }

  @JsonIgnore
  @Override
  public boolean getDataPlane() {
    return false;
  }

  @JsonIgnore
  @Override
  public String getName() {
    return "whirlpoolIsolation";
  }
}
