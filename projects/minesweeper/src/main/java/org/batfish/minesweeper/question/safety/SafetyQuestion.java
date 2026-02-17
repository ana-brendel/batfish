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

import static com.google.common.base.Preconditions.checkArgument;

@ParametersAreNonnullByDefault
public final class SafetyQuestion extends Question {
  private static final String PROP_PROPERTY = "target";
  private static final String PROP_LOCATION = "location";
  private static final String PROP_ASSUMPTION_LOCATIONS = "assumption_locations";
  private static final String PROP_ASSUMPTIONS = "assumptions";
  private static final String PROP_SHOW_ALL = "show_all";
  private static final String PROP_REFINE = "refine";

  private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets = new HashMap<>();
  private final Location.Builders _assumption_locations;
  private final Invariant.Builders _assumptions;
  private final boolean _show_all;
  private final boolean _refine;

  public SafetyQuestion() {
    this(null, null, null, null, false, false);
  }

  private SafetyQuestion(
      @Nullable Invariant.Builder target,
      @Nullable Location.Builder location,
      @Nullable Location.Builders assumptions_locations,
      @Nullable Invariant.Builders assumptions,
      boolean show_all,
      boolean refine) {
    if (target != null && location != null) {
      _targets.put(location, target);
    }

    checkArgument(
        assumptions_locations == null
            ? assumptions == null
            : assumptions != null
                && (assumptions_locations.get_builders().size()
                    == assumptions.get_builders().size()),
        "Must have the same number of assumptions and assumption locations");

    _assumption_locations = assumptions_locations;
    _assumptions = assumptions;

    _show_all = show_all;
    _refine = refine;
  }

  @JsonCreator
  private static SafetyQuestion jsonCreator(
      @JsonProperty(PROP_PROPERTY) Invariant.Builder target,
      @JsonProperty(PROP_LOCATION) Location.Builder location,
      @JsonProperty(PROP_ASSUMPTION_LOCATIONS) @Nullable Location.Builders assumption_locations,
      @JsonProperty(PROP_ASSUMPTIONS) @Nullable Invariant.Builders assumptions,
      @JsonProperty(PROP_SHOW_ALL) @Nullable Boolean show_all,
      @JsonProperty(PROP_REFINE) @Nullable Boolean refine) {
    // default for show_all and refine is false (to run faster in default case)
    return new SafetyQuestion(
        target,
        location,
        assumption_locations,
        assumptions,
        show_all != null && show_all,
        refine != null && refine);
  }

  @Nonnull
  public Map<Location.Builder, Invariant.Builder> get_targets() {
    return _targets;
  }

  public boolean get_show_all() {
    return _show_all;
  }

  public boolean get_refine() {
    return _refine;
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
    return "safety";
  }
}
