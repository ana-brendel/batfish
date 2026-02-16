package org.batfish.minesweeper.question.verificationutilities;

import static org.apache.commons.lang3.ObjectUtils.firstNonNull;
import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;
import static org.batfish.minesweeper.bdd.TransferBDDUtils.makeRoutePairing;
import static org.batfish.minesweeper.question.searchroutepolicies.SearchRoutePoliciesAnswerer.routeConstraintsToBDD;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.LineAction;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchExpr;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.CommunityMatchExprToBDD;
import org.batfish.minesweeper.bdd.CommunitySetMatchExprToBDD;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferBDDUtils;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.searchroutepolicies.BgpRouteConstraints;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;

public class Invariant {
  private final TransferBDD tbdd;
  private final BDD bdd; // the bdd stored here is not assumed to be well-formed
  public final String str;

  /**
   * Provided BDD is not assumed to represent a well-formed BDDRoute
   *
   * @param tbdd the TransferBDD to be used
   * @param bdd BDD to be represented by invariant
   */
  public Invariant(TransferBDD tbdd, BDD bdd) {
    this(tbdd, bdd, null);
  }

  /**
   * Default invariant is true
   *
   * @param tbdd the TransferBDD to be used
   */
  public Invariant(TransferBDD tbdd) {
    this(tbdd, tbdd.getFactory().one());
  }

  public Invariant(TransferBDD tbdd, BDD bdd, String str) {
    this.tbdd = tbdd;
    this.bdd = bdd;
    this.str = str == null || str.isEmpty() ? null : str;
  }

  public static Invariant getFalse(TransferBDD tbdd) {
    return new Invariant(tbdd, tbdd.getFactory().zero());
  }

  public Invariant negate() {
    return new Invariant(tbdd, bdd.not());
  }

  @Override
  public String toString() {
    return this.toString(false);
  }

  public String toString(boolean refinementOccurred) {
    if (this.isFalse()) {
      return refinementOccurred ? "no traffic" : "false";
    } else if (this.isTrue()) {
      return "true";
    } else {
      String returned =
          Objects.requireNonNullElseGet(this.str, () -> BDDString.get(this.tbdd, this.bdd));
      assert !returned.trim().isEmpty();
      return returned;
    }
  }

  public String toString(boolean refinementOccurred, @Nonnull Map<BDD, String> cache) {
    if (cache.containsKey(this.bdd)) {
      return cache.get(this.bdd);
    } else {
      String result = this.toString(refinementOccurred);
      cache.put(this.bdd, result);
      return result;
    }
  }

  /**
   * Creates an invariant type from a BgpRouteConstraint (constants used for routeConstraintsToBDD
   * expect that this invariant will be used to start the weakest precondition based inference)
   *
   * @param tbdd the TransferBDD to be used
   * @param constraint constraint to be reflected by invariant
   * @param direction IN for invariant on node, OUT for invariant on edge (inherited from
   *     routeConstraintsToBDD)
   * @param context context used (inherited from routeConstraintsToBDD)
   * @return invariant representative of constraint
   */
  // TODO check if this makes sense
  public static Invariant ofBgpRouteConstraints(
      TransferBDD tbdd,
      BgpRouteConstraints constraint,
      Environment.Direction direction,
      TransferBDD.Context context) {
    BDDRoute base = new BDDRoute(tbdd.getFactory(), tbdd.getConfigAtomicPredicates());
    // outputRoute fixed to true because if an invariant is created this way, we will be using it as
    // a post constraint
    return new Invariant(
        tbdd, routeConstraintsToBDD(constraint, base.deepCopy(), true, tbdd, context, direction));
  }

  public static final class Builder {
    private final String str;
    private final List<ClauseBuilder> clauses = new ArrayList<>();

    private Builder() {
      this.str = null;
    }

    private Builder(String str) {
      this.str = str;
    }

    public Builder addClause(ClauseBuilder clause) {
      clauses.add(clause);
      return this;
    }

    public List<ClauseBuilder> getClauses() {
      return clauses;
    }

    public Invariant build(TransferBDD tbdd) {
      return this.build(tbdd, null);
    }

    public Invariant build(TransferBDD tbdd, RoutingPolicy policy) {
      if (clauses.isEmpty()) {
        return new Invariant(tbdd);
      } else {
        Collection<BDD> BDDs =
            clauses.stream().map(clause -> clause.build(tbdd, policy)).collect(Collectors.toSet());
        if (this.str == null) {
          return new Invariant(tbdd, tbdd.getFactory().orAll(BDDs));
        } else {
          return new Invariant(tbdd, tbdd.getFactory().orAll(BDDs), this.str);
        }
      }
    }

    @JsonCreator
    @VisibleForTesting
    static Builder forValue(@Nonnull String value) {
      Builder builder = new Builder(value);
      if (value.equals("[]")) {
        return builder;
      }
      String[] splits = value.trim().split("]");
      for (String clause : splits) {
        String trimmed = clause.trim();
        if (!trimmed.startsWith("[") && !trimmed.isEmpty()) {
          throw new BatfishException(
              "String parsing into property (Invariant.Builder) failed. "
                  + "A property should be in DNF form - [clause1][clause2]...[clause_n]. "
                  + "The trimmed clause is: "
                  + trimmed);
        } else if (!trimmed.isEmpty()) {
          builder.addClause(ClauseBuilder.parseForClauseBuilder(trimmed.substring(1)));
        }
      }
      return builder;
    }
  }

  /// Added to help parse a string corresponding to a list of invariants (for pybatfish)
  public static class Builders {
    private final String PROP_INVARIANTS = "invariants";
    public final @Nonnull List<Builder> _builders;

    @JsonCreator
    public Builders(@JsonProperty(PROP_INVARIANTS) @Nullable java.util.List<Builder> builders) {
      _builders = builders == null ? List.of() : builders;
    }

    @JsonCreator
    @VisibleForTesting
    static Builders forValue(String value) {
      String[] splits = value.trim().split(",");
      ImmutableList.Builder<Builder> builders = ImmutableList.builder();
      for (String invariant : splits) {
        builders.add(Builder.forValue(invariant.trim()));
      }
      return new Builders(builders.build());
    }

    @Nonnull
    public List<Builder> get_builders() {
      return _builders;
    }
  }

  public static final class ClauseBuilder {
    private PrefixSpace _positivePrefix;
    private PrefixSpace _negativePrefix;
    private RegexConstraints _communities;

    private ClauseBuilder() {}

    public ClauseBuilder matchPrefix(PrefixSpace prefix) {
      if (!prefix.isEmpty()) {
        if (_positivePrefix == null) {
          _positivePrefix = prefix;
        } else {
          _positivePrefix = _positivePrefix.intersection(prefix);
        }
      }
      return this;
    }

    public ClauseBuilder avoidPrefix(PrefixSpace prefix) {
      if (!prefix.isEmpty()) {
        if (_negativePrefix == null) {
          _negativePrefix = prefix;
        } else {
          _negativePrefix.addSpace(prefix);
        }
      }
      return this;
    }

    public ClauseBuilder setCommunities(RegexConstraints communities) {
      _communities = communities;
      return this;
    }

    private static BDD communityBDD(
        RegexConstraint regex, TransferBDD tbdd, BDDRoute route, TransferBDD.Context context) {
      return switch (regex.getRegexType()) {
        case REGEX -> {
          Map<String, Set<Integer>> stringKeys = new HashMap<>();
          tbdd.getConfigAtomicPredicates()
              .getStandardCommunityAtomicPredicates()
              .getRegexAtomicPredicates()
              .forEach((key, value) -> stringKeys.put(key.getRegex(), value));
          Set<Integer> cvi = stringKeys.get(regex.getRegex());
          if (cvi == null) {
            // The comparison on the CV directly doesn't seem to work, so I matched with the regex
            throw new BatfishException("Null variable list for regex " + regex.getRegex());
          }
          Collection<BDD> bdds =
              cvi.stream()
                  .map(i -> route.getCommunityAtomicPredicates()[i])
                  .collect(ImmutableSet.toImmutableSet());
          yield tbdd.getFactory().orAll(bdds);
        }
        case STRUCTURE_NAME -> {
          if (context == null) {
            throw new BatfishException("-- require context (from policy) to get community BDD");
          }
          CommunityMatchExpr matcher =
              context.config().getCommunityMatchExprs().get(regex.getRegex());
          yield matcher.accept(
              new CommunityMatchExprToBDD(),
              new CommunitySetMatchExprToBDD.Arg(tbdd, route, context));
        }
      };
    }

    private static BDD communitiesToBDD(
        RegexConstraints communities,
        TransferBDD tbdd,
        BDDRoute route,
        TransferBDD.Context context) {
      // assumes that all constraints should be true at the same time
      BDDFactory factory = tbdd.getFactory();
      BDD positiveBDD =
          communities.getPositiveRegexConstraints().isEmpty()
              ? factory.one()
              : factory.andAll(
                  communities.getPositiveRegexConstraints().stream()
                      .map(r -> communityBDD(r, tbdd, route, context))
                      .collect(ImmutableSet.toImmutableSet()));
      if (communities.getNegativeRegexConstraints().isEmpty()) {
        return positiveBDD;
      } else {
        BDD negativeBDD =
            factory.orAll(
                communities.getNegativeRegexConstraints().stream()
                    .map(r -> communityBDD(r, tbdd, route, context))
                    .collect(ImmutableSet.toImmutableSet()));
        return positiveBDD.diffWith(negativeBDD);
      }
    }

    private static BDD prefixSpaceToBDD(PrefixSpace space, BDDRoute r, boolean positive) {
      BDDFactory factory = r.getPrefix().getFactory();
      if (space.isEmpty()) {
        return factory.one();
      } else {
        BDD result = factory.zero();
        for (PrefixRange range : space.getPrefixRanges()) {
          BDD rangeBDD = isRelevantForDestination(r, range);
          result = result.or(rangeBDD);
        }
        if (!positive) {
          result = result.not();
        }
        return result;
      }
    }

    public BDD build(TransferBDD tbdd, RoutingPolicy policy) {
      BDDRoute base = new BDDRoute(tbdd.getFactory(), tbdd.getConfigAtomicPredicates());
      TransferBDD.Context context = policy == null ? null : TransferBDD.Context.forPolicy(policy);
      BDD clauseBDD = tbdd.getFactory().one();
      if (_positivePrefix != null && !_positivePrefix.isEmpty()) {
        clauseBDD.andWith(prefixSpaceToBDD(_positivePrefix, base, true));
      }
      if (_negativePrefix != null && !_negativePrefix.isEmpty()) {
        clauseBDD.andWith(prefixSpaceToBDD(_negativePrefix, base, false));
      }
      if (_communities != null && !_communities.isEmpty()) {
        clauseBDD.andWith(communitiesToBDD(_communities, tbdd, base, context));
      }
      return clauseBDD;
    }

    /// Added to help parse a string corresponding to a single clause
    private static Invariant.ClauseBuilder parseForClauseBuilder(String value) {
      if (value.trim().isEmpty()) {
        return createClause(null, null, null);
      }
      PrefixSpace positivePrefix = new PrefixSpace();
      PrefixSpace negativePrefix = new PrefixSpace();
      ImmutableList.Builder<RegexConstraint> communities = ImmutableList.builder();
      String[] atoms = value.trim().split("&");
      for (String atom : atoms) {
        String trimmed = atom.trim();
        if (!trimmed.isEmpty()) {
          String[] parts = trimmed.trim().split("=");
          if (parts.length == 2) {
            String category = parts[0].trim();
            String input = parts[1].trim();
            switch (category) {
              case "comm":
                communities.add(RegexConstraint.parse(input));
                break;
              case "prefix":
                boolean positive = true;
                if (input.startsWith("!")) {
                  input = input.substring(1);
                  positive = false;
                }
                // Optional<Prefix> prefix = Prefix.tryParse(input);
                Optional<PrefixSpace> prefix = Optional.empty();
                try {
                  prefix = Optional.of(new PrefixSpace(PrefixRange.fromString(input)));
                } catch (Exception ignore) {
                }
                if (prefix.isEmpty()) {
                  throw new BatfishException(
                      "Provided prefix (" + input + ") is not a valid prefix");
                } else if (!positive) {
                  negativePrefix.addSpace(prefix.get());
                } else {
                  if (positivePrefix.isEmpty()) {
                    positivePrefix.addSpace(prefix.get());
                  } else {
                    positivePrefix.intersection(prefix.get());
                  }
                }
                break;
              default:
                throw new BatfishException(
                    "Error when parsing string for clause -"
                        + " check ["
                        + category
                        + "] which does not match a supported feature (comm or prefix) with ! "
                        + "implying the following value is negated (The whole value provided is ["
                        + value
                        + "])");
            }
          } else {
            throw new BatfishException(
                "Error when parsing string for clause -"
                    + " each clause should have format [field1=value1,...,field_n=value_n]. "
                    + " Current field supported: comm, prefix."
                    + " Provided string: "
                    + trimmed.trim());
          }
        }
      }
      return createClause(
          positivePrefix, negativePrefix, new RegexConstraints(communities.build()));
    }

    public RegexConstraints getCommunities() {
      return _communities;
    }
  }

  public static Builder builder() {
    return new Builder();
  }

  public static ClauseBuilder clauseBuilder() {
    return new ClauseBuilder();
  }

  public static ClauseBuilder createClause(
      PrefixSpace pos, PrefixSpace neg, RegexConstraints comms) {
    return clauseBuilder()
        .matchPrefix(firstNonNull(pos, new PrefixSpace()))
        .avoidPrefix(firstNonNull(neg, new PrefixSpace()))
        .setCommunities(firstNonNull(comms, new RegexConstraints()));
  }

  /// Returns the BDD stored in this invariant (with well-formed constraint applied)
  public BDD getBDD() {
    return bdd;
  }

  /// Returns true if the invariant is false
  public boolean isFalse() {
    return this.getBDD().isZero();
  }

  /// Returns true if the invariant is true (for any well-formed route)
  public boolean isTrue() {
    return this.getBDD().isOne();
  }

  public Invariant copy() {
    return new Invariant(tbdd, bdd.id());
  }

  /**
   * Determines BDD corresponding to the input constraints that must hold in order for the invariant
   * condition to hold on output.
   *
   * @param tbdd transfer bdd used
   * @param inv invariant to hold on output route
   * @param r route holding the modifications and conditions after policy
   * @return bdd constraining input in order to satisfy invariant on output
   */
  public static BDD conditionsForConstraint(TransferBDD tbdd, BDD inv, @Nonnull BDDRoute r) {
    // TODO needs to be updated to include accurate reflect of the AS path (maybe other
    // characteristics)
    if (inv.isOne()) { // if the invariant is always true... should I do one for always false too?
      return tbdd.getFactory().one();
    } else {
      BDDPairing pairing = makeRoutePairing(r, tbdd);
      return inv.veccompose(pairing);
    }
  }

  /**
   * Synthesizes the weakest precondition for this invariant to hold after the provided policy is
   * executed. If the includeDenied flag is false, then only preconditions which result in routes
   * that are permitted is considered.
   *
   * @param policy weakest precondition for this policy
   * @param includeDenied true if denied routes should be included
   * @return weakest precondition for this invariant to hold on policy
   */
  public Invariant weakestPrecondition(@Nonnull RoutingPolicy policy, boolean includeDenied) {
    if (policy.getStatements().isEmpty()) {
      if (policy.getOwner() == null
          || policy.getOwner().getDefaultInboundAction() == LineAction.PERMIT) {
        return this.copy(); // default is permit, so invariant itself is the weakest precondition
      } else {
        return new Invariant(tbdd); // default is deny so the weakest precondition is true
      }
    } else {
      TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
      List<TransferReturn> paths;
      try {
        paths = tbdd.computePaths(policy.getStatements(), context, true);
      } catch (Exception e) {
        String name =
            policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
        throw new BatfishException(
            "Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
      }
      BDD acceptedWP =
          TransferBDDUtils.weakestPrecondition(
              paths,
              this.getBDD(),
              tbdd,
              (post, path) -> conditionsForConstraint(tbdd, post, path.getOutputRoute()));

      return new Invariant(
          tbdd,
          includeDenied
              ? acceptedWP.orWith(TransferBDDUtils.deniedRoutes(paths, tbdd))
              : acceptedWP);
    }
  }

  /**
   * Synthesizes the weakest precondition for this invariant to hold after the provided policy is
   * executed. Note, this method does not guarantee that there exists a route that satisfies the
   * invariant, just that any route which is permitted will satisfy the invariant.
   *
   * @param policy weakest precondition for this policy
   * @return weakest precondition for this invariant to hold on policy
   */
  public Invariant weakestPrecondition(@Nonnull RoutingPolicy policy) {
    return this.weakestPrecondition(policy, true);
  }

  /**
   * Finds a strong common implicant for provided invariants via conjoining the invariants.
   *
   * @param left first condition
   * @param right second condition
   * @return common and strong (non-false if possible) implicant for both conditions
   */
  public static Invariant strongestCommonImplicant(Invariant left, Invariant right) {
    assert left.tbdd.equals(right.tbdd);
    return new Invariant(left.tbdd, left.bdd.and(right.bdd));
  }

  /**
   * Indicates if this invariant implies the provided invariant
   *
   * @param post postcondition for implication
   * @return true if implies provided invariant
   */
  public boolean implies(Invariant post) {
    return (!this.getBDD().diffSat(post.getBDD()));
  }

  /**
   * Indicates if this invariant is implied by provided invariant
   *
   * @param pre precondition for implication
   * @return true if implied by provided invariant
   */
  public boolean impliedBy(Invariant pre) {
    return pre.implies(this);
  }

  /**
   * Synthesizes the strongest postcondition which will hold after any route satisfying this
   * invariant is passed through the provided policy. If no routes satisfying this invariant are
   * permitted passed this policy, then the postcondition returned is false.
   *
   * @param policy gets the strongest postcondition for this policy
   * @return invariant corresponding to the strongest postcondition
   */
  public Invariant strongestPostcondition(@Nonnull RoutingPolicy policy) {
    if (policy.getStatements().isEmpty()) {
      if (policy.getOwner() == null
          || policy.getOwner().getDefaultInboundAction() == LineAction.PERMIT) {
        return this.copy(); // default is permit, so invariant itself is the strongest postcondition
      } else {
        return Invariant.getFalse(tbdd); // default is deny so the strongest postcondition is false
      }
    } else {
      TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
      List<TransferReturn> paths;
      try {
        paths = tbdd.computePaths(policy.getStatements(), context, true);
      } catch (Exception e) {
        String name =
            policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
        throw new BatfishException(
            "Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
      }
      BDD strongest =
          TransferBDDUtils.strongestPostcondition(paths, this.getBDD(), tbdd, Function.identity());
      return new Invariant(tbdd, strongest);
    }
  }

  @Override
  public boolean equals(Object obj) {
    if (obj != null && obj.getClass() == this.getClass()) {
      return this.getBDD().equals(((Invariant) obj).getBDD());
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return Objects.hash(tbdd, bdd);
  }

  /**
   * Intended for testing, checks if the provided precondition ensures this invariant holds on the
   * result of the policy being applied.
   *
   * @param pre precondition for incoming routes
   * @param policy policy to be executed
   * @return true if this invariant holds as postcondition
   */
  @VisibleForTesting
  boolean validPrecondition(@Nonnull Invariant pre, @Nonnull RoutingPolicy policy) {
    TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
    List<TransferReturn> paths;
    try {
      paths = tbdd.computePaths(policy.getStatements(), context, true);
    } catch (Exception e) {
      String name =
          policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
      throw new BatfishException(
          "Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
    }
    if (!paths.stream().filter(TransferReturn::getAccepted).toList().isEmpty()) {
      for (TransferReturn path : paths) {
        BDD pathAnnouncements = path.getInputConstraints();
        if (path.getAccepted()) { // path is permitted, need to check if precondition is sat, so are
          // output
          BDDRoute route = path.getOutputRoute();
          BDD constraintsMatchingOutput = conditionsForConstraint(tbdd, this.getBDD(), route);
          BDD constrainedInput = pathAnnouncements.and(pre.getBDD());
          BDD intersection = constrainedInput.and(constraintsMatchingOutput);
          BDD diff = constrainedInput.diff(intersection); // this should be empty
          if (!diff.isZero()) {
            return false;
          }
        } // path is denied, so it cannot violate any post-condition
      }
    }
    return true; // if there are no accepted paths, any condition is valid precondition
  }
}
