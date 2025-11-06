package org.batfish.minesweeper.question.verify;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchExpr;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.CommunityMatchExprToBDD;
import org.batfish.minesweeper.bdd.CommunitySetMatchExprToBDD;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;

import javax.annotation.Nonnull;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import static org.apache.commons.lang3.ObjectUtils.firstNonNull;
import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;

public class Invariant {
    private final TransferBDD tbdd;
    private final BDD bdd;
    private final BDDRoute base;

    public Invariant(TransferBDD tbdd, BDD bdd) {
        this.tbdd = tbdd;
        this.bdd = bdd;
        this.base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
    }

    public Invariant(TransferBDD tbdd) {
        this.tbdd = tbdd;
        this.bdd = tbdd.getFactory().one();
        this.base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
    }

    public static Builder builder() {
        return new Builder();
    }

    public static ClauseBuilder clauseBuilder() {
        return new ClauseBuilder();
    }

    public static ClauseBuilder createClause(PrefixSpace pos, PrefixSpace neg, RegexConstraints comms) {
        return clauseBuilder()
                .matchPrefix(firstNonNull(pos,new PrefixSpace()))
                .avoidPrefix(firstNonNull(neg,new PrefixSpace()))
                .setCommunities(firstNonNull(comms,new RegexConstraints()));
    }

    public BDD getBDD() {
        return base.wellFormednessConstraints(true).and(bdd.id());
    }

    public boolean isFalse() {
        return base.wellFormednessConstraints(true).and(bdd).isZero();
    }

    public boolean isTrue() {
        return this.getBDD().equals(base.wellFormednessConstraints(true));
    }

    public Invariant copy() {
        return new Invariant(tbdd,bdd.id());
    }

    /**
     * Determines BDD corresponding to the input constraints that must hold in order for the invariant condition to hold on output.
     * @param tbdd transfer bdd used
     * @param inv invariant to hold on output route
     * @param isOutputRoute (not used yet) route after import or after export ?
     * @param r route holding the modifications and conditions after policy
     * @return bdd constraining input in order to satisfy invariant on output
     */
    public static BDD conditionsForConstraint(TransferBDD tbdd, BDD inv, boolean isOutputRoute, @Nonnull BDDRoute r) {
        if (inv.isOne()) { // if the invariant is always true... should I do one for always false too?
            return r.wellFormednessConstraints(true).and(tbdd.getFactory().one());
        } else {
            BDDPairing pairing = getVariableMapping(tbdd, r);
            BDD composed = inv.veccompose(pairing);
            return r.wellFormednessConstraints(true).and(composed);
        }
    }

    /**
     * Synthesizes the weakest precondition for this invariant to hold after the provided policy is executed. Note, this
     * method does not guarantee that there exists a route that satisfies the invariant, just that any route which is permitted
     * will satisfy the invariant.
     * @param policy weakest precondition for this policy
     * @return weakest precondition for this invariant to hold on policy
     */
    public Invariant weakestPrecondition(RoutingPolicy policy) {
        if (policy == null || policy.getStatements().isEmpty() || this.isTrue()) {
            return this.copy();
        }
        TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
        List<TransferReturn> paths;
        try {
            paths = tbdd.computePaths(policy.getStatements(),context,true);
        } catch (Exception e) {
            String name = policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
            throw new BatfishException("Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
        }
        if (paths.stream().filter(TransferReturn::getAccepted).toList().isEmpty()) {
            return new Invariant(tbdd); // no permitted paths means any input is safe
        } else {
            ImmutableList.Builder<BDD> builder = ImmutableList.builder();
            for (TransferReturn path : paths) {
                BDD pathAnnouncements = path.getInputConstraints();
                if (path.getAccepted()) { // path is permitted, only get the input conditions that satisfy invariant
                    BDDRoute route = path.getOutputRoute();
                    BDD constraintsMatchingOutput = conditionsForConstraint(tbdd,this.getBDD(),false,route);
                    BDD intersection = pathAnnouncements.and(constraintsMatchingOutput);
                    builder.add(intersection);
                } else { // path is produced denied route, so this condition is safe
                    // might want to think more about this, so we want to accept conditions that contradict post condition
                    BDDRoute wf_base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
                    builder.add(pathAnnouncements.and(wf_base.wellFormednessConstraints(true)));
                }
            }
            BDD disjunction = tbdd.getFactory().orAll(builder.build());
            return new Invariant(tbdd,disjunction);
        }
    }

    /**
     * Finds a strong common implicant for provided invariants via conjoining the invariants.
     * @param left first condition
     * @param right second condition
     * @return common and strong (non-false if possible) implicant for both conditions
     */
    public static Invariant strongestCommonImplicant(Invariant left, Invariant right) {
        assert left.tbdd.equals(right.tbdd);
        return new Invariant(left.tbdd, left.getBDD().and(right.getBDD()));
    }

    private static BDDPairing getVariableMapping(TransferBDD tbdd, BDDRoute route) {
        BDDRoute base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        BDDPairing pairs = tbdd.getFactory().makePair();
        // PREFIX CONSTRAINTS
        for (int i = 0; i < base.getPrefix().size(); i++) {
            BDD bdd_var = base.getPrefix().getBitBDD(i);
            BDD new_bdd = route.getPrefix().getBitBDD(i);
            assert bdd_var != null;
            pairs.set(bdd_var.var(),new_bdd);
        }
        // COMMUNITY CONSTRAINTS
        for (int i = 0; i < base.getCommunityAtomicPredicates().length; i++) {
            BDD bdd_var = base.getCommunityAtomicPredicates()[i];
            BDD new_bdd = route.getCommunityAtomicPredicates()[i];
            pairs.set(bdd_var.var(),new_bdd);
        }
        return pairs;
    }

    public static final class Builder {
        private final List<ClauseBuilder> clauses = new ArrayList<>();

        private Builder () {}

        public Builder addClause(ClauseBuilder clause) {
            clauses.add(clause);
            return this;
        }

        public Invariant build(TransferBDD tbdd) {
            return this.build(tbdd,null);
        }

        public Invariant build(TransferBDD tbdd, RoutingPolicy policy) {
            Collection<BDD> BDDs = clauses.stream().map(clause -> clause.build(tbdd,policy)).collect(Collectors.toSet());
            return new Invariant(tbdd,tbdd.getFactory().orAll(BDDs));
        }
    }

    public static final class ClauseBuilder {
        private PrefixSpace _positivePrefix;
        private PrefixSpace _negativePrefix;
        private RegexConstraints _communities;

        private ClauseBuilder() {}

        public ClauseBuilder matchPrefix(PrefixSpace prefix) {
            _positivePrefix = prefix;
            return this;
        }

        public ClauseBuilder avoidPrefix(PrefixSpace prefix) {
            _negativePrefix = prefix;
            return this;
        }

        public ClauseBuilder setCommunities(RegexConstraints communities) {
            _communities = communities;
            return this;
        }

        private static BDD communityBDD(RegexConstraint regex, TransferBDD tbdd, BDDRoute route, TransferBDD.Context context) {
            return switch (regex.getRegexType()) {
                case REGEX ->
                        tbdd.getFactory().orAll(tbdd.getConfigAtomicPredicates()
                                .getStandardCommunityAtomicPredicates()
                                .getRegexAtomicPredicates()
                                .get(CommunityVar.from(regex.getRegex()))
                                .stream().map(i -> route.getCommunityAtomicPredicates()[i])
                                .collect(ImmutableSet.toImmutableSet()));
                case STRUCTURE_NAME ->{
                    if (context == null) { throw new BatfishException("-- require context (from policy) to get community BDD"); }
                    CommunityMatchExpr matcher = context.config().getCommunityMatchExprs().get(regex.getRegex());
                    yield matcher.accept(new CommunityMatchExprToBDD(), new CommunitySetMatchExprToBDD.Arg(tbdd,route,context));
                }
            };
        }

        private static BDD communitiesToBDD(RegexConstraints communities, TransferBDD tbdd, BDDRoute route, TransferBDD.Context context) {
            // assumes that all constraints should be true at the same time
            BDDFactory factory = tbdd.getFactory();
            BDD positiveBDD = communities.getPositiveRegexConstraints().isEmpty() ? factory.one()
                    : factory.andAll(communities.getPositiveRegexConstraints().stream()
                    .map(r -> communityBDD(r,tbdd,route,context))
                    .collect(ImmutableSet.toImmutableSet()));
            if (communities.getNegativeRegexConstraints().isEmpty()) {
                return positiveBDD;
            } else {
                BDD negativeBDD = factory.orAll(communities.getNegativeRegexConstraints().stream()
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
                    BDD rangeBDD = isRelevantForDestination(r,range);
                    result = result.or(rangeBDD);
                }
                if (!positive){
                    result = result.not();
                }
                return result;
            }
        }

        public BDD build(TransferBDD tbdd, RoutingPolicy policy) {
            BDDRoute base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
            TransferBDD.Context context = policy == null ? null : TransferBDD.Context.forPolicy(policy);
            BDD clauseBDD = base.wellFormednessConstraints(true);
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
    }

    public boolean implies(Invariant post) {
        return (this.getBDD().imp(post.getBDD())).isOne();
    }

    public boolean impliedBy(Invariant post) {
        return (post.getBDD().imp(this.getBDD())).isOne();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj.getClass() == this.getClass()) {
            return this.getBDD().equals(((Invariant) obj).getBDD());
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return Objects.hash(tbdd, bdd);
    }

    @VisibleForTesting
    boolean validPrecondition(@Nonnull  Invariant pre, @Nonnull RoutingPolicy policy) {
        TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
        List<TransferReturn> paths;
        try {
            paths = tbdd.computePaths(policy.getStatements(),context,true);
        } catch (Exception e) {
            String name = policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
            throw new BatfishException("Unexpected error analyzing policy " + policy.getName()
                    + " in node " + name, e);
        }
        if (!paths.stream().filter(TransferReturn::getAccepted).toList().isEmpty()) {
            for (TransferReturn path : paths) {
                BDD pathAnnouncements = path.getInputConstraints();
                if (path.getAccepted()) { // path is permitted, need to check if precondition is sat, so are output
                    BDDRoute route = path.getOutputRoute();
                    BDD constraintsMatchingOutput = conditionsForConstraint(tbdd,this.getBDD(),false, route);
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
