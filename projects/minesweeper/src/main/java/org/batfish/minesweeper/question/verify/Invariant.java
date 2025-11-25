package org.batfish.minesweeper.question.verify;

import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.LineAction;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchExpr;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.CommunityMatchExprToBDD;
import org.batfish.minesweeper.bdd.CommunitySetMatchExprToBDD;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferBDDUtils;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.searchroutepolicies.BgpRouteConstraints;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.apache.commons.lang3.ObjectUtils.firstNonNull;
import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;
import static org.batfish.minesweeper.bdd.TransferBDDUtils.makeRoutePairing;
import static org.batfish.minesweeper.question.searchroutepolicies.SearchRoutePoliciesAnswerer.routeConstraintsToBDD;

public class Invariant {
    private final TransferBDD tbdd;
    private final BDD bdd; // the bdd stored here is not assumed to be well-formed
    private final BDDRoute base;
    public final String str;

    /**
     * Provided BDD is not assumed to represent a well-formed BDDRoute
     * @param tbdd the TransferBDD to be used
     * @param bdd BDD to be represented by invariant
     */
    public Invariant(TransferBDD tbdd, BDD bdd) {
        this.tbdd = tbdd;
        this.bdd = bdd;
        this.base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        this.str = "";
    }

    /**
     * Default invariant is true
     * @param tbdd the TransferBDD to be used
     */
    public Invariant(TransferBDD tbdd) {
        this.tbdd = tbdd;
        this.bdd = tbdd.getFactory().one();
        this.base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        this.str = "True";
    }

    public Invariant(TransferBDD tbdd, BDD bdd, String str) {
        this.tbdd = tbdd;
        this.bdd = bdd;
        this.base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        this.str = str;
    }

    public static Invariant getFalse(TransferBDD tbdd) {
        return new Invariant(tbdd,tbdd.getFactory().zero());
    }

    public Invariant negate() {
        return new Invariant(tbdd,bdd.not(),"False");
    }

    /**
     * Creates an invariant type from a BgpRouteConstraint (constants used for routeConstraintsToBDD expect that
     * this invariant will be used to start a weakest precondition based inference)
     * @param tbdd the TransferBDD to be used
     * @param constraint constraint to be reflected by invariant
     * @param direction IN for invariant on node, OUT for invariant on edge (inherited from routeConstraintsToBDD)
     * @param context context used (inherited from routeConstraintsToBDD)
     * @return invariant representative of constraint
     */
    // TODO check if this makes sense
    public static Invariant ofBgpRouteConstraints(TransferBDD tbdd, BgpRouteConstraints constraint,
                     Environment.Direction direction, TransferBDD.Context context) {
        BDDRoute base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        // outputRoute fixed to true because if an invariant is created this way, we will be using it as a post constraint
        return new Invariant(tbdd,routeConstraintsToBDD(constraint,base.deepCopy(),true,tbdd,context,direction));
    }

    public static final class Builder {
        private final String str;
        private final List<ClauseBuilder> clauses = new ArrayList<>();

        private Builder () { this.str = null; }
        private Builder (String str) { this.str = str; }

        public Builder addClause(ClauseBuilder clause) {
            clauses.add(clause);
            return this;
        }

        public List<ClauseBuilder> getClauses() {
            return clauses;
        }

        public Invariant build(TransferBDD tbdd) {
            return this.build(tbdd,null);
        }

        public Invariant build(TransferBDD tbdd, RoutingPolicy policy) {
            Collection<BDD> BDDs = clauses.stream().map(clause -> clause.build(tbdd,policy)).collect(Collectors.toSet());
            if (this.str == null) {
                return new Invariant(tbdd,tbdd.getFactory().orAll(BDDs));
            } else {
                return new Invariant(tbdd,tbdd.getFactory().orAll(BDDs),this.str);
            }
        }

        @JsonCreator
        @VisibleForTesting
        static Builder forValue(@Nonnull String value) {
            Builder builder = new Builder(value);
            String[] splits = value.trim().split("]");
            for (String clause : splits) {
                String trimmed = clause.trim();
                if (!trimmed.startsWith("[") && !trimmed.isEmpty()) {
                    throw new BatfishException("String parsing into property (Invariant.Builder) failed. " +
                            "A property should be in DNF form - [clause1][clause2]...[clause_n]. " +
                            "The trimmed clause is: " + trimmed);
                } else if (!trimmed.isEmpty()){
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

        private static BDD communityBDD(RegexConstraint regex, TransferBDD tbdd, BDDRoute route, TransferBDD.Context context) {
            return switch (regex.getRegexType()) {
                case REGEX -> {
                    Map<String,Set<Integer>> stringKeys = new HashMap<>();
                    tbdd.getConfigAtomicPredicates()
                            .getStandardCommunityAtomicPredicates().getRegexAtomicPredicates()
                            .forEach((key,value) -> stringKeys.put(key.getRegex(),value));
                    Set<Integer> cvi = stringKeys.get(regex.getRegex());
                    if (cvi == null) {
                        // The comparison on the CV directly doesn't seem to work, so I matched with the regex
                        throw new BatfishException("Null variable list for regex " + regex.getRegex());
                    }
                    Collection<BDD> bdds = cvi.stream()
                            .map(i -> route.getCommunityAtomicPredicates()[i])
                            .collect(ImmutableSet.toImmutableSet());
                    yield tbdd.getFactory().orAll(bdds);
                }
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

        /// Added to help parse a string corresponding to a single clause
        private static Invariant.ClauseBuilder parseForClauseBuilder(String value) {
            if (value.trim().isEmpty()) {
                return createClause(null,null,null);
            }
            PrefixSpace positivePrefix = new PrefixSpace();
            PrefixSpace negativePrefix = new PrefixSpace();
            ImmutableList.Builder<RegexConstraint> communities = ImmutableList.builder();
            String[] atoms = value.trim().split("&");
            for (String atom: atoms) {
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
                                Optional<Prefix> prefix = Prefix.tryParse(input);
                                if (prefix.isEmpty()) {
                                    throw new BatfishException("Provided positive prefix (" + input + ") is not a valid prefix");
                                } else if (!positive) {
                                    negativePrefix.addPrefix(prefix.get());
                                } else {
                                    if (positivePrefix.isEmpty()) {
                                        positivePrefix.addPrefix(prefix.get());
                                    } else {
                                        positivePrefix.intersection(new PrefixSpace(PrefixRange.fromPrefix(prefix.get())));
                                    }
                                }
                                break;
                            default:
                                throw new BatfishException("Error when parsing string for clause -" +
                                        " check [" + category + "] which does not match a supported feature (comm or prefix) with ! " +
                                        "implying the following value is negated (The whole value provided is [" + value + "])");
                        }
                    } else {
                        throw new BatfishException("Error when parsing string for clause -" +
                                " each clause should have format [field1=value1,...,field_n=value_n]. " +
                                " Current field supported: comm, prefix.");
                    }
                }
            }
            return createClause(positivePrefix,negativePrefix,new RegexConstraints(communities.build()));
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

    public static ClauseBuilder createClause(PrefixSpace pos, PrefixSpace neg, RegexConstraints comms) {
        return clauseBuilder()
                .matchPrefix(firstNonNull(pos,new PrefixSpace()))
                .avoidPrefix(firstNonNull(neg,new PrefixSpace()))
                .setCommunities(firstNonNull(comms,new RegexConstraints()));
    }

    /// Returns the BDD stored in this invariant (with well-formed constraint applied)
    public BDD wellFormedBDD() {
        return base.wellFormednessConstraints(true).and(bdd.id());
    }

    /// Returns true if the invariant is false
    public boolean isFalse() {
        return this.wellFormedBDD().isZero();
    }

    /// Returns true if the invariant is true (for any well-formed route)
    public boolean isTrue() {
        return this.wellFormedBDD().equals(base.wellFormednessConstraints(true));
    }

    public Invariant copy() {
        return new Invariant(tbdd,bdd.id());
    }

    /**
     * Determines BDD corresponding to the input constraints that must hold in order for the invariant condition to hold on output.
     * @param tbdd transfer bdd used
     * @param inv invariant to hold on output route
     * @param r route holding the modifications and conditions after policy
     * @return bdd constraining input in order to satisfy invariant on output
     */
    public static BDD conditionsForConstraint(TransferBDD tbdd, BDD inv, @Nonnull BDDRoute r) {
        if (inv.isOne()) { // if the invariant is always true... should I do one for always false too?
            return tbdd.getFactory().one();
        } else {
            BDDPairing pairing = makeRoutePairing(r,tbdd);
            return inv.veccompose(pairing);
        }
    }

    /**
     * Synthesizes the weakest precondition for this invariant to hold after the provided policy is executed. Note, this
     * method does not guarantee that there exists a route that satisfies the invariant, just that any route which is permitted
     * will satisfy the invariant.
     * @param policy weakest precondition for this policy
     * @return weakest precondition for this invariant to hold on policy
     */
    public Invariant weakestPrecondition(@Nonnull RoutingPolicy policy) {
        if (policy.getStatements().isEmpty()) {
            if (policy.getOwner() == null || policy.getOwner().getDefaultInboundAction() == LineAction.PERMIT) {
                return this.copy(); // default is permit, so invariant itself is the weakest precondition
            } else {
                return new Invariant(tbdd); // default is deny so the weakest precondition is true
            }
        } else {
            TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
            List<TransferReturn> paths;
            try {
                paths = tbdd.computePaths(policy.getStatements(),context,true);
            } catch (Exception e) {
                String name = policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
                throw new BatfishException("Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
            }
            BDD acceptedWP = TransferBDDUtils.weakestPrecondition(paths,this.wellFormedBDD(),tbdd,
                    (post,path) -> conditionsForConstraint(tbdd,post,path.getOutputRoute()));
            BDD weakest = acceptedWP.or(TransferBDDUtils.deniedRoutes(paths,tbdd));
            return new Invariant(tbdd,weakest);
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
        return new Invariant(left.tbdd, left.bdd.and(right.bdd));
    }

    /**
     * Indicates if this invariant implies the provided invariant
     * @param post postcondition for implication
     * @return true if implies provided invariant
     */
    public boolean implies(Invariant post) {
        return (this.wellFormedBDD().imp(post.wellFormedBDD())).isOne();
    }

    /**
     * Indicates if this invariant is implied by provided invariant
     * @param pre precondition for implication
     * @return true if implied by provided invariant
     */
    public boolean impliedBy(Invariant pre) {
        return (pre.wellFormedBDD().imp(this.wellFormedBDD())).isOne();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj.getClass() == this.getClass()) {
            return this.wellFormedBDD().equals(((Invariant) obj).wellFormedBDD());
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return Objects.hash(tbdd, bdd);
    }

    /// Returns invariant as string, but is not robust ("quick and dirty")
    public String weakDisplay(List<String> prefixesConsidered) {
        WeakReader reader = new WeakReader(this);
        return String.join(" OR ",reader.read(prefixesConsidered));
    }

    /// Class for displaying the invariant (easily separated)
    private class WeakReader {
        private final Invariant inv;

        private WeakReader(Invariant inv) { this.inv = inv;}

        private BDD communityBDD(RegexConstraint comm) {
            return Invariant.createClause(null,null,new RegexConstraints(List.of(comm))).build(inv.tbdd,null);
        }

        private BDD prefixBDD(PrefixSpace space, boolean positive) {
            return Invariant.createClause(positive ? space : null,positive ? null : space,null).build(inv.tbdd,null);
        }

        private boolean filterRedundant(Set<Map.Entry<String,BDD>> set) {
            List<String> positives = set.stream().map(Map.Entry::getKey).filter(key -> key.startsWith("has"))
                    .map(key -> key.replaceFirst("has ","")).toList();
            List<String> negatives = set.stream().map(Map.Entry::getKey).filter(key -> key.startsWith("does not have"))
                    .map(key -> key.replaceFirst("does not have ","")).toList();
            return positives.stream().noneMatch(negatives::contains);
        }

        private Map.Entry<String,BDD> makeOneEntry(Set<Map.Entry<String,BDD>> set) {
            ImmutableList.Builder<String> builder = ImmutableList.builder();
            BDD clause = inv.base.wellFormednessConstraints(true);
            for (Map.Entry<String,BDD> entry : set) {
                clause = clause.and(entry.getValue());
                builder.add(entry.getKey());
            }
            return new AbstractMap.SimpleEntry<>(String.join(" and ",builder.build()),clause);
        }

        private List<String> read(List<String> prefixesConsidered) {
            Map<String,BDD> atoms = new HashMap<>();

            for (CommunityVar cv : inv.tbdd.getConfigAtomicPredicates().getStandardCommunityAtomicPredicates().getRegexes()) {
                String regex = cv.getRegex();
                atoms.put("has comm " + regex, communityBDD(new RegexConstraint(regex,false)));
                atoms.put("does not have comm " + regex, communityBDD(new RegexConstraint(regex,true)));
            }

            for (String prefixString : prefixesConsidered) {
                Optional<Prefix> prefix = Prefix.tryParse(prefixString);
                Optional<Ip> ip = Ip.tryParse(prefixString);
                PrefixSpace PREFIX;
                if (prefix.isPresent()) {
                    PREFIX = new PrefixSpace(PrefixRange.fromPrefix(prefix.get()));
                } else if (ip.isPresent()) {
                    PREFIX = new PrefixSpace(PrefixRange.fromPrefix(ip.get().toPrefix()));
                } else {
                    throw new BatfishException("Cannot parse provided ip/prefix string for display.");
                }
                atoms.put("has prefix " + prefixString,prefixBDD(PREFIX,true));
                atoms.put("does not have prefix " + prefixString,prefixBDD(PREFIX,false));
            }

            Set<Set<Map.Entry<String,BDD>>> combos = Sets.powerSet(atoms.entrySet());

            Set<Map.Entry<String,BDD>> clauses = combos.stream().filter(this::filterRedundant).map(this::makeOneEntry).collect(Collectors.toSet());

            if (inv.isFalse()) {
                return ImmutableList.of("false");
            } else if (inv.isTrue()) {
                return ImmutableList.of("true");
            } else {
                ImmutableList.Builder<Map.Entry<String, BDD>> builder = ImmutableList.builder();
                List<Map.Entry<String, BDD>> sorted = clauses.stream()
                        .sorted(Comparator.comparingInt(entry -> entry.getKey().length())).toList();
                BDD disjunction = tbdd.getFactory().zero();
                for (Map.Entry<String, BDD> entry : sorted) {
                    BDD clause = base.wellFormednessConstraints(true).and(entry.getValue());
                    if (clause.imp(inv.wellFormedBDD()).isOne()) {
                        boolean keep = true;
                        for (Map.Entry<String, BDD> added : builder.build()) {
                            if (keep) {
                                BDD in = added.getValue().and(base.wellFormednessConstraints(true));
                                if (clause.imp(in).isOne()) { // if this clause implies any that are kept, we don't need to add
                                    keep = false;
                                }
                            }
                        }
                        if (keep) {
                            builder.add(entry);
                            disjunction = disjunction.or(entry.getValue());
                        }
                    }
                }
                // attempt at better pruning for readability (removes redundant clauses)
                List<Map.Entry<String, BDD>> kept = builder.build();
                List<Map.Entry<String, BDD>> result = builder.build().stream()
                        .filter(entry -> kept.stream().allMatch(other ->
                                !entry.getValue().imp(other.getValue()).isOne() || other.getValue().equals(entry.getValue()))).toList();
                assert inv.wellFormedBDD().equals(disjunction);
                return result.stream().map(Map.Entry::getKey).toList();
            }
        }
    }

    /**
     * Intended for testing, checks if the provided precondition ensures this invariant holds on
     * the result of the policy being applied.
     * @param pre precondition for incoming routes
     * @param policy policy to be executed
     * @return true if this invariant holds as postcondition
     */
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
                    BDD constraintsMatchingOutput = conditionsForConstraint(tbdd,this.wellFormedBDD(), route);
                    BDD constrainedInput = pathAnnouncements.and(pre.wellFormedBDD());
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
