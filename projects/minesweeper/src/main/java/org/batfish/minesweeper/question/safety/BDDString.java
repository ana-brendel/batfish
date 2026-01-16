package org.batfish.minesweeper.question.safety;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Sets;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.BgpRoute;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.LongSpace;
import org.batfish.datamodel.OriginMechanism;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.ReceivedFromSelf;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.routing_policy.Environment;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.datamodel.routing_policy.expr.Conjunction;
import org.batfish.datamodel.routing_policy.expr.Disjunction;
import org.batfish.datamodel.routing_policy.expr.MatchLocalPreference;
import org.batfish.datamodel.routing_policy.expr.MatchMetric;
import org.batfish.datamodel.routing_policy.expr.MatchPrefixSet;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.SetLocalPreference;
import org.batfish.datamodel.routing_policy.statement.SetMetric;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.bdd.TransferBDD;

import javax.annotation.Nonnull;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.batfish.minesweeper.question.searchroutepolicies.SearchRoutePoliciesAnswerer.longSpaceToBDD;
import static org.batfish.minesweeper.question.searchroutepolicies.SearchRoutePoliciesAnswerer.prefixSpaceToBDD;

public class BDDString {
    private final TransferBDD tbdd;
    private final BDD bdd; // the bdd stored here is not assumed to be well-formed
    private final BDDRoute base;
    private final Shortcuts shortcuts;

    private record PrefixSpacePair(PrefixSpace pos, PrefixSpace neg) {
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof PrefixSpacePair pair) {
                return pair.pos.equals(this.pos) && pair.neg.equals(this.neg);
            } else return false;
        }

        public PrefixSpacePair addPos(PrefixRange range) {
            if (pos.isEmpty())
                return new PrefixSpacePair(new PrefixSpace(range),new PrefixSpace(neg.getPrefixRanges()));
            PrefixSpace update = new PrefixSpace(pos.getPrefixRanges());
            update.intersection(new PrefixSpace(range));
            return new PrefixSpacePair(update,new PrefixSpace(neg.getPrefixRanges()));
        }
        public PrefixSpacePair addNeg(PrefixRange range) {
            PrefixSpace update = new PrefixSpace(neg.getPrefixRanges());
            update.addPrefixRange(range);
            return new PrefixSpacePair(new PrefixSpace(pos.getPrefixRanges()),update);
        }
        public Optional<stringOfBDD> getString(BDDRoute base) {
            BDD pos_bdd = prefixSpaceToBDD(pos, base, false);
            BDD neg_bdd = prefixSpaceToBDD(neg, base, true);
            BDD combined = pos_bdd.diff(neg_bdd);
            if (combined.isConstant()) {
                return Optional.empty();
            } else {
                Set<String> strings = pos.getPrefixRanges().stream()
                        .map(p->"prefix(" + p + ")").collect(Collectors.toSet());
                strings.addAll(neg.getPrefixRanges().stream()
                        .map(p->"!prefix(" + p + ")").collect(Collectors.toSet()));
                return Optional.of(new stringOfBDD(String.join(",",strings),combined,strings.size()));
            }
        }
    }

    public record stringOfBDD(@Nonnull String str, @Nonnull BDD bdd, int size) {
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof stringOfBDD other)
                return (other.bdd.equals(this.bdd));
            return false;
        }

        @Override
        public int hashCode() { return Objects.hashCode(bdd); }

        public stringOfBDD copy() {
            return new stringOfBDD(str,bdd.id(),size);
        }

        public stringOfBDD combineWith(stringOfBDD other) {
            BDD combo = other.bdd.and(this.bdd);
            if (combo.isOne()) {
                return new stringOfBDD("true",combo,1);
            } else if (combo.isZero()) {
                return new stringOfBDD("false",combo,1);
            } else {
                return new stringOfBDD(this.str + "," + other.str, combo,other.size + this.size);
            }
        }

        public static stringOfBDD combineAll(TransferBDD tbdd, Set<stringOfBDD> set) {
            if (set.isEmpty()) {
                return new stringOfBDD("true",tbdd.getFactory().one(),1);
            } else {
                BDD combined = tbdd.getFactory().andAll(set.stream().map(stringOfBDD::bdd).collect(Collectors.toSet()));
                if (combined.isOne()) {
                    return new stringOfBDD("true",combined,1);
                } else if (combined.isZero()) {
                    return new stringOfBDD("false",combined,1);
                } else {
                    int total = set.stream().mapToInt(stringOfBDD::size).sum();
                    String label = String.join(",",set.stream().map(stringOfBDD::str).collect(Collectors.toSet()));
                    assert !label.isEmpty();
                    return new stringOfBDD(label,combined,total);
                }
            }
        }
    }

    /// Record to hold information relevant to creating string representations for BDD -- somewhat hacky
    public record Shortcuts(Set<Long> meds, Set<Long> local_prefs, Set<Prefix> prefixes) {
        private void addMed(long l) { meds.add(l); }
        private void addLocalPref(long l) { local_prefs.add(l); }
        private void addPrefix(Prefix p) { prefixes.add(p); }
        private Set<stringOfBDD> medBDDs(BDDRoute base) {
            Set<stringOfBDD> result = new HashSet<>();
            meds.forEach(med -> {
                BDD bdd = longSpaceToBDD(LongSpace.of(med),base.getMed());
                result.add(new stringOfBDD("med(" + med + ")",bdd.id(),1));
                result.add(new stringOfBDD("!med(" + med + ")",bdd.id().not(),1));
            });
            return result;
        }
        private Set<stringOfBDD> localPrefBDDs(BDDRoute base) {
            Set<stringOfBDD> result = new HashSet<>();
            local_prefs.forEach(lp -> {
                BDD bdd = longSpaceToBDD(LongSpace.of(lp),base.getLocalPref());
                result.add(new stringOfBDD("med(" + lp + ")",bdd.id(),1));
                result.add(new stringOfBDD("!med(" + lp + ")",bdd.id().not(),1));
            });
            return result;
        }
        private Set<stringOfBDD> prefixBDDCombos(BDDRoute base) {
            Set<PrefixSpacePair> combos = new HashSet<>();
            for (Prefix prefix : prefixes) {
                PrefixRange exact = PrefixRange.fromPrefix(prefix);
                PrefixRange range = PrefixRange.sameAsOrMoreSpecificThan(prefix);
                Set<PrefixSpacePair> toAdd = new HashSet<>();
                // for each in the combos, add a new space with this prefix option
                combos.forEach(space -> {
                    toAdd.add(space.addPos(exact));
                    toAdd.add(space.addNeg(exact));
                    toAdd.add(space.addPos(range));
                    toAdd.add(space.addNeg(range));
                });
                combos.addAll(toAdd);
                // add each individually
                combos.add(new PrefixSpacePair(new PrefixSpace(exact),new PrefixSpace()));
                combos.add(new PrefixSpacePair(new PrefixSpace(),new PrefixSpace(exact)));
                combos.add(new PrefixSpacePair(new PrefixSpace(range),new PrefixSpace()));
                combos.add(new PrefixSpacePair(new PrefixSpace(),new PrefixSpace(range)));
            }
            Set<stringOfBDD> result = new HashSet<>();
            combos.forEach(p -> p.getString(base).ifPresent(result::add));
            return result;
        }
        private Set<stringOfBDD> prefixBDDs(BDDRoute base) {
            Set<stringOfBDD> result = new HashSet<>();
            prefixes.forEach(prefix -> {
                // exact matches to prefixes
                BDD matches = prefixSpaceToBDD(new PrefixSpace(PrefixRange.fromPrefix(prefix)), base, false);
                BDD avoids = prefixSpaceToBDD(new PrefixSpace(PrefixRange.fromPrefix(prefix)), base, true);
                result.add(new stringOfBDD("prefix(" + prefix + ")",matches,1));
                result.add(new stringOfBDD("!prefix(" + prefix + ")",avoids,1));
                // matches the bits of the prefix but might be longer
                PrefixRange range = PrefixRange.sameAsOrMoreSpecificThan(prefix);
                BDD matchesAny = prefixSpaceToBDD(new PrefixSpace(range), base, false);
                BDD avoidsAny = prefixSpaceToBDD(new PrefixSpace(range), base, true);
                result.add(new stringOfBDD("prefix(" + range + ")",matchesAny,1));
                result.add(new stringOfBDD("!prefix(" + range + ")",avoidsAny,1));
            });
            return result;
        }
        private boolean isRelevant(BDD bdd, Set<stringOfBDD> pairs) {
            int[] profile = bdd.varProfile();
            for (stringOfBDD sbdd : pairs) {
                int[] s_profile = sbdd.bdd.varProfile();
                for (int i = 0; i < profile.length; i++) {
                    assert i < s_profile.length;
                    if (0 < s_profile[i] && 0 < profile[i])
                        return true;
                }
            }
            return false;
        }
        /// Returns possible combos of constraints (restricted to variables present in target BDD)
        public Map<BDD,stringOfBDD> combos(TransferBDD tbdd,BDD target) {
            Set<stringOfBDD> considered = new HashSet<>();
            for (Map.Entry<BDD,String> entry : variableToString(tbdd).entrySet()) {
                stringOfBDD pos = new stringOfBDD(entry.getValue(), entry.getKey(),1);
                if (isRelevant(target,Set.of(pos))) {
                    considered.add(pos);
                    considered.add(new stringOfBDD("!" + entry.getValue(), entry.getKey().not(),1));
                }
            }

            BDDRoute base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
            Set<stringOfBDD> medStrBDDs = medBDDs(base);
            Set<stringOfBDD> localPrefStrBDDs = localPrefBDDs(base);
            Set<stringOfBDD> prefixStrBDDs = prefixBDDs(base);

            if (isRelevant(target,medStrBDDs)) considered.addAll(medStrBDDs);
            if (isRelevant(target,localPrefStrBDDs)) considered.addAll(localPrefStrBDDs);
            if (isRelevant(target,prefixStrBDDs)) considered.addAll(prefixStrBDDs);

            // Sets.powerSet throws an error when there are more than 30 possible elements.
            // Might be worth capping the power set at a lower threshold for timing.
            Set<Set<stringOfBDD>> combos = new HashSet<>(considered.size() > 30 ?
                    Sets.combinations(considered,2) : Sets.powerSet(considered));
            if (considered.size() > 30) combos.addAll(Sets.combinations(considered,1));

            //Set<stringOfBDD> prefixStrBDDs = prefixBDDCombos(base);
            // if prefixes are relevant try adding the different prefix combos, as option
//            if (isRelevant(target,prefixStrBDDs)) {
//                Set<Set<stringOfBDD>> toAdd = new HashSet<>();
//                prefixStrBDDs.forEach(p_str -> {
//                    combos.forEach(s -> {
//                        Set<stringOfBDD> copy = new HashSet<>(s);
//                        copy.add(p_str.copy());
//                        toAdd.add(copy);
//                    });
//                    toAdd.add(Set.of(p_str));
//                });
//                combos.addAll(toAdd);
//            }

            Map<BDD,stringOfBDD> result = new HashMap<>();

            combos.forEach(atoms -> {
                stringOfBDD combined = stringOfBDD.combineAll(tbdd,atoms);
                if (result.containsKey(combined.bdd)) {
                    stringOfBDD existing = result.get(combined.bdd);
                    if (combined.size() < existing.size())
                        result.put(combined.bdd,combined);
                    else if (combined.size() == existing.size() && combined.str.length() < existing.str.length())
                        result.put(combined.bdd,combined);
                } else if (!combined.bdd.isZero() && !combined.bdd.isOne()) {
                    result.put(combined.bdd,combined);
                }
            });

            return result;
        }
        public static Shortcuts ofConfigs(Collection<Configuration> configs) {
            Set<Long> meds = new HashSet<>();
            Set<Long> local_prefs = new HashSet<>();
            Set<Prefix> prefixes = new HashSet<>();
            configs.forEach(config -> {
                config.getRouteFilterLists().values().forEach(rfl -> rfl.getLines()
                        .forEach(line -> prefixes.add(line.getIpWildcard().toPrefix())));
                config.getRoutingPolicies().values().forEach(rp -> {
                    Shortcuts fromPolicy = ofPolicy(config,rp);
                    meds.addAll(fromPolicy.meds());
                    local_prefs.addAll(fromPolicy.local_prefs());
                    prefixes.addAll(fromPolicy.prefixes());
                });
            });
            return new Shortcuts(meds,local_prefs,prefixes);
        }
        public static Shortcuts ofPolicy(Configuration config, RoutingPolicy policy) {
            Set<Long> meds = new HashSet<>();
            Set<Long> local_prefs = new HashSet<>();
            Set<Prefix> prefixes = new HashSet<>();
            policy.getStatements().forEach(line -> {
                Shortcuts fromStatement = ofStatement(config, line);
                meds.addAll(fromStatement.meds);
                local_prefs.addAll(fromStatement.local_prefs);
                prefixes.addAll(fromStatement.prefixes);
            });
            return new Shortcuts(meds,local_prefs,prefixes);
        }
        private static Shortcuts ofBooleanExpr(Configuration c, BooleanExpr expr) {
            Shortcuts running = new Shortcuts(new HashSet<>(),new HashSet<>(),new HashSet<>());
            if (expr instanceof MatchLocalPreference localPref) {
                running.addMed(localPref.getMetric().evaluate(Environment.builder(c).build()));
            } else if (expr instanceof MatchPrefixSet prefix) {
                try { // I don't think this ever runs
                    running.addPrefix(prefix.getPrefix().evaluate(Environment.builder(c).build()));
                } catch (Exception ignored) {}
            } else if (expr instanceof MatchMetric metric) {
                running.addMed(metric.getMetric().evaluate(Environment.builder(c).build()));
            } else if (expr instanceof Conjunction conj) {
                running = running.combineWith(combineSet(conj.getConjuncts().stream()
                        .map(e -> ofBooleanExpr(c,e)).collect(Collectors.toSet())));
            } else if (expr instanceof Disjunction disj) {
                running = running.combineWith(combineSet(disj.getDisjuncts().stream()
                        .map(e -> ofBooleanExpr(c,e)).collect(Collectors.toSet())));
            }
            return running;
        }
        private static Shortcuts ofStatement(Configuration c, Statement line) {
            Shortcuts running = new Shortcuts(new HashSet<>(),new HashSet<>(),new HashSet<>());
            if (line instanceof If if_statement) {
                running = running.combineWith(ofBooleanExpr(c,if_statement.getGuard()));
                running = running.combineWith(combineSet(if_statement.getTrueStatements().stream()
                        .map(s -> ofStatement(c,s)).collect(Collectors.toSet())));
                running = running.combineWith(combineSet(if_statement.getFalseStatements().stream()
                        .map(s -> ofStatement(c,s)).collect(Collectors.toSet())));
            } else if (line instanceof SetMetric metric) {
                running.addMed(metric.getMetric().evaluate(Environment.builder(c).build()));
            } else if (line instanceof SetLocalPreference localPref) {
                running.addLocalPref(localPref.getLocalPreference().evaluate(Environment.builder(c).build()));
            } // weight?
            return running;
        }
        private Shortcuts combineWith(Shortcuts other) {
            Set<Long> meds = new HashSet<>(other.meds);
            Set<Long> local_prefs = new HashSet<>(other.local_prefs);
            Set<Prefix> prefixes = new HashSet<>(other.prefixes);
            local_prefs.addAll(this.local_prefs);
            prefixes.addAll(this.prefixes);
            return new Shortcuts(meds,local_prefs,prefixes);
        }
        private static Shortcuts combineSet(Set<Shortcuts> cuts) {
            Shortcuts running = new Shortcuts(new HashSet<>(),new HashSet<>(),new HashSet<>());
            for (Shortcuts cut : cuts)
                running = running.combineWith(cut);
            return running;
        }
    }

    private BDDString(TransferBDD tbdd, BDD bdd, Shortcuts shortcuts) {
        this.tbdd = tbdd;
        this.base = new BDDRoute(tbdd.getFactory(),tbdd.getConfigAtomicPredicates());
        this.bdd = bdd.and(this.base.wellFormednessConstraints(true));
        this.shortcuts = shortcuts;
    }

    public static String get(TransferBDD tbdd, BDD bdd, Shortcuts shortcuts) {
        BDDString str = new BDDString(tbdd,bdd,shortcuts);
        String result = str.str();
        assert !result.isEmpty();
        return result;
    }

    private static Map<BDD,String> variableToString(TransferBDD tbdd) {
        Map<BDD,String> map = new HashMap<>();
        BDDFactory factory = tbdd.getFactory();
        ConfigAtomicPredicates atoms = tbdd.getConfigAtomicPredicates();

        tbdd.getCommunityAtomicPredicates().forEach((cv,vars) -> {
            BDD comm_bdd = factory.orAll(vars.stream().map(factory::ithVar).collect(Collectors.toSet()));
            map.put(comm_bdd,"comm(" + cv.getRegex() + ")");
        });

        atoms.getStandardCommunityAtomicPredicates().getRegexAtomicPredicates()
                .forEach((rgx,vars) -> {
                    BDD as_path_bdd = factory.orAll(vars.stream().map(factory::ithVar).collect(Collectors.toSet()));
                    map.computeIfAbsent(as_path_bdd, k -> "comm(" + rgx.getRegex() + ")");
                });

        // TODO when adding the as path variables in the mix, it interferes with communities for some reason
        atoms.getAsPathRegexAtomicPredicates().getRegexAtomicPredicates()
                .forEach((rgx,vars) -> {
                    BDD as_path_bdd = factory.orAll(vars.stream().map(factory::ithVar).collect(Collectors.toSet()));
                    // this is current hack to avoid removing communities BDD when BDD overlap with as path bdd
                    // -- unsure why this is happening, maybe it has to do with taking the disjunction?
                    // currently, we only add the as path bdd when it doesn't overlap with any from the communities
                    map.computeIfAbsent(as_path_bdd, k -> "asPath(" + rgx.getRegex() + ")");
                });
        return map;
    }

    // TODO make this more efficient by storing the stringOfBDD which correspond to conditions in lattice
    private stringOfBDD commonImplicand(BDD target) {
        return null;
        // initially aimed to factor out the largest common factor from disjuncts - was buggy, removed
    }

    private String stringByte(byte[] bytes) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < base.getPrefix().size(); i++) {
            BDD bdd_var = base.getPrefix().getBitBDD(i);
            int var = bdd_var.var();
            if (bytes[var] < 0) {
                result.append("? ");
            } else if (bytes[var] == 0) {
                result.append("0 ");
            } else if (bytes[var] == 1) {
                result.append("1 ");
            } else {
                throw new BatfishException("ERR");
            }
        }
        result.append("... length: ");
        for (int i = 0; i < base.getPrefixLength().size(); i++) {
            BDD bdd_var = base.getPrefixLength().getBitBDD(i);
            int var = bdd_var.var();
            if (bytes[var] < 0) {
                result.append("? ");
            } else if (bytes[var] == 0) {
                result.append("0 ");
            } else if (bytes[var] == 1) {
                result.append("1 ");
            } else {
                throw new BatfishException("ERR");
            }
        }
        return result.toString();
    }

    private Optional<stringOfBDD> gatherDisjuncts(BDD target) {
        List<stringOfBDD> sorted = shortcuts.combos(tbdd,target).values().stream()
                .sorted(Comparator.comparingInt(stringOfBDD::size))
                .toList();
        String all = "\n + " + String.join("\n - ",sorted.stream().map(stringOfBDD::str).collect(Collectors.toSet()));
        BDD wf = base.wellFormednessConstraints(true);
        BDD wf_target = target.and(wf.id());
        Set<stringOfBDD> disjuncts = new HashSet<>();
        Set<String> imply = new HashSet<>();
        for (stringOfBDD stringOfBDD : sorted) {
            BDD check = stringOfBDD.bdd().and(wf.id());
            if (check.imp(wf_target).isOne()) {
                imply.add(stringOfBDD.str);
                if (disjuncts.stream().noneMatch(existing -> check.imp(existing.bdd.and(wf.id())).isOne())) {
                    disjuncts.removeIf(existing -> (existing.bdd.and(wf.id())).imp(check).isOne());
                    disjuncts.add(stringOfBDD);
                }
            }
        }
        BDD disjunction = tbdd.getFactory().orAll(disjuncts.stream().map(stringOfBDD::bdd).collect(Collectors.toSet()));
        String stringResult = String.join(" OR ",disjuncts.stream().map(stringOfBDD::str).collect(Collectors.toSet()));
        assert wf_target.equals(disjunction.and(wf));
        if (!wf_target.equals(disjunction.and(wf))) {
            String msg = disjuncts.isEmpty() ? " There were no disjunctions which were gathered." : "";
            String curr = "\nCurrent Result -- " + stringResult;

            boolean t_impl_r = wf_target.imp(disjunction.and(wf)).isOne();
            String l_to_r = "\nTarget => Result ? -- " + t_impl_r +
                    (t_impl_r ? "" : "\n\t -- counter: " + counter(wf, wf_target, disjunction.and(wf)));
            boolean r_impl_t = (disjunction.and(wf)).imp(wf_target).isOne();
            String r_to_l = "\nResult => Target ? -- " + r_impl_t +
                    (r_impl_t ? "" : "\n\t -- counter: " + counter(wf, disjunction.and(wf), wf_target));

            String testing = "\n + " + String.join("\n + ",imply);

//            throw new BatfishException("Error in parsing the string representation of the BDD." +
//                    msg + curr + l_to_r + r_to_l + testing);
            return Optional.empty();
        }
        return Optional.of(new stringOfBDD(stringResult,disjunction.and(wf),disjuncts.stream().mapToInt(stringOfBDD::size).sum()));
    }

    private static String nonDefaultRoute(Bgpv4Route route) {
        ImmutableList.Builder<String> features = ImmutableList.builder();
        // Always include the IP address
        features.add("network=" + route.getNetwork());
        if (route.getAdministrativeCost() != 0)
            features.add("admin=" + route.getAdministrativeCost());
        if (route.getTag() != 0)
            features.add("tag=" + route.getTag());
        if (route.getAsPath().length() != 0)
            features.add("asPath=" + route.getAsPath());
        if (!route.getClusterList().isEmpty())
            features.add("clusterList=" + route.getClusterList());
        if (!route.getCommunities().getCommunities().isEmpty())
            features.add("communities=" + route.getCommunities());
        if (route.getLocalPreference() != BgpRoute.DEFAULT_LOCAL_PREFERENCE)
            features.add("localPreference=" + route.getLocalPreference());
        if (route.getMetric() != 0)
            features.add("med=" + route.getMetric());
        //if (route.getNextHop() != ...)
        //features.add("nextHop=" + route.getNextHop());
        if (!route.getOriginatorIp().equals(Ip.ZERO))
            features.add("originatorIp=" + route.getOriginatorIp());
        if (route.getOriginMechanism() != OriginMechanism.LEARNED)
            features.add("originMechanism=" + route.getOriginMechanism().name());
        //if (route.getOriginType() != OriginType.INCOMPLETE)
        //features.add("originType=" + route.getOriginType().name());
        if (route.getProtocol() != RoutingProtocol.BGP)
            features.add("srcProtocol=" + route.getProtocol().name());
        if (route.getReceivedFrom() != ReceivedFromSelf.instance())
            features.add("receivedFrom=" + route.getReceivedFrom());
        if (route.getReceivedFromRouteReflectorClient())
            features.add("receivedFromRouteReflectorClient=" + true);
        //features.add("srcProtocol=" + route.getSrcProtocol().name());
        if (route.getWeight() != 0)
            features.add("weight=" + route.getWeight());
        return "Bgpv4Route{" + String.join(", ", features.build()) + "}";
    }

    private String counter(BDD wf, BDD expected, BDD result) {
        BDD constraint = wf.and(expected.and(result.not()));
        if (constraint.isZero() || wf.equals(constraint)) return "NO COUNTER";
        BDD model = ModelGeneration.constraintsToModel(constraint, tbdd.getConfigAtomicPredicates());
        Bgpv4Route counter = ModelGeneration.satAssignmentToBgpInputRoute(model, tbdd.getConfigAtomicPredicates());
        return nonDefaultRoute(counter);
    }

    private String str() {
        if (this.bdd.isZero()) return "false";
        BDD wf = base.wellFormednessConstraints(true);
        if (wf.equals(this.bdd.and(wf.id()))) return "true";
        BDD running = this.bdd.id().and(wf.id());
        // this wasn't working, so now this just return null
        stringOfBDD factors = commonImplicand(running);
        if (factors != null) {
            running.existEq(factors.bdd);
        }
        // at this point, running should hold a disjunction of conditions to be considered
        if (running.isZero() || wf.equals(running.and(wf.id()))) {
            return running.isZero() ? "false" : "true";
        } else if (factors != null){
            // this branch should never run at this point (factors is always null right now)
            Optional<stringOfBDD> disjuncts = gatherDisjuncts(running);
            if (disjuncts.isPresent()) {
                BDD wf_factor = factors.bdd.and(wf.id());
                assert (this.bdd.id().and(wf.id())).equals(wf_factor.and(disjuncts.get().bdd()));
                return factors.str() + " AND [" + disjuncts.get().str() + "]";
            } else {
                return "STRING OF BDD ERROR";
            }
        } else {
            Optional<stringOfBDD> disjuncts = gatherDisjuncts(running);
            if (disjuncts.isPresent()) {
                assert (this.bdd.id().and(wf)).equals(disjuncts.get().bdd());
                return disjuncts.get().str();
            } else {
                return "STRING OF BDD ERROR";
            }
        }
    }
}
