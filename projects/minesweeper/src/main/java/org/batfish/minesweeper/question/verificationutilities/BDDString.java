package org.batfish.minesweeper.question.verificationutilities;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Prefix;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class BDDString {
    private final BDD bdd; // the bdd stored here is not assumed to be well-formed
    private final BDDFactory factory;
    private final BDDRoute base;
    private final BDD wf;

    private final BDD prefixInfoSupport;
    private final Map<CommunityVar, Set<Integer>> communities;

    private final Map<Integer,String> atomicPredicateBank = new HashMap<>();
    private final Map<String,Integer> stringBank = new HashMap<>();

    public static String get(TransferBDD tbdd, BDD bdd) {
        BDD wf = tbdd.getOriginalRoute().wellFormednessConstraints(true);
        if (bdd.isZero()) {
            return "False";
        } else if (bdd.isOne() || wf.equals(wf.and(bdd))) {
            return "True";
        } else {
            BDDString str = new BDDString(tbdd,wf.and(bdd));
            return str.getString();
        }
    }

    private BDDString(TransferBDD tbdd, BDD bdd) {
        this.bdd = bdd.id();
        this.factory = tbdd.getFactory();
        this.base = tbdd.getOriginalRoute();
        this.wf = this.base.wellFormednessConstraints(true);
        this.prefixInfoSupport = this.base.getPrefix().support().and(this.base.getPrefixLength().support());

        // make the only variable corresponding to "all communities" be the one isolated for it
        this.communities = tbdd.getCommunityAtomicPredicates();
        Set<Integer> communityVars = this.communities.entrySet().stream()
                .filter(entry -> !entry.getKey().getRegex().equals("[^^$]*"))
                .flatMap(entry -> entry.getValue().stream()).collect(Collectors.toSet());
        Set<Integer> update = this.communities.get(CommunityVar.from("[^^$]*")).stream()
                .filter(var -> !communityVars.contains(var)).collect(Collectors.toSet());
        this.communities.put(CommunityVar.from("[^^$]*"),update);
//        this.tbdd.getConfigAtomicPredicates().getAsPathRegexAtomicPredicates().getRegexAtomicPredicates();
    }

    private BDD dropVariables(BDD original, BDD toRemove) {
        return original.exist(toRemove.support());
    }

    private Integer addStringToBank(String label) {
        if (stringBank.containsKey(label)) {
            assert atomicPredicateBank.containsKey(stringBank.get(label));
            return stringBank.get(label);
        } else {
            int var = atomicPredicateBank.size() + 1;
            atomicPredicateBank.put(var,label);
            stringBank.put(label,var);
            return var;
        }
    }

    private String getFromStringBank(Integer var) {
        if (var < 0) {
            return "!" + this.atomicPredicateBank.get(-var);
        } else {
            return var == 0 ? "+" : this.atomicPredicateBank.get(var);
        }
    }

    /// Currently, the only atomic predicates which are considered are communities (not AS paths)
    private Pair<BDD, Set<Integer>> fetchAtomicPredicateBDD(byte[] assignment) {
        Set<Integer> strings = new HashSet<>();
        Set<BDD> running = new HashSet<>();
        for (CommunityVar var : this.communities.keySet()) {
            for (Integer v : this.communities.get(var)) {
                assert v < assignment.length;
                if (assignment[v] == 0) {
                    // false - community is explicitly not set
                    running.add(this.factory.ithVar(v).not());
                    // needs to be negative because it is negated
                    int varLabel = - this.addStringToBank("comm(" + var.getRegex() + ")");
                    strings.add(varLabel);
                    break;
                } else if (assignment[v] == 1) {
                    // true - community is explicitly set
                    running.add(this.factory.ithVar(v));
                    int varLabel = this.addStringToBank("comm(" + var.getRegex() + ")");
                    strings.add(varLabel);
                    break;
                } else {
                    // don't care - this atomic predicate is not handled
                    assert assignment[v] == -1;
                }
            }
        }
        return Pair.of(this.factory.andAll(running),strings);
    }

    private BDD bddOfByteArr(byte[] arr) {
        Set<BDD> running = new HashSet<>();
        for (int v = 0; v < arr.length; v++) {
            if (arr[v] == 0)
                running.add(this.factory.ithVar(v).not());
            else if (arr[v] == 1)
                running.add(this.factory.ithVar(v));
            else
                assert arr[v] == -1;
        }
        return this.factory.andAll(running);
    }

    private Prefix prefixOfBDD(BDD bdd) {
        Ip ip = Ip.create(this.base.getPrefix().satAssignmentToLong(bdd));
        int length = (int) this.base.getPrefixLength().satAssignmentToLong(bdd);
        // included check for invalid prefixes -- might be wrong
        return Prefix.create(ip, (0 <= length && length <= 32) ? length : 32);
    }

    /// Returns set which is disjunction over the prefixes - first BDD in pair is prefix, second is remaining bdd for pass
    private Optional<Set<Pair<Pair<BDD,BDD>, Integer>>> extractPrefixes(Set<BDD> disjuncts) {
        // collect distinct prefix groups
        Map<BDD,Set<BDD>> prefixBDDGroups = new HashMap<>();
        for (BDD assignment : disjuncts) {
            BDD remaining = assignment.exist(this.prefixInfoSupport);
            BDD prefixBDD = assignment.project(this.prefixInfoSupport);
            if (!prefixBDDGroups.containsKey(remaining))
                prefixBDDGroups.put(remaining,new HashSet<>());
            prefixBDDGroups.get(remaining).add(prefixBDD);
        }

        // process common prefix groups - right now, we are just checking for positive prefixes, or negation
        Map<BDD,Set<Pair<Pair<BDD,Prefix>,Boolean>>> prefixGroups = new HashMap<>();
        for (BDD remaining : prefixBDDGroups.keySet()) {
            Set<BDD> differentPrefixes = prefixBDDGroups.get(remaining);
            Set<Pair<Pair<BDD,Prefix>,Boolean>> prefixes =
                    differentPrefixes.stream().map(b ->
                            Pair.of(Pair.of(b.project(this.prefixInfoSupport),this.prefixOfBDD(b)),true))
                            .collect(Collectors.toSet());
            if (prefixes.stream().allMatch(pair ->
                    pair.getLeft().getRight().getStartIp().equals(Ip.parse("0.0.0.0")))) {
                // if all the prefixes are some zero ip, treat that as no prefix
                prefixes.clear();
            } else if (prefixes.size() > 1) {
                BDD disjunction = this.factory.orAll(differentPrefixes);
                BDD potential = this.wf.and(disjunction.not());
                Set<Pair<BDD,Prefix>> negated = new HashSet<>();
                BDD.AllSatIterator iterator = potential.allsat();
                while (iterator.hasNext()) {
                    BDD assignment = bddOfByteArr(iterator.next());
                    BDD projection = assignment.project(this.prefixInfoSupport);
                    Prefix prefix = this.prefixOfBDD(assignment);
                    negated.add(Pair.of(projection,prefix));
                    // only switches to the negation if there is one negated prefix
                    if (negated.size() > 1) break;
                }
                // only switches to the negation if there is one negated prefix
                if (negated.size() == 1) {
                    prefixes = Set.of(Pair.of(negated.stream().findFirst().get(),false));
                }
            }
            if (!prefixes.isEmpty()) prefixGroups.put(remaining,prefixes);
        }

        if (prefixGroups.isEmpty()) {
            return Optional.empty();
        } else {
            return Optional.of(prefixGroups.entrySet().stream().flatMap(entry -> {
                BDD remaining = entry.getKey();
                Set<Pair<Pair<BDD,Prefix>,Boolean>> prefixes = entry.getValue();
                if (prefixes.isEmpty()) {
                    return Stream.of(Pair.of(Pair.of(this.factory.one(),remaining),0));
                } else {
                    return prefixes.stream().map(prefix -> {
                        Integer var = this.addStringToBank("prefix(" + prefix.getLeft().getRight().toString() + ")");
                        BDD prefixBDD = prefix.getLeft().getLeft();
                        return Pair.of(Pair.of(prefixBDD, remaining), prefix.getRight() ? var : -var);
                    });
                }
            }).collect(Collectors.toSet()));
        }
    }

    private Set<BDD> checkSetForConstant(Set<BDD> set) {
        Optional<BDD> single = set.stream().findFirst();
        if (set.size() == 1 && (this.wf.equals(this.wf.and(single.get())) || single.get().isOne())) {
            return new HashSet<>();
        }  else {
            assert single.isEmpty() || !single.get().isZero();
            BDD disjunction = this.factory.orAll(set);
            if (this.wf.equals(this.wf.and(disjunction)) || disjunction.isOne()) {
                return new HashSet<>();
            } else {
                return set;
            }
        }
    }

    private Set<Set<Integer>> resolution(Set<Set<Integer>> clauses) {
        Set<Integer> atoms = clauses.stream().filter(clause -> clause.size() == 1)
                .map(clause -> clause.stream().findFirst().get())
                .collect(Collectors.toSet());
        for (Integer atom : atoms) {
            // see if we can remove the negation of the atom from any of the other clauses
            if (atom != 0 && clauses.stream().anyMatch(clause -> clause.size() != 1 &&
                    clause.stream().anyMatch(v -> v == -atom))) {
                // if we can remove negation of atom, filter it out and recall
                return resolution(clauses.stream()
                        .map(clause -> clause.size() == 1 ? clause
                                : clause.stream().filter(v -> v != -atom)
                                .collect(Collectors.toSet()))
                        .collect(Collectors.toSet()));
            }
        }
        // in the case that none of the atoms can work towards resolution, we terminate
        return clauses;
    }

    private String getString() {
        Map<BDD,Set<Integer>> bddToDisplays = new HashMap<>();
        Map<BDD,Set<BDD>> disjunctsByAtomicPredicates = new HashMap<>();
        BDD.AllSatIterator iterator = this.bdd.allsat();

        while (iterator.hasNext()) {
            // for each satisfying assignment, pull out the atomic predicates
            byte[] sat = iterator.next();
            Pair<BDD, Set<Integer>> atoms = this.fetchAtomicPredicateBDD(sat);
            BDD remaining = this.dropVariables(this.bddOfByteArr(sat),atoms.getLeft());

            // if we haven't seen this set of atomic predicates yet, add to maps
            if (!disjunctsByAtomicPredicates.containsKey(atoms.getLeft())) {
                assert !bddToDisplays.containsKey(atoms.getLeft());
                bddToDisplays.put(atoms.getLeft(),atoms.getRight());
                disjunctsByAtomicPredicates.put(atoms.getLeft(), new HashSet<>());
            }

            // assert that the both are present, update the atomic predicates to include the disjunction
            assert disjunctsByAtomicPredicates.containsKey(atoms.getLeft());
            assert bddToDisplays.containsKey(atoms.getLeft());
            disjunctsByAtomicPredicates.get(atoms.getLeft()).add(remaining);
        }

        // deals with prefixes - haven't touched yet
        Map<BDD,Set<BDD>> pullPrefixes = new HashMap<>();
        for (BDD aps : disjunctsByAtomicPredicates.keySet()) {
            Optional<Set<Pair<Pair<BDD,BDD>, Integer>>> pulled = this.extractPrefixes(disjunctsByAtomicPredicates.get(aps));
            if (pulled.isEmpty()) {
                // prefixes are irrelevant
                pullPrefixes.put(aps,disjunctsByAtomicPredicates.get(aps));
            } else {
                Set<Pair<Pair<BDD,BDD>, Integer>> prefixDisjuncts = pulled.get();
                // for each prefix disjunct, join with the common and accumulate remaining disjuncts
                prefixDisjuncts.forEach(pair -> {
                    BDD remaining = pair.getLeft().getRight();
                    Integer prefixLabel = pair.getRight();
                    BDD prefixBDD = prefixLabel < 0 ? pair.getLeft().getLeft().not() : pair.getLeft().getLeft();
                    // combine the prefix bdd with the existing common bdd
                    BDD combined = prefixBDD.and(aps.id());
                    // update the display if not included
                    if (!bddToDisplays.containsKey(combined)) {
                        bddToDisplays.put(combined, new HashSet<>(bddToDisplays.get(aps)));
                        if (prefixLabel != 0) bddToDisplays.get(combined).add(prefixLabel);
                    }
                    // add this disjunct to the set
                    if (!pullPrefixes.containsKey(combined)) pullPrefixes.put(combined,new HashSet<>());
                    pullPrefixes.get(combined).add(remaining);
                });
            }
        }

        // sanity check - displayed bdd equals the input bdd
        if (!(this.factory.orAll(pullPrefixes.entrySet().stream().map(disjunct -> {
            BDD common = disjunct.getKey();
            BDD internalDisjuncts = this.factory.orAll(disjunct.getValue());
            return common.and(internalDisjuncts);
        }).collect(Collectors.toSet())).and(this.wf)).equals(this.bdd))
            return "ERR (BDD String)";

        // simplify the formula then translate to strings and disjoin each conjunction
        return this.resolution(pullPrefixes.entrySet().stream()
                .map(entry -> {
                    Set<Integer> predicates = bddToDisplays.get(entry.getKey());
                    if (!checkSetForConstant(entry.getValue()).isEmpty()) predicates.add(0);
                    return predicates;
                }).collect(Collectors.toSet())).stream().map(clause ->
                        String.join(",",clause.stream().map(this::getFromStringBank).sorted().toList()))
                .sorted().collect(Collectors.joining(" OR "));
    }
}
