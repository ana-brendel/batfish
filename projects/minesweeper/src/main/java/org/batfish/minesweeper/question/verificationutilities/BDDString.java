package org.batfish.minesweeper.question.verificationutilities;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.apache.commons.lang3.tuple.Pair;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Prefix;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;

import javax.annotation.Nonnull;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class BDDString {
  private final BDD original; // the bdd stored here is not assumed to be well-formed
  private final BDDFactory factory;
  private final BDDRoute base;

  private final int maxPrefixVarNum;

  private final BDD prefixOnlySupport;
  private final BDD prefixInfoSupport;
  private final Map<CommunityVar, Set<Integer>> communities;

  // Integer representation used for easier simplification/reduction
  /// Maps integers to the string that describes that property
  private final Map<Integer, String> integerToStringMap = new HashMap<>();
  /// Maps string description of property to the integer used to represent it
  private final Map<String, Integer> stringToIntegerMap = new HashMap<>();

  /// Returns string representation of the provided BDD
  public static String get(TransferBDD tbdd, BDD bdd) {
    if (bdd.isZero()) {
      return "False";
    } else if (bdd.isOne()) {
      return "True";
    } else {
      BDDString str = new BDDString(tbdd, bdd);
      String result = str.getString();
      return result.trim().equals("+") ? "LIMIT (Complex BDD)" : result;
    }
  }

  private BDDString(TransferBDD tbdd, BDD bdd) {
    this.original = bdd.id();
    this.factory = tbdd.getFactory();
    this.base = tbdd.getOriginalRoute();
    this.prefixOnlySupport = this.base.getPrefix().support();
    this.prefixInfoSupport = this.prefixOnlySupport.and(this.base.getPrefixLength().support());
    int[] prefixVars = prefixOnlySupport.scanSet();
    this.maxPrefixVarNum = Arrays.stream(prefixVars).max().getAsInt();

    // make the only variable corresponding to "all communities" be the one isolated for it
    this.communities = tbdd.getCommunityAtomicPredicates();
    Set<Integer> communityVars =
        this.communities.entrySet().stream()
            .filter(entry -> !entry.getKey().getRegex().equals("[^^$]*"))
            .flatMap(entry -> entry.getValue().stream())
            .collect(Collectors.toSet());
    Set<Integer> update =
        this.communities.get(CommunityVar.from("[^^$]*")).stream()
            .filter(var -> !communityVars.contains(var))
            .collect(Collectors.toSet());
    this.communities.put(CommunityVar.from("[^^$]*"), update);
    //
    // this.tbdd.getConfigAtomicPredicates().getAsPathRegexAtomicPredicates().getRegexAtomicPredicates();
  }

  /// Returns the original BDD with any variable mentioned in toRemove removed
  private static BDD dropVariables(BDD original, BDD toRemove) {
    return original.exist(toRemove.support());
  }

  /// Generates (or if it exists, find) the integer which represents the string property provided
  private Integer addStringToBank(String label) {
    if (stringToIntegerMap.containsKey(label)) {
      assert label.equals(integerToStringMap.get(stringToIntegerMap.get(label)))
          : "Stored integer and string relation is not reflexive.";
      return stringToIntegerMap.get(label);
    } else {
      int var = integerToStringMap.size() + 1;
      integerToStringMap.put(var, label);
      stringToIntegerMap.put(label, var);
      return var;
    }
  }

  /// Returns the property associated with the variable. If the variable is negative, this is
  /// associated with the negation of that property. A zero corresponds to '+' which means there is
  /// some information which we are not effectively representing.
  private String getFromStringBank(Integer var) {
    if (var < 0) {
      return "!" + this.integerToStringMap.get(-var);
    } else {
      // var = 0 corresponds to some extra BDD information not reflected accurately
      return var == 0 ? "+" : this.integerToStringMap.get(var);
    }
  }

  public static String trimRegex(String regex) {
    return regex.replaceAll("\\^", "").replaceAll("\\$", "");
  }

  /// Returns mapping of BDD to the string representation of the atomic predicates satisfied by that
  /// BDD. Currently, the only atomic predicates which are considered are communities.
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
          int varLabel = -this.addStringToBank("comm(" + trimRegex(var.getRegex()) + ")");
          strings.add(varLabel);
          break;
        } else if (assignment[v] == 1) {
          // true - community is explicitly set
          running.add(this.factory.ithVar(v));
          int varLabel = this.addStringToBank("comm(" + trimRegex(var.getRegex()) + ")");
          strings.add(varLabel);
          break;
        } else {
          // don't care - this atomic predicate is not handled
          assert assignment[v] == -1;
        }
      }
    }
    return Pair.of(this.factory.andAll(running), strings);
  }

  /// Converts byte[] corresponding to variable assignments to bdd, bdd size is limited by total
  /// variable count
  private BDD bddOfByteArr(byte[] arr) {
    Set<BDD> running = new HashSet<>();
    for (int v = 0; v < arr.length; v++) {
      if (arr[v] == 0) {
        running.add(this.factory.ithVar(v).not());
      } else if (arr[v] == 1) {
        running.add(this.factory.ithVar(v));
      } else {
        assert arr[v] == -1;
      }
    }
    return this.factory.andAll(running);
  }

  /// Return prefix range associated with a bdd.
  /// If this BDD does not represent a single prefix range, the method returns a
  /// bitstring representation of the prefix range.
  private @Nonnull String prefixOfBDD(BDD bdd) {
    BDD prefixOnlyBDD = bdd.project(this.prefixOnlySupport);
    StringBuilder result;
    // check that the BDD assigns values to some contiguous set of variables corresponding to the
    // IP address in the prefix, starting from the highest order bit, and that no other bits
    // of the IP address are set. if this is not the case, then we can't represent the BDD
    // as a single prefix range, so we return null.
    int[] prefixSupport = prefixOnlyBDD.support().scanSet();
    int minToMaxPrefixLength;
    if (prefixSupport == null || prefixSupport.length == 0) {
      minToMaxPrefixLength = 0;
    } else {
      // note: we assume the variables in prefixSupport are in increasing order,
      // which seems to be the case based on the behavior of support() and scanSet()
      minToMaxPrefixLength = this.maxPrefixVarNum - prefixSupport[0] + 1;
    }
    if (prefixSupport == null || prefixSupport.length == minToMaxPrefixLength) {
      // the BDD represents a single prefix
      Ip ip = Ip.create(this.base.getPrefix().satAssignmentToLong(prefixOnlyBDD));
      Prefix p = Prefix.create(ip, minToMaxPrefixLength);
      result = new StringBuilder(p.toString());
    } else {
      result = new StringBuilder();
      // return a bit representation of the prefix, since it does not represent a unique prefix
      for (int i = 0; i < minToMaxPrefixLength; i++) {
        BDD var = factory.ithVar(maxPrefixVarNum - i);
        String bitChar = getBitChar(prefixOnlyBDD, var);
        result.append(bitChar);
        if (i % 8 == 7 && i != minToMaxPrefixLength - 1) {
          result.append(".");
        }
      }
      result.append("/").append(minToMaxPrefixLength);
    }

    // now let's work on the length range
    BDD lenSupport = this.base.getPrefixLength().support();
    BDD lenOnlyBDD = bdd.project(lenSupport);
    // let's find the min and max lengths that satisfy the bdd
    int lower = 33;
    int upper = -1;
    BDD.BDDIterator iter = lenOnlyBDD.iterator(lenSupport);
    while (iter.hasNext()) {
      BDD assignment = iter.next();
      int length = (int) this.base.getPrefixLength().satAssignmentToLong(assignment);
      if (length < lower) {
        lower = length;
      }
      if (length > upper) {
        upper = length;
      }
    }

    // if the length range is the same as the prefix length, then we don't add the range
    // to the string representation since it is redundant
    if (lower != upper || lower != minToMaxPrefixLength) {
      // check that the BDD represents all and only the range of lengths from lower to upper,
      // inclusive; otherwise we can't represent it as a single prefix range so we return a
      // bitstring
      if (this.base.getPrefixLength().range(lower, upper).equals(lenOnlyBDD)) {
        result.append(":").append(lower).append("-").append(upper);
      } else {
        int maxLengthVar = Arrays.stream(lenSupport.scanSet()).max().getAsInt();
        for (int i = 0; i < 6; i++) {
          BDD var = factory.ithVar(maxLengthVar - i);
          String bitChar = getBitChar(prefixOnlyBDD, var);
          result.append(bitChar);
        }
      }
    }
    return result.toString();
  }

  // return a character representing whether a given bdd variable has a particular
  // required value in the given bdd
  private static String getBitChar(BDD bdd, BDD var) {
    String bitChar;
    if (!bdd.diffSat(var)) {
      bitChar = "1";
    } else if (!bdd.andSat(var)) {
      bitChar = "0";
    } else {
      bitChar = "*";
    }
    return bitChar;
  }

  /// Returns set which is disjunction over the prefixes - first BDD in pair is prefix, second is
  // remaining bdd for pass
  private Optional<Set<Pair<Pair<BDD, BDD>, Integer>>> extractPrefixes(Set<BDD> disjuncts) {
    // collect distinct prefix groups
    // mapping from remaining BDD (after pulling out the prefix) to
    // a map from the prefix BDD to the BDD representing the valid prefix lengths
    // we combine disjuncts with the same prefix bits so that we can consider their lengths together
    // when producing a string representation
    Map<BDD, Map<BDD, BDD>> prefixBDDGroups = new HashMap<>();
    for (BDD assignment : disjuncts) {
      BDD remaining = assignment.exist(this.prefixInfoSupport);
      BDD prefixAndLengthBDD = assignment.project(this.prefixInfoSupport);
      BDD prefixOnlyBDD = prefixAndLengthBDD.project(this.prefixOnlySupport);
      BDD lengthBDD = prefixAndLengthBDD.project(this.base.getPrefixLength().support());
      if (!prefixBDDGroups.containsKey(remaining)) {
        prefixBDDGroups.put(remaining, new HashMap<>());
      }
      Map<BDD, BDD> prefixToLength = prefixBDDGroups.get(remaining);
      if (!prefixToLength.containsKey(prefixOnlyBDD)) {
        prefixToLength.put(prefixOnlyBDD, lengthBDD);
      } else {
        prefixToLength.put(prefixOnlyBDD, prefixToLength.get(prefixOnlyBDD).orWith(lengthBDD));
      }
    }

    // process common prefix groups - right now, we are just checking for positive prefixes, or
    // negation
    Map<BDD, Set<Pair<Pair<BDD, String>, Boolean>>> prefixGroups = new HashMap<>();
    for (BDD remaining : prefixBDDGroups.keySet()) {
      Map<BDD, BDD> differentPrefixes = prefixBDDGroups.get(remaining);
      Set<Pair<Pair<BDD, String>, Boolean>> prefixes =
          differentPrefixes.entrySet().stream()
              .map(
                  entry -> {
                    BDD full = entry.getKey().and(entry.getValue());
                    return Pair.of(Pair.of(full, this.prefixOfBDD(full)), true);
                  })
              .collect(Collectors.toSet());

      if (prefixes.size() > 1) {
        // this branch checks if the set of prefixes is the negation of a prefix, limited to one
        BDD disjunction =
            this.factory.orAllAndFree(
                differentPrefixes.entrySet().stream()
                    .map(e -> e.getKey().and(e.getValue()))
                    .toList());
        BDD potential = disjunction.not();
        Set<Pair<BDD, String>> negated = new HashSet<>();
        BDD.AllSatIterator iterator = potential.allsat();
        while (iterator.hasNext()) {
          BDD assignment = bddOfByteArr(iterator.next());
          BDD projection = assignment.project(this.prefixInfoSupport);
          String prefix = this.prefixOfBDD(assignment);
          negated.add(Pair.of(projection, prefix));
          // only switches to the negation if there is one negated prefix
          if (negated.size() > 1) {
            break;
          }
        }
        // only switches to the negation if there is one negated prefix
        if (negated.size() == 1) {
          prefixes = Set.of(Pair.of(negated.stream().findFirst().get(), false));
        }
      }
      if (!prefixes.isEmpty()) {
        prefixGroups.put(remaining, prefixes);
      }
    }

    if (prefixGroups.isEmpty()) {
      return Optional.empty();
    } else {
      return Optional.of(
          prefixGroups.entrySet().stream()
              .flatMap(
                  entry -> {
                    BDD remaining = entry.getKey();
                    Set<Pair<Pair<BDD, String>, Boolean>> prefixes = entry.getValue();
                    if (prefixes.isEmpty()) {
                      return Stream.of(Pair.of(Pair.of(this.factory.one(), remaining), 0));
                    } else {
                      return prefixes.stream()
                          .map(
                              prefix -> {
                                Integer var =
                                    this.addStringToBank(
                                        "prefix(" + prefix.getLeft().getRight() + ")");
                                BDD prefixBDD = prefix.getLeft().getLeft();
                                return Pair.of(
                                    Pair.of(prefixBDD, remaining), prefix.getRight() ? var : -var);
                              });
                    }
                  })
              .collect(Collectors.toSet()));
    }
  }

  /// Checks remaining BDD set to see if it is a constant
  private Set<BDD> checkSetForConstant(Set<BDD> set) {
    Optional<BDD> single = set.stream().findFirst();
    if (set.size() == 1 && single.get().isOne()) {
      return new HashSet<>();
    } else {
      assert single.isEmpty() || !single.get().isZero()
          : "Expect that BDD set is empty or not a single false BDD.";
      BDD disjunction = this.factory.orAll(set);
      if (disjunction.isOne()) {
        return new HashSet<>();
      } else {
        return set;
      }
    }
  }

  /// Naive resolution algorithm (only reduces with single atoms)
  private Set<Set<Integer>> resolution(Set<Set<Integer>> clauses) {
    Set<Integer> atoms =
        clauses.stream()
            .filter(clause -> clause.size() == 1)
            .map(clause -> clause.stream().findFirst().get())
            .collect(Collectors.toSet());
    for (Integer atom : atoms) {
      // see if we can remove the negation of the atom from any of the other clauses
      if (atom != 0
          && clauses.stream()
              .anyMatch(
                  clause -> clause.size() != 1 && clause.stream().anyMatch(v -> v == -atom))) {
        // if we can remove negation of atom, filter it out and recall
        return resolution(
            clauses.stream()
                .map(
                    clause ->
                        clause.size() == 1
                            ? clause
                            : clause.stream().filter(v -> v != -atom).collect(Collectors.toSet()))
                .collect(Collectors.toSet()));
      }
    }
    // in the case that none of the atoms can work towards resolution, we terminate
    return clauses;
  }

  /* *** Main driving loop for isolating the string associated with the provided BDD ***
   *   Note: the provided BDD is original BDD projected onto the variables which we are
   *   displaying the string for - in this case, atomic predicates (communities) and prefixes.
   *
   *   If there are more than 64 satisfying assignments, we don't investigate and return a string
   *   indicating that the BDD is too complex for current analysis.
   *
   *   FUTURE IDEA: I think we might want to make the prefixes into atomic predicates and assign them their
   *   own BDD variables. This will be useful for generating interpolants and for string representation - I
   *   believe this will need to be introduced in the weakest precondition / strongest postcondition functions,
   *   most likely earlier with the creation of the TransferBDD. Larger software engineering task.
   * */
  private String driver(BDD bdd) {
    Map<BDD, Set<Integer>> bddToDisplays = new HashMap<>();
    Map<BDD, Set<BDD>> disjunctsByAtomicPredicates = new HashMap<>();
    BDD.AllSatIterator iterator = bdd.allsat();

    // STEP 1: Pull out any atomic predicates (i.e. easy to provide strings for)
    int countLimit = 64;
    while (iterator.hasNext()) {
      countLimit -= 1;
      if (countLimit == 0) {
        return "LIMIT (Complex BDD)";
      }
      // for each satisfying assignment, pull out the atomic predicates
      byte[] sat = iterator.next();
      Pair<BDD, Set<Integer>> atoms = this.fetchAtomicPredicateBDD(sat);
      BDD remaining = dropVariables(this.bddOfByteArr(sat), atoms.getLeft());

      // if we haven't seen this set of atomic predicates yet, add to maps
      if (!disjunctsByAtomicPredicates.containsKey(atoms.getLeft())) {
        assert !bddToDisplays.containsKey(atoms.getLeft())
            : "At this point, we should only have a bddToDisplay if we've added to the disjunctsByAtomicPredicates.";
        bddToDisplays.put(atoms.getLeft(), atoms.getRight());
        disjunctsByAtomicPredicates.put(atoms.getLeft(), new HashSet<>());
      }

      assert disjunctsByAtomicPredicates.containsKey(atoms.getLeft())
              && bddToDisplays.containsKey(atoms.getLeft())
          : "This BDD is not mapped in disjunctsByAtomicPredicates or bddToDisplays";

      // add this leftover BDD to the correct set of remaining disjuncts
      disjunctsByAtomicPredicates.get(atoms.getLeft()).add(remaining);
    }
    // AFTER STEP 1: disjunctsByAtomicPredicates should hold a map of Pi -> Qi1,...,Qin
    // where each Pi is a conjunction of atomic predicates and each Qij is some more complicated BDD
    // ex. provided bdd = [P1 /\ (Q11 \/ ... \/ Q1n)] \/ ... \/ [Pm /\ (Qm1 \/ ... \/ Qmn)]

    // STEP 2: Reason independently about the sets of disjuncts, specifically looking for negations
    // of prefixes
    Map<BDD, Set<BDD>> pullPrefixes = new HashMap<>();
    for (BDD aps : disjunctsByAtomicPredicates.keySet()) {
      Optional<Set<Pair<Pair<BDD, BDD>, Integer>>> pulled =
          this.extractPrefixes(disjunctsByAtomicPredicates.get(aps));
      if (pulled.isEmpty()) {
        // prefixes are either irrelevant or too complex to produce from the BDD
        pullPrefixes.put(aps, disjunctsByAtomicPredicates.get(aps));
      } else {
        Set<Pair<Pair<BDD, BDD>, Integer>> prefixDisjuncts = pulled.get();
        // for each prefix disjunct, join with the common and accumulate remaining disjuncts
        prefixDisjuncts.forEach(
            pair -> {
              BDD remaining = pair.getLeft().getRight();
              Integer prefixLabel = pair.getRight();
              BDD prefixBDD =
                  prefixLabel < 0 ? pair.getLeft().getLeft().not() : pair.getLeft().getLeft();
              // combine the prefix bdd with the existing common bdd
              BDD combined = prefixBDD.and(aps.id());
              // update the display if not included
              if (!bddToDisplays.containsKey(combined)) {
                bddToDisplays.put(combined, new HashSet<>(bddToDisplays.get(aps)));
                if (prefixLabel != 0) {
                  bddToDisplays.get(combined).add(prefixLabel);
                }
              }
              // add this disjunct to the set
              if (!pullPrefixes.containsKey(combined)) {
                pullPrefixes.put(combined, new HashSet<>());
              }
              pullPrefixes.get(combined).add(remaining);
            });
      }
    }
    // AFTER STEP 2: pullPrefixes should hold a map of Pi -> Qi1,...,Qin
    // where each Pi is a conjunction of atomic predicates with a prefix (or negation of prefix)
    // and each Qij is some more complicated BDD (same interpretation as above)

    // STEP 3: Sanity check against returning an incorrect string representation by our metric (with
    // respect to the BDD being projected onto prefixes and atomic predicates (communities))
    // TODO might want to change this to an assert to save on computations outside of testing
    if (!(this.factory.orAll(
            pullPrefixes.entrySet().stream()
                .map(
                    disjunct -> {
                      BDD common = disjunct.getKey();
                      BDD internalDisjuncts = this.factory.orAll(disjunct.getValue());
                      return common.and(internalDisjuncts);
                    })
                .collect(Collectors.toSet())))
        .equals(bdd)) {
      return "ERR (BDD String)";
    }

    // STEP 4: simplify the formula via naive resolution then translate to strings and disjoin each
    // conjunction
    return this.resolution(
            pullPrefixes.entrySet().stream()
                .map(
                    entry -> {
                      Set<Integer> predicates = bddToDisplays.get(entry.getKey());
                      if (!checkSetForConstant(entry.getValue()).isEmpty()) {
                        predicates.add(0);
                      }
                      return predicates;
                    })
                .collect(Collectors.toSet()))
        .stream()
        .map(
            clause ->
                String.join(",", clause.stream().map(this::getFromStringBank).sorted().toList()))
        .sorted()
        .collect(Collectors.joining(" OR "));
  }

  /// Invokes algorithm to generate string, only considers prefixes and communities
  private String getString() {
    BDD variablesToProjectOn = this.prefixInfoSupport.id();
    this.communities
        .values()
        .forEach(vars -> vars.forEach(v -> variablesToProjectOn.andWith(this.factory.ithVar(v))));
    BDD projection = this.original.project(variablesToProjectOn);
    return this.driver(projection);
  }
}
