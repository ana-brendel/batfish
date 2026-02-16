package org.batfish.minesweeper.bdd;

import com.google.common.annotations.VisibleForTesting;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Stream;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.BatfishException;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.question.verificationutilities.Invariant;

/**
 * Various utility methods for working with the results of the symbolic routing analysis {@link
 * org.batfish.minesweeper.bdd.TransferBDD}.
 */
public class TransferBDDUtils {

  /**
   * Produces a BDD representing the weakest precondition of (part of) a routing policy, represented
   * by a set of paths that result from symbolic routing analysis, relative to a given
   * postcondition, which is a predicate on routes. Logically, the weakest precondition is the
   * weakest predicate on input routes that ensures that they are permitted by the given set of
   * paths and yield a route that satisfies the given postcondition. This is a standard notion from
   * program verification (see Dijkstra, A Discipline of Programming, 1976).
   *
   * @param paths symbolic representation of the execution paths through a routing policy
   * @param postcondition the postcondition in some form
   * @param tbdd an object containing the state of the symbolic route analysis that produced the
   *     paths
   * @param postconditionToBDD a function that converts the postcondition and a path to a BDD
   *     representing the constraint that the path's output routes satisfy the postcondition; this
   *     function must return a new BDD object, so that we can avoid memory leaks without destroying
   *     or modifying BDDs in the caller's context
   * @return the weakest precondition as a BDD
   */
  public static <T> BDD weakestPrecondition(
      List<TransferReturn> paths,
      T postcondition,
      TransferBDD tbdd,
      BiFunction<T, TransferReturn, BDD> postconditionToBDD) {

    // collect all accepting paths
    Stream<TransferReturn> permits = paths.stream().filter(TransferReturn::getAccepted);
    // compute the weakest precondition for each path
    Stream<BDD> pathWPs =
        permits.map(path -> weakestPreconditionForPath(path, postcondition, postconditionToBDD));

    // return the disjunction of the per-path weakest preconditions
    return tbdd.getFactory().orAllAndFree(pathWPs.toList());
  }

  /**
   * Produces a BDD representing the set of input routes that are denied by the given (part of) a
   * routing policy, represented by a set of paths that result from symbolic routing analysis.
   *
   * @param paths symbolic representation of the execution paths through a routing policy
   * @param tbdd an object containing the state of the symbolic route analysis that produced the
   *     paths
   * @return a BDD representing the denied input routes
   */
  public static BDD deniedRoutes(List<TransferReturn> paths, TransferBDD tbdd) {
    Stream<TransferReturn> denies = paths.stream().filter(p -> !p.getAccepted());

    return tbdd.getFactory().orAll(denies.map(TransferReturn::getInputConstraints).toList());
  }

  /**
   * Creates a pairing from each BDD variable in the symbolic routing analysis to the corresponding
   * BDD in the given symbolic route. This is useful in particular for chaining together the results
   * of the symbolic routing analysis using {@link net.sf.javabdd.BDD#veccompose(BDDPairing)}.
   *
   * @param route the BDDRoute
   * @param tbdd the routing analysis object that produced the given route
   */
  public static BDDPairing makeRoutePairing(BDDRoute route, TransferBDD tbdd) {
    BDDFactory factory = tbdd.getFactory();
    ConfigAtomicPredicates configAPs = tbdd.getConfigAtomicPredicates();

    // create a fresh BDDRoute to pair with the given one
    BDDRoute freshRoute = new BDDRoute(factory, configAPs);
    BDDPairing pairing = factory.makePair();

    route.augmentPairing(freshRoute, pairing);

    return pairing;
  }

  /**
   * Produces a BDD representing the weakest precondition of a single path that results from
   * symbolic routing analysis, relative to a given postcondition, which is a predicate on routes.
   * Logically, the weakest precondition is the weakest predicate on input routes that ensures that
   * they are permitted by the path and yield a route that satisfies the given postcondition.
   *
   * @param path symbolic representation of an execution path through a routing policy
   * @param postcondition the postcondition in some form
   * @param postconditionToBDD a function that converts the postcondition and a path to a BDD
   *     representing the constraint that the path's output routes satisfy the postcondition; this
   *     function must return a new BDD object, so that we can avoid memory leaks without destroying
   *     or modifying BDDs in the caller's context
   * @return the weakest precondition as a BDD
   */
  @VisibleForTesting
  static <T> BDD weakestPreconditionForPath(
      TransferReturn path, T postcondition, BiFunction<T, TransferReturn, BDD> postconditionToBDD) {

    return postconditionToBDD.apply(postcondition, path).andEq(path.getInputConstraints());
  }

  /**
   * Function takes in a precondition and a path through a routing policy, and it returns the
   * strongest postcondition which can be asserted by any routes which result from the policy that
   * adhered to the precondition on entry.
   *
   * @param tbdd an object containing the state of the symbolic route analysis that produced the
   *     paths
   * @param precondition invariant assumed to hold on entry to the policy
   * @param path symbolic representation of the execution paths through a routing policy
   * @return strongest post condition as BDD for the provided path
   */
  private static BDD bddPrePathToPostBDD(TransferBDD tbdd, BDD precondition, TransferReturn path) {
    BDD inputConstraints = precondition.and(path.getInputConstraints());

    if (inputConstraints.isZero()) {
      return tbdd.getFactory().zero();
    } else {
      BDD strongest = inputConstraints.id();
      BDDPairing pairing = makeRoutePairing(path.getOutputRoute(), tbdd);

      for (int v : tbdd.getFactory().getVarOrder()) {
        BDD var = tbdd.getFactory().ithVar(v); // variable in consideration
        BDD variableSet = var.veccompose(pairing); // condition true in order for variable to be set

        // check if the variable is updated at all, if it is, then existentially quantify that
        // variable
        if (!variableSet.equals(var)) {
          strongest.existEq(var);
        }

        if (inputConstraints.imp(variableSet).isOne()) {
          strongest = strongest.and(var);
        } else if (inputConstraints.imp(variableSet.not()).isOne()) {
          strongest = strongest.and(var.not());
        } else if (!variableSet.equals(var)) {
          throw new BatfishException(
              "Strongest postcondition method currently doesn't handle variable dependent updates");
        }
      }
      return strongest;
    }
  }

  /**
   * Produces a BDD representing the strongest postcondition of (part of) a routing policy,
   * represented by a set of paths that result from symbolic routing analysis, relative to a given
   * precondition, which is a predicate on routes. Logically, the strongest postcondition is any
   * property that we know will be true after the policy is executed on a route with the provided
   * precondition. This is determined by taking any path through the policy which adheres to the
   * provided precondition and considers any modifications made.
   *
   * @param paths symbolic representation of the execution paths through a routing policy
   * @param precondition a precondition that should hold on routes considered
   * @param tbdd an object containing the state of the symbolic route analysis that produced the
   *     paths
   * @param preconditionToBDD function which takes a precondition and path that yields a BDD
   *     corresponding to the post condition on that path
   * @return strongest postcondition as a BDD
   */
  public static <T> BDD strongestPostcondition(
      List<TransferReturn> paths,
      T precondition,
      TransferBDD tbdd,
      Function<T, BDD> preconditionToBDD) {
    // collect all accepting paths
    Stream<TransferReturn> permits = paths.stream().filter(TransferReturn::getAccepted);
    // compute the strongest postcondition for each path
    Stream<BDD> pathSPs =
        permits.map(path -> bddPrePathToPostBDD(tbdd, preconditionToBDD.apply(precondition), path));
    // return the disjunction of the per-path strongest postcondition (as each are possible)
    return tbdd.getFactory().orAll(pathSPs.toList());
  }

  /**
   * IN PROGRESS - implementation for finding an interpolant between the provided formulas --
   * improvement option 1: conjoin existentially quantified pre and posts (not just pre) --
   * improvement option 2: resolution
   *
   * @param tbdd an object containing the state of the symbolic route analysis that produced the
   *     paths
   * @param p first formula (BDD) for interpolation
   * @param q second formula (BDD) for interpolation
   * @return interpolant between the two provided formulas as BDD
   */
  public static Optional<BDD> interpolate(TransferBDD tbdd, BDD p, BDD q) {
    assert p.varProfile().length == q.varProfile().length;
    Invariant p_inv = new Invariant(tbdd, p);
    Invariant q_inv = new Invariant(tbdd, q);

    // Not sure if this is necessary, for our current purposes we wouldn't want to interpolate is P
    // does not imply Q
    if (!p_inv.implies(q_inv)) {
      return Optional.empty();
    }

    // STEP 1: Simplify q by pruning disjuncts that are incompatible with p; and
    // do the same dually for p
    BDD q_pruned = simplifyRight(tbdd, p, q);
    BDD q_not = q.not();
    BDD p_not = p.not();
    BDD p_pruned = simplifyRight(tbdd, q_not, p_not).notEq();
    q_not.free();
    p_not.free();

    // STEP 2: Existentially quantify out any variables in p which do not appear in the pruned q
    // ex. P = (A \/ B) /\ C and Q = A \/ B, so P => Q and C is not in Q so we remove it from P to
    // get interpolant A \/ B
    for (int i = 0; i < p_pruned.varProfile().length; i++) {
      BDD var = tbdd.getFactory().ithVar(i);
      // we want to only keep variables that are present in both - check if either counts is zero
      if (p_pruned.varProfile()[i] == 0 || q_pruned.varProfile()[i] == 0) {
        p_pruned.existEq(var);
      }
      var.free();
    }

    // STEP 3: In the case that we keep the prefix length but have no prefix, remove length
    // variables
    // TODO This is an edge case - might be a bug on my end related to the well-formedness
    // constraint stuff, might be unnecessary
    if (!p_pruned.testsVars(tbdd.getOriginalRoute().getPrefix().support())) {
      p_pruned.existEq(tbdd.getOriginalRoute().getPrefixLength().support());
    }

    // STEP 4 ??? (tbd to address existing limitations in approach)
    //    ex. Reasoning distinctly about negations of prefixes (demonstrated in
    // InvariantTest.interpolationExactTest())
    //    ex. ...

    q_pruned.free();

    return Optional.of(p_pruned);
  }

  // Prune q to only include assignments which are satisfiable given p (hopefully scaling
  // is not issue)
  // ex. P = A /\ B and  Q = A \/ !B, then P /\ A is satisfiable but P /\ !B is unsatisfiable so we
  // simplify Q to just A
  private static BDD simplifyRight(TransferBDD tbdd, BDD p, BDD q) {
    BDD q_pruned = tbdd.getFactory().zero();
    BDD.AllSatIterator qit = q.allsat();
    while (qit.hasNext()) {
      byte[] arr = qit.next();
      Set<BDD> running = new HashSet<>();
      for (int v = 0; v < arr.length; v++) {
        if (arr[v] == 0) {
          running.add(tbdd.getFactory().ithVar(v).not());
        } else if (arr[v] == 1) {
          running.add(tbdd.getFactory().ithVar(v));
        }
      }
      BDD q_assignment = tbdd.getFactory().andAllAndFree(running);

      if (!p.and(q_assignment).isZero()) {
        q_pruned.orWith(q_assignment);
      }
    }
    return q_pruned;
  }
}
