package org.batfish.minesweeper.question.verify;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDPairing;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;

import java.util.List;
import java.util.function.BiFunction;
import java.util.stream.Stream;

/**
 * This class includes the same functions as TransferBDDUtils class Todd will push and I plan on
 * using those, these are placeholders (makeRoutePairing isn't exact match because there were other
 * modifications to files that it depended on)
 */
public class TransferBDDUtils {

    /**
     * [EXACT COPY] Produces a BDD representing the weakest precondition of (part of) a routing policy, represented
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
     *     representing the constraint that the path's output routes satisfy the postcondition
     * @return the weakest precondition as a BDD
     */
    public static <T> BDD weakestPrecondition(
            List<TransferReturn> paths,
            T postcondition,
            TransferBDD tbdd,
            BiFunction<T, TransferReturn, BDD> postconditionToBDD) {

        // collect all accepting paths
        Stream<TransferReturn> permits = paths.stream().filter(TransferReturn::getAccepted);

        return tbdd.getFactory()
                .orAll(
                        permits
                                // for each accepting path, we conjoin its input constraints with the constraint
                                // that the output route on that path satisfies the given postcondition
                                .map(
                                        tr ->
                                                tr.getInputConstraints()
                                                        .andWith(postconditionToBDD.apply(postcondition, tr)))
                                .toList());
    }

    /**
     * [EXACT COPY] Produces a BDD representing the set of input routes that are denied by the given (part of) a
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
}
