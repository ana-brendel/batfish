package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;
import java.util.AbstractMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.batfish.minesweeper.bdd.TransferBDDUtils.makeRoutePairing;

public class Lightyear {
    private final TransferBDD tbdd;
    private final Map<Ip,Node> nodes;
    private final Map<Edge, RoutingPolicy> imports;
    private final Map<Edge, RoutingPolicy> exports;

    public Lightyear(TransferBDD tbdd, Map<Ip, Node> nodes, Map<Edge, RoutingPolicy> imports, Map<Edge, RoutingPolicy> exports) {
        this.tbdd = tbdd;
        this.nodes = nodes;
        this.imports = imports;
        this.exports = exports;
    }

    // this just uses bdds, unsure if this is fully correct
    private boolean completeCheck(Invariant pre, Invariant post, RoutingPolicy policy) {
        List<TransferReturn> paths;
        TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
        try {
            paths = tbdd.computePaths(policy.getStatements(), context, true);
        } catch (Exception e) {
            throw new BatfishException("Error processing policy in the Lightyear check.");
        }
        Map<Boolean, List<TransferReturn>> pathMap = paths.stream().filter(TransferReturn::getAccepted)
                .collect(Collectors.partitioningBy(tr -> tr.getOutputRoute().getUnsupported()));
        List<TransferReturn> relevantPaths = pathMap.get(false);
        relevantPaths.addAll(pathMap.get(true));
        for (TransferReturn path : relevantPaths) {
            BDD pathAnnouncements = path.getInputConstraints();
            BDDRoute outputRoute = path.getOutputRoute();
            BDD intersection = pathAnnouncements.and(pre.wellFormedBDD());
            BDDPairing pairing = makeRoutePairing(outputRoute,tbdd);
            BDD neededForOutput = post.negate().wellFormedBDD().veccompose(pairing);
            if (!intersection.and(neededForOutput).isZero()) return false;
        }
        return true;
    }

    public boolean check(Map<Location,Invariant> invariants) {
        Map<Map.Entry<Location,Location>,Boolean> checkResults = new HashMap<>();
        for (Location location : invariants.keySet()) {
            Invariant precondition = invariants.get(location);
            if (location instanceof Edge edge && nodes.containsKey(edge.getDst())) {
                assert invariants.containsKey(nodes.get(edge.getDst())) && imports.containsKey(edge);
                Invariant postcondition = invariants.get(nodes.get(edge.getDst()));
                checkResults.put(new AbstractMap.SimpleEntry<>(edge,nodes.get(edge.getDst())),
                        completeCheck(precondition,postcondition,imports.get(edge)));
            } else if (location instanceof Node node) {
                for (Location e : invariants.keySet()) {
                    if (e instanceof Edge edge && edge.isSrc(node)) {
                        assert exports.containsKey(edge);
                        Invariant postcondition = invariants.get(edge);
                        checkResults.put(new AbstractMap.SimpleEntry<>(node,edge),
                                completeCheck(precondition,postcondition,exports.get(edge)));
                    }
                }
            }
        }
        return checkResults.values().stream().allMatch(b->b);
    }
}
