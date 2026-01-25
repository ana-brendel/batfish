package org.batfish.minesweeper.question.liveness;

import net.sf.javabdd.BDD;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.question.verificationutilities.BDDString;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;

public class InterferenceCheck {
    public final BDDString.Shortcuts shortcuts;
    private final Path.Context context;

    private final PrefixSpace prefix;
    private final Location location;
    private final Invariant target;

    private final Map<Ip, Node> nodes;
    private final Map<Node,Set<Edge>> edgesByDestination;

    private final Queue<Location> working = new LinkedList<>();
    private final Map<Location, Invariant> inferred = new Hashtable<>();

    public InterferenceCheck(@Nonnull Path.Context context, BDDString.Shortcuts shortcuts,
                        @Nonnull PrefixSpace prefix, @Nonnull Location location, @Nonnull Invariant target,
                        @Nonnull Map<Ip, Node> nodes, @Nonnull Map<Node,Set<Edge>> edgesByDestination) {
        this.context = context;
        this.shortcuts = shortcuts;
        this.prefix = prefix;
        this.location = location;
        this.target = target;
        this.nodes = nodes;
        this.edgesByDestination = edgesByDestination;
    }

    private void inferenceLoop() {
        while (!working.isEmpty()) {
            Location location = working.remove();
            Invariant property = inferred.get(location);
            if (location instanceof Edge edge && nodes.containsKey(edge.getSrc())) {
                RoutingPolicy exportPolicy = context.exports().getOrDefault(edge, null);
                if (exportPolicy == null)
                    throw new BatfishException("Infer.inferenceLoop() - No export policy for: " + edge);
                Node src = nodes.get(edge.getSrc());
                Invariant existing = inferred.getOrDefault(src,Invariant.getFalse(context.tbdd()));
                Invariant wp = property.weakestPrecondition(exportPolicy,false);
                // TODO verify that disjoining here is the correct move - we want to consider any "bad route"
                Invariant updated = new Invariant(context.tbdd(),existing.wellFormedBDD().or(wp.wellFormedBDD()));
                inferred.put(src,updated);
                if (!existing.equals(updated) && !working.contains(src)) {
                    working.add(src);
                }
            } else if (location instanceof Node node) {
                for (Edge edge : edgesByDestination.get(node)) {
                    RoutingPolicy importPolicy = context.imports().getOrDefault(edge, null);
                    if (importPolicy == null)
                        throw new BatfishException("Infer.inferenceLoop() - No import policy for: " + edge);
                    Invariant existing = inferred.getOrDefault(edge,Invariant.getFalse(context.tbdd()));
                    Invariant wp = property.weakestPrecondition(importPolicy,false);
                    // TODO verify that disjoining here is the correct move - we want to consider any "bad route"
                    Invariant updated = new Invariant(context.tbdd(),existing.wellFormedBDD().or(wp.wellFormedBDD()));
                    inferred.put(edge,updated);
                    if (!existing.equals(updated) && !working.contains(edge)) {
                        working.add(edge);
                    }
                }
            }
        }
    }

    private Map<Location,Bgpv4Route> interferenceExample() {
        Map<Location,Bgpv4Route> checks = new HashMap<>();
        for (Location assumption_location : context.assumptions().keySet()) {
            if (!inferred.containsKey(assumption_location)) {
                throw new BatfishException("");
            } else {
                BDD assumption = context.assumptions().get(assumption_location).wellFormedBDD();
                BDD badRouteCondition = inferred.get(assumption_location).wellFormedBDD();
                BDD intersection = assumption.and(badRouteCondition);
                if (!intersection.isZero()) {
                    // if the intersection is not empty, then routes meeting this condition at this location might cause interference
                    BDD model = ModelGeneration.constraintsToModel(intersection, context.tbdd().getConfigAtomicPredicates());
                    Bgpv4Route counter = ModelGeneration.satAssignmentToBgpInputRoute(model, context.tbdd().getConfigAtomicPredicates());
                    checks.put(assumption_location,counter);
                }
            }
        }
        return checks;
    }

    public Optional<Map<Location,Bgpv4Route>> run() {
        inferred.clear();
        working.clear();
        Invariant condition = new Invariant(context.tbdd(),target.negate().wellFormedBDD().and(context.prefixSpaceToBDD(prefix)));
        inferred.put(location,condition);
        working.add(location.copy());
        inferenceLoop();
        Map<Location,Bgpv4Route> checks = interferenceExample();
        return checks.isEmpty() ? Optional.empty() : Optional.of(checks);
    }
}
