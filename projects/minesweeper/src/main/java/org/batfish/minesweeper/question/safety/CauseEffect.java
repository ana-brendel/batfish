package org.batfish.minesweeper.question.safety;

import com.google.common.collect.ImmutableList;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.batfish.minesweeper.bdd.TransferBDDUtils.makeRoutePairing;

public class CauseEffect {
    private final TransferBDD tbdd;
    private final BDD cause;
    private final BDD effect;
    private final BDDString.Shortcuts shortcuts;

    private CauseEffect(TransferBDD tbdd, BDD cause, BDD effect, BDDString.Shortcuts shortcuts) {
        this.tbdd = tbdd;
        this.cause = cause;
        this.effect = effect;
        this.shortcuts = shortcuts;
    }

    private static Optional<BDD> getEffect(TransferBDD tbdd, BDDRoute route) {
        Set<BDD> effects = new HashSet<>();
        BDDPairing pairing = makeRoutePairing(route,tbdd);

        for (int v : tbdd.getFactory().getVarOrder()) {
            BDD var = tbdd.getFactory().ithVar(v); // variable in consideration
            BDD variableSet = var.veccompose(pairing); // condition true in order for variable to be set

            if (variableSet.isOne()) {
                effects.add(var);
            } else if (variableSet.isZero()) {
                effects.add(var.not());
            } else if (!variableSet.equals(var)){
                throw new BatfishException("Strongest postcondition method currently doesn't handle variable dependent updates");
            }
        }

        return effects.isEmpty() ? Optional.empty() : Optional.of(tbdd.getFactory().andAll(effects));
    }

    public static Optional<Set<CauseEffect>> ofPolicy(TransferBDD tbdd, RoutingPolicy policy) {
        Set<CauseEffect> result = new HashSet<>();
        if (policy.getStatements().isEmpty()) {
            return Optional.empty();
        } else {
            TransferBDD.Context context = TransferBDD.Context.forPolicy(policy);
            List<TransferReturn> paths;
            BDDString.Shortcuts shortcuts = policy.getOwner() != null ?
                    BDDString.Shortcuts.ofPolicy(policy.getOwner(),policy) : null;
            try {
                paths = tbdd.computePaths(policy.getStatements(),context,true);
            } catch (Exception e) {
                String name = policy.getOwner() != null ? policy.getOwner().getHostname() : "policy owner null";
                throw new BatfishException("Unexpected error analyzing policy " + policy.getName() + " in node " + name, e);
            }
            for (TransferReturn path : paths) {
                BDD wf = path.getOutputRoute().wellFormednessConstraints(true);
                BDD pathConstraint = path.getInputConstraints();
                if (!path.getAccepted()) {
                    result.add(new CauseEffect(tbdd,pathConstraint.and(wf),tbdd.getFactory().zero(),shortcuts));
                } else {
                    Optional<BDD> modification = getEffect(tbdd,path.getOutputRoute());
                    if (!pathConstraint.isOne() && modification.isPresent()) {
                        result.add(new CauseEffect(tbdd,pathConstraint.and(wf),modification.get().and(wf),shortcuts));
                    }
                }
            }
        }
        return result.isEmpty() ? Optional.empty() : Optional.of(result);
    }

    public String toString() {
        String causeStr = (new Invariant(tbdd,cause)).toString(false,shortcuts);
        String effectStr = (new Invariant(tbdd,effect)).toString(false,shortcuts);
        return causeStr + " causes " + effectStr;
    }

    private static List<String> getPrefixesConsideredForDisplay(Configuration config) {
        ImmutableList.Builder<String> builder = ImmutableList.builder();
        config.getRouteFilterLists().values()
                .forEach(rfl -> rfl.getLines()
                        .forEach(line -> builder.add(line.getIpWildcard().toString())));
        return builder.build();
    }

    public BDD asBDD() {
        return cause.id().not().or(effect.id());
    }

}
