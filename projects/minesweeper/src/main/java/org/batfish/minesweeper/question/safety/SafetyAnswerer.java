package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Setup;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.batfish.minesweeper.question.verificationutilities.Setup.buildInvariant;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_safety;
import static org.batfish.minesweeper.question.verificationutilities.Setup.nonDefaultRoute;

// Currently the question takes in a single target location-invariant pair whereas the assumptions might be a list
public final class SafetyAnswerer extends Answerer {
    private static final Logger LOGGER = LogManager.getLogger(SafetyAnswerer.class);

    private final @Nonnull Map<Location.Builder, Invariant.Builder> _targets;
    private final @Nonnull Map<Location.Builder, Invariant.Builder> _assumptions;
    private final @Nonnull Set<RegexConstraint> _communityRegexes;
    private final @Nonnull Set<RegexConstraint> _asPathRegexes;
    private final boolean _readable;
    private final boolean _refine;

    public SafetyAnswerer(SafetyQuestion question, IBatfish batfish) {
        super(question, batfish);
        _readable = question.get_readable();
        _targets = question.get_targets();
        _refine = question.get_refine();

        // this is added because the assumptions are taken as two lists with corresponding inputs
        List<Invariant.Builder> invAssumptions = question.get_assumptions().isPresent() ?
                question.get_assumptions().get().get_builders() : List.of();
        List<Location.Builder> locAssumptions = question.get_assumption_locations().isPresent() ?
                question.get_assumption_locations().get().get_builders() : List.of();
        assert invAssumptions.size() == locAssumptions.size() ;
        _assumptions = new HashMap<>();
        for (int i = 0; i < invAssumptions.size(); i++) {
            _assumptions.put(locAssumptions.get(i),invAssumptions.get(i));
        }

        _communityRegexes = new HashSet<>();
        invAssumptions.forEach(clauses -> clauses.getClauses()
                .forEach(c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints())));
        _asPathRegexes = new HashSet<>(); // not included in the NetworkClause nor Invariant class yet
        _targets.values().forEach(clauses -> clauses.getClauses()
                .forEach(c -> _communityRegexes.addAll(c.getCommunities().getRegexConstraints())));
    }

    public record Result(NetworkInfo info, boolean refinementOccurred, Map<Location, Optional<Bgpv4Route>> checks,
                         Map<Location,Invariant> targets, Refine.Result refinement) {
        /// Gather the answer element needed for a question return
        public TableAnswerElement getAnswerElement(boolean readable) {
            Map<Location,Invariant> results = refinement.refined;
            Map<Location,String> result_str = new HashMap<>(results.size());
            Map<BDD,String> cache = new HashMap<>();
            if (readable) {
                results.forEach((l, i) -> result_str.put(l, i.toString(refinementOccurred, cache)));
            } else {
                // we only get strings for the targets and assumptions, or if true or false (saves time)
                results.forEach((l, i) -> {
                    if (targets.containsKey(l) || info.getAssumptions().containsKey(l) || i.isFalse() || i.isTrue())
                        result_str.put(l, i.toString(refinementOccurred, cache));
                    else
                        result_str.put(l,"...");
                });
            }
            TableAnswerElement tae = new TableAnswerElement(metadata_safety());
            results.keySet()
                    .forEach(loc -> tae.addRow(Row.builder()
                            .put(Setup.LOCATION_COL, loc.toString())
                            .put(Setup.ASSUMPTION_COL, info.getAssumptions().containsKey(loc) ?
                                    info.getAssumptions().get(loc).toString(refinementOccurred,cache) : "-")
                            .put(Setup.TARGET_COL, targets.containsKey(loc) ?
                                    targets.get(loc).toString(refinementOccurred,cache) : "-")
                            .put(Setup.INFERRED_INVARIANTS_COL, result_str.containsKey(loc) && result_str.get(loc).isEmpty() ?
                                    "STRING OF BDD ERROR" : result_str.get(loc))
                            .put(Setup.OVERALL_VERIFICATION_COL, refinement.verified)
                            .put(Setup.LOCAL_VERIFICATION_COL, checks.containsKey(loc) ? checks.get(loc).isEmpty() : "")
                            .put(Setup.ASSUMPTION_VIOLATION_COL, checks.containsKey(loc) && checks.get(loc).isPresent()
                                    ? nonDefaultRoute(checks.get(loc).get()) : "").build()));
            return tae;
        }
    }

    public static Result run(NetworkInfo info, boolean refine, Location location, Invariant target) {
        // Set up and run the invariant inference
        Infer inference = info.toInfer();
        inference.addProperty(location,target);

        LOGGER.info("Beginning inference...");
        Infer.Result result = inference.run();
        LOGGER.info("Finished inferring weakest conditions needed for property to hold.");

        // Run the refinement of invariants, if the initial inference supports the safety condition
        Refine.Result refined;
        boolean refinementOccurred = true;
        // we only want to refine if the inference did not yield any falses, or if the refinement flag is set
        if (result.counter.isPresent() || !refine) {
            LOGGER.info("No invariant refinement.");
            refinementOccurred = false;
            refined = inference.refiner().noRefinement();
        } else {
            LOGGER.info("Beginning invariant refinement...");
            refined = inference.refiner().refine();
            LOGGER.info("Finished refining invariants.");
        }

        if (result.verified != refined.verified)
            throw new BatfishException("SafetyAnswerer.run() - Inference and refinement final verification results inconsistent.");

        return new Result(info,refinementOccurred,result.checks,Map.of(location,target),refined);
    }

    @Override
    public AnswerElement answer(NetworkSnapshot snapshot) {
        LOGGER.info("Within the answerer for verification.");

        // Gather information from the network
        SpecifierContext context = _batfish.specifierContext(snapshot);
        Map<String, Configuration> configs = context.getConfigs();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(_communityRegexes,_asPathRegexes,configs.values());
        TransferBDD tbdd = new TransferBDD(configAPs);
        NetworkInfo info = new NetworkInfo(tbdd,configs);
        _assumptions.forEach(info::addAssumption);
        LOGGER.info(info.displayNodes());

        if (_targets.isEmpty())
            return info.getAnswerElement();
        else if (_targets.size() != 1)
            throw new BatfishException("SafetyAnswerer.answer() - Expects exactly one property to verify, provided with " + _targets.size());

        Map.Entry<Location, Invariant> target = buildInvariant(info,true,_targets.entrySet().stream().findFirst().get());
        Result result = run(info,_refine,target.getKey(),target.getValue());
        LOGGER.info("Completed analysis.");

        return result.getAnswerElement(_readable);
    }
}
