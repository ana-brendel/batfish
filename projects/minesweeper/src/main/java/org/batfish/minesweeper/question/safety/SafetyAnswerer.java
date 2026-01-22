package org.batfish.minesweeper.question.safety;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
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

    public SafetyAnswerer(SafetyQuestion question, IBatfish batfish) {
        super(question, batfish);
        _readable = question.get_readable();
        _targets = question.get_targets();

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

    /// Gather the answer element needed for a question return
    private TableAnswerElement getAnswerElement(
            boolean refinementOccurred, Map<Location, Optional<Bgpv4Route>> checks, Refine.Result refinement, Infer verifier) {
        Map<Location,Invariant> results = refinement.refined();
        Map<Location,String> result_str = new HashMap<>(results.size());
        Map<BDD,String> cache = new HashMap<>();
        if (_readable) {
            results.forEach((l, i) -> result_str.put(l, i.toString(refinementOccurred,verifier.shortcuts, cache)));
        } else {
            // we only get strings for the targets and assumptions, or if true or false (saves time)
            results.forEach((l, i) -> {
                if (verifier.getTargets().containsKey(l) || verifier.getAssumptions().containsKey(l) || i.isFalse() || i.isTrue())
                    result_str.put(l, i.toString(refinementOccurred,verifier.shortcuts, cache));
                else
                    result_str.put(l,"...");
            });
        }
        TableAnswerElement tae = new TableAnswerElement(metadata_safety());
        results.keySet().stream().sorted()
                .forEach(loc -> tae.addRow(Row.builder()
                .put(Setup.LOCATION_COL, loc.toString())
                .put(Setup.ASSUMPTION_COL, verifier.getAssumptions().containsKey(loc) ?
                        verifier.getAssumptions().get(loc).toString(refinementOccurred,verifier.shortcuts,cache) : "-")
                .put(Setup.TARGET_COL, verifier.getTargets().containsKey(loc) ?
                        verifier.getTargets().get(loc).toString(refinementOccurred,verifier.shortcuts,cache) : "-")
                .put(Setup.INFERRED_INVARIANTS_COL, result_str.containsKey(loc) && result_str.get(loc).isEmpty() ?
                        "STRING OF BDD ERROR" : result_str.get(loc))
                .put(Setup.OVERALL_VERIFICATION_COL, refinement.verified())
                .put(Setup.LOCAL_VERIFICATION_COL, checks.containsKey(loc) ? checks.get(loc).isEmpty() : "")
                .put(Setup.ASSUMPTION_VIOLATION_COL, checks.containsKey(loc) && checks.get(loc).isPresent()
                        ? nonDefaultRoute(checks.get(loc).get()) : "").build()));
        return tae;
    }

    @Override
    public AnswerElement answer(NetworkSnapshot snapshot) {
        LOGGER.info("Within the answerer for verification.");
        SpecifierContext context = _batfish.specifierContext(snapshot);
        Map<String, Configuration> configs = context.getConfigs();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(_communityRegexes,_asPathRegexes,configs.values());
        TransferBDD tbdd = new TransferBDD(configAPs);
        Infer verifier = new Infer(tbdd,configs);
        LOGGER.info(verifier.displayNodes());
        _targets.entrySet().stream()
                .map(e -> buildInvariant(verifier,true,e))
                .forEach(e -> verifier.addProperty(e.getKey(),e.getValue()));
        _assumptions.forEach(verifier::addAssumption);
        Infer.Result result = verifier.run();
        Refine.Result refined;
        boolean refinementOccurred = true;
        // we only want to refine if the inference did not yield any falses
        if (result.counter().isPresent()) {
            refinementOccurred = false;
            refined = verifier.refiner().noRefinement();
        } else {
            refined = verifier.refiner().refine();
        }
        assert result.verified() == refined.verified();
        return getAnswerElement(refinementOccurred,result.checks(),refined,verifier);
    }
}
