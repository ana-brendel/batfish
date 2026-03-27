package org.batfish.minesweeper.question.safety;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/// Added class to isolate which edges have the violation on them, currently unused
public class ViolationAnalysis {
  private static final Logger LOGGER = LogManager.getLogger(ViolationAnalysis.class);

  private static boolean batchHasViolation(
      NetworkInfo info, List<Map.Entry<Location, Invariant>> batch) {
    Infer inference = info.toInfer();
    batch.forEach(entry -> inference.addProperty(entry.getKey(), entry.getValue()));
    Infer.Result verification = inference.run(false); // don't need to log each iteration
    return !verification.verified;
  }

  private static Set<Location> findViolations(
      NetworkInfo info, List<Map.Entry<Location, Invariant>> batch) {
    Set<Location> result = new HashSet<>();
    if (batch.isEmpty()) {
      return result;
    } else if (batch.size() == 1) {
      if (batchHasViolation(info, batch)) {
        assert batch.stream().findFirst().isPresent();
        result.add(batch.stream().findFirst().get().getKey());
      }
      return result;
    } else {
      int half = batch.size() / 2; // integer division
      List<Map.Entry<Location, Invariant>> batch1 = batch.subList(0, half);
      List<Map.Entry<Location, Invariant>> batch2 = batch.subList(half, batch.size());
      if (batchHasViolation(info, batch1)) {
        result.addAll(findViolations(info, batch1));
      }
      if (batchHasViolation(info, batch2)) {
        result.addAll(findViolations(info, batch2));
      }
      return result;
    }
  }

  public static Optional<String> run(NetworkInfo info, SafetyResult result) {
    // if there is an explicit counterexample (inferred false) then we can just report that
    if (1 < result.targets().size()
        && !result.checks().isEmpty()
        && result.inferenceCounter().isEmpty()) {
      LOGGER.info("Beginning to isolate violations with multiple targets...");
      Set<Location> violations =
          findViolations(
              info,
              result.targets().entrySet().stream().sorted(Map.Entry.comparingByKey()).toList());
      LOGGER.info("Finished violation isolation.");
      if (violations.isEmpty()) {
        return Optional.of("PROPERTY INDEPENDENTLY HOLDS AT EACH LOCATION");
      } else {
        Set<String> strings =
            violations.stream().map(info::locationStr).collect(Collectors.toSet());
        return Optional.of(
            "[ALL OTHER TARGETS INDEPENDENTLY VERIFY] INDEPENDENT VIOLATIONS AT: "
                + String.join(", ", strings));
      }
    } else {
      return Optional.empty();
    }
  }
}
