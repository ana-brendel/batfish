package org.batfish.minesweeper.question.reachability;

import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Setup;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_liveness;
import static org.batfish.minesweeper.question.verificationutilities.Setup.nonDefaultRoute;

public record ReachabilityResult(
    Optional<Path> goodPath,
    List<Path> badPaths,
    Optional<Map<Location, Bgpv4Route>> potentialInterferences) {

  public TableAnswerElement getAnswerElement(NetworkInfo info) {
    TableAnswerElement tae = new TableAnswerElement(metadata_liveness());

    boolean verified =
        goodPath.isPresent()
            && (potentialInterferences.isEmpty() || potentialInterferences.get().isEmpty());

    // add overall result
    tae.addRow(
        Row.builder()
            .put(Setup.RESULT_LABEL_COL, Setup.OVERALL_RESULT)
            .put(Setup.RESULT_VALUE_COL, verified ? "True" : "False")
            .build());

    // add the good route, if present
    goodPath.ifPresent(
        p ->
            tae.addRow(
                Row.builder()
                    .put(Setup.RESULT_LABEL_COL, Setup.GOOD_PATH_LABEL)
                    .put(Setup.RESULT_VALUE_COL, p.display(info))
                    .build()));

    // if no good paths are found, report back paths which fail to help diagnose problem
    assert goodPath.isPresent() || !badPaths.isEmpty();
    badPaths.forEach(
        path ->
            tae.addRow(
                Row.builder()
                    .put(Setup.RESULT_LABEL_COL, Setup.BAD_PATH_LABEL)
                    .put(Setup.RESULT_VALUE_COL, path.displayBadPath(info))
                    .build()));

    // add possible interference, if applicable
    assert badPaths.isEmpty() || potentialInterferences.isEmpty();
    potentialInterferences.ifPresent(
        interferences ->
            interferences.forEach(
                (entersAt, counter) ->
                    tae.addRow(
                        Row.builder()
                            .put(
                                Setup.RESULT_LABEL_COL,
                                Setup.SOURCE_OF_INTERFERENCE + info.locationStr(entersAt))
                            .put(Setup.RESULT_VALUE_COL, nonDefaultRoute(counter))
                            .build())));

    return tae;
  }
}
