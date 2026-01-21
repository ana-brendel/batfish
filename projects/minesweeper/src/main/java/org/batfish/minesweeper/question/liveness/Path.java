package org.batfish.minesweeper.question.liveness;

import org.batfish.common.BatfishException;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Location;

import javax.annotation.Nonnull;

public class Path {
    private final @Nonnull Location[] steps;
    private final @Nonnull Invariant[] properties;

    public Path(Location[] steps, Invariant[] properties) {
        this.steps = steps == null ? new Location[0] : steps;
        this.properties = properties == null ? new Invariant[0] : properties;
        if (this.steps.length != this.properties.length)
            throw new BatfishException("Path.constructor - " + this.steps.length +
                    " locations on the path and " + this.properties.length + " properties provided.");
    }

//    public static class Builder {
//        private final Map<Edge, RoutingPolicy> imports;
//        private final Map<Edge, RoutingPolicy> exports;
//        private final Queue<Location> steps;
//
//    }
}
