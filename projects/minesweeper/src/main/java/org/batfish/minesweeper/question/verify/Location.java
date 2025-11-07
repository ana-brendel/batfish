package org.batfish.minesweeper.question.verify;

public abstract class Location {
    abstract boolean isEdge();
    abstract boolean isNode();
    abstract Location copy();
}
