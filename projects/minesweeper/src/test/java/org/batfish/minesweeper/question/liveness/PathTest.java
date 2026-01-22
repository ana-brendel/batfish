package org.batfish.minesweeper.question.liveness;

import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.Stack;

import static org.junit.Assert.assertEquals;

public class PathTest {
    @Before
    public void setup() throws IOException { }

    @Test
    public void develop() {
        Stack<String> s = new Stack<>();
        s.push("a");
        s.push("b");
        s.push("c");
        assertEquals("a", s.remove(0));
        assertEquals("b", s.remove(0));
    }
}

