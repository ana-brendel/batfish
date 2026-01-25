package org.batfish.minesweeper.question.liveness;

import org.batfish.datamodel.Ip;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import static org.batfish.minesweeper.question.liveness.Path.Builder.copySteps;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class PathTest {
    private final Path.Context empty_context = new Path.Context(
            new TransferBDD(new ConfigAtomicPredicates(List.of(),Set.of(),Set.of())), new HashMap<>(),new HashMap<>(),new HashMap<>());

    @Before
    public void setup() throws IOException { }

    @Test
    public void copyStepsTests() {
        Stack<Location> original = new Stack<>();
        original.push(new Edge("10.0.0.1","10.0.0.2"));
        original.push(new Node("10.0.0.2","nodeName"));
        original.push(new Edge("10.0.0.2","10.0.0.3"));
        Stack<Location> copy = copySteps(original);
        assertEquals(original,copy);
        assertEquals(original.pop(),copy.pop());
        assertEquals(original.remove(0),copy.remove(0));
        assertEquals(original.peek(),copy.peek());
    }

    @Test
    public void pathBuilderTests() {
        Node a = new Node("10.0.0.1","nodeA");
        Node b = new Node(Set.of(Ip.parse("10.0.0.2"),Ip.parse("11.0.0.2")),"nodeB");
        Node c = new Node(Set.of(Ip.parse("10.0.0.3"),Ip.parse("11.0.0.3"),Ip.parse("12.0.0.3")),"nodeC");
        Node d = new Node("10.0.0.4","nodeD");
        Edge a_b = new Edge(Ip.parse("10.0.0.1"),Ip.parse("11.0.0.2"));
        Edge b_d = new Edge(Ip.parse("10.0.0.2"),Ip.parse("10.0.0.4"));
        Edge d_c = new Edge(Ip.parse("10.0.0.4"),Ip.parse("12.0.0.3"));
        Edge c_b = new Edge(Ip.parse("11.0.0.3"),Ip.parse("10.0.0.2"));

        Path.Builder b1 = Path.builder(empty_context);
        assertTrue(b1.addToPath(c));
        assertTrue(b1.addToPath(d_c));
        assertTrue(b1.fromList(List.of(d,b_d,b,a_b,a)));

        Path.Builder b2 = Path.builder(empty_context);
        assertTrue(b2.addToPath(c));
        assertTrue(b2.addToPath(d_c));
        assertFalse(b2.fromList(List.of(d,b_d,a_b,a)));

        Path.Builder b3 = Path.builder(empty_context);
        assertTrue(b3.addToPath(a));
        assertFalse(b3.addToPath(a_b));

        Path.Builder b4 = Path.builder(empty_context);
        assertTrue(b4.fromList(List.of(c,d_c,d,b_d,b,c_b)));
        assertFalse(b4.addToPath(c));

        Path.Builder b5 = Path.builder(empty_context);
        assertFalse(b5.fromList(List.of(c,d_c,d,b,c_b)));
    }
}

