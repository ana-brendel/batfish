package org.batfish.minesweeper.question.safety;

import org.batfish.datamodel.Ip;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

public class LocationTest {
    @Before
    public void setup() throws IOException { }

    @Test
    public void nodeSanityTests() {
        Location n1 = new Node(Ip.parse("10.0.0.1"),"node1");
        Location n2 = new Node(Ip.parse("128.0.0.1"),"node2");
        Location n3 = new Node("10.0.0.1","node3");
        Node n4 = new Node("128.0.0.2","node2");
        Node n5 = new Node("128.0.0.1","node2");
        Node n6 = new Node(Ip.parse("10.0.0.1"),"node1");
        Edge edge = new Edge("128.0.0.1","128.0.0.2");
        assertEquals(n1,n3);
        assertNotEquals(n2,n4);
        assertEquals(n2,n5);
        assertEquals(Ip.parse("128.0.0.2"),n4.getSingleIp());
        assertTrue(n4.incoming(edge));
        assertTrue(n5.outgoing(edge));
        assertFalse(n6.incoming(edge));
        assertFalse(n6.outgoing(edge));
    }

    @Test
    public void edgeSanityTests() {
        Location e1 = new Edge(Ip.parse("100.110.120.1"),Ip.parse("100.111.120.1"));
        Location e2 = new Edge(Ip.parse("100.111.120.1"),Ip.parse("100.110.120.1"));
        Edge e3 = new Edge("100.110.120.1","100.111.120.1");
        Edge e4 = new Edge("100.110.120.2","100.111.120.1");
        Node n1 = new Node(Ip.parse("100.110.120.1"),"");
        Node n2 = new Node("100.111.120.1","");
        Node n3 = new Node("10.0.0.0","");
        assertEquals(e1,e3);
        assertEquals(e2,e3.flipEdge());
        assertNotEquals(e1,e4);
        assertNotEquals(e3,e4);
        assertTrue(e3.isSrc(n1));
        assertTrue(e4.isDst(n2));
        assertFalse(e4.isSrc(n3));
        assertFalse(e4.isDst(n3));
    }
}
