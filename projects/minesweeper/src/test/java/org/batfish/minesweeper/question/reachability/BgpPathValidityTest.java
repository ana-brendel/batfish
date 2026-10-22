package org.batfish.minesweeper.question.reachability;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.AsExpr;
import org.batfish.datamodel.routing_policy.expr.ExplicitAs;
import org.batfish.datamodel.routing_policy.expr.LiteralAsList;
import org.batfish.datamodel.routing_policy.expr.LocalAs;
import org.batfish.datamodel.routing_policy.statement.PrependAsPath;
import org.batfish.datamodel.routing_policy.statement.Statements;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.junit.Before;
import org.junit.Test;

public class BgpPathValidityTest {
  private final NetworkFactory nf = new NetworkFactory();
  private Map<Edge, RoutingPolicy> imports;
  private Map<Edge, RoutingPolicy> exports;
  private int nextIp;

  @Before
  public void setup() {
    imports = new HashMap<>();
    exports = new HashMap<>();
    nextIp = 1;
  }

  private Ip freshIp() {
    return Ip.create(Ip.parse("10.0.0.0").asLong() + nextIp++);
  }

  /// An edge into dst, with AS info as configured at dst
  private Edge edge(
      Node src, Ip srcIp, Node dst, Ip dstIp, Long srcAs, Long dstAs, boolean allowsLocalAsIn) {
    boolean eBGP = srcAs == null || dstAs == null || !srcAs.equals(dstAs);
    Edge edge = new Edge(srcIp, dstIp, eBGP);
    if (src != null) {
      edge.setSrcNode(src);
    }
    edge.setDstNode(dst);
    dst.addIncomingNeighbor(edge);
    edge.setSessionAsInfo(srcAs, dstAs, allowsLocalAsIn);
    return edge;
  }

  /// A session between a and b, returning the edge a -> b
  private Edge link(Node a, long asA, Node b, long asB) {
    Ip aIp = freshIp();
    Ip bIp = freshIp();
    edge(b, bIp, a, aIp, asB, asA, false);
    return edge(a, aIp, b, bIp, asA, asB, false);
  }

  /// An edge from an external neighbor (no config) into node
  private Edge external(long externalAs, Node node, long nodeAs) {
    return edge(null, freshIp(), node, freshIp(), externalAs, nodeAs, false);
  }

  private RoutingPolicy prepending(AsExpr... ases) {
    Configuration owner =
        nf.configurationBuilder().setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build();
    return nf.routingPolicyBuilder()
        .setOwner(owner)
        .setStatements(
            List.of(
                new PrependAsPath(new LiteralAsList(List.of(ases))),
                Statements.ExitAccept.toStaticStatement()))
        .build();
  }

  /// Makes the node a route reflector that uses the given cluster ID on all its sessions. Call it
  /// after creating the node's sessions.
  private static void reflector(Node node, long clusterId, boolean clientToClient) {
    for (Edge in : node.getAllIncomingEdges()) {
      in.setRouteReflectionInfo(in.dstTreatsSrcAsClient(), clusterId);
    }
    node.setRouteReflectionInfo(clientToClient, Set.of(clusterId));
  }

  private static void reflector(Node node, long clusterId) {
    reflector(node, clusterId, true);
  }

  /// Makes the client a route-reflector client of the reflector
  private static void client(Node reflector, Node client) {
    Edge in = reflector.getIncomingFrom(client).orElseThrow();
    in.setRouteReflectionInfo(true, in.getDstClusterId());
  }

  private boolean valid(boolean endsAtEdge, Edge... edges) {
    return new BgpPathValidity(imports, exports).isValid(List.of(edges), endsAtEdge);
  }

  @Test
  public void ebgpChainIsValid() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    assertTrue(valid(false, external(100, a, 1), link(a, 1, b, 2), link(b, 2, c, 3)));
  }

  @Test
  public void reenteringAnAsIsInvalid() {
    // a and c are in the same AS, so c rejects a route that has passed through a
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    assertFalse(valid(false, external(100, a, 1), link(a, 1, b, 2), link(b, 2, c, 1)));
  }

  @Test
  public void reenteringAnAsWithAllowAsInIsValid() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    Edge bToC = edge(b, freshIp(), c, freshIp(), 2L, 1L, true);
    assertTrue(valid(false, external(100, a, 1), link(a, 1, b, 2), bToC));
  }

  @Test
  public void targetEdgeReceiverIsNotChecked() {
    // the route is sent to c but the target is the edge, before c's loop check
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    assertTrue(valid(true, external(100, a, 1), link(a, 1, b, 2), link(b, 2, c, 1)));
  }

  @Test
  public void externalAsIsInPath() {
    // the external neighbor's AS is prepended on the incoming edge
    Node a = new Node("a");
    Node b = new Node("b");
    assertFalse(valid(false, external(2, a, 1), link(a, 1, b, 2)));
  }

  @Test
  public void ibgpToIbgpIsInvalid() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    assertFalse(valid(false, external(100, a, 1), link(a, 1, b, 1), link(b, 1, c, 1)));
  }

  @Test
  public void ibgpToEbgpIsValid() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    assertTrue(valid(false, external(100, a, 1), link(a, 1, b, 1), link(b, 1, c, 2)));
  }

  @Test
  public void unknownAsIsNotTreatedAsIbgp() {
    // NetworkInfo marks a session whose local AS is unknown as iBGP, but its type is unknown
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    Edge aToB = new Edge(freshIp(), freshIp(), false);
    aToB.setSrcNode(a);
    aToB.setDstNode(b);
    Edge bToC = new Edge(freshIp(), freshIp(), false);
    bToC.setSrcNode(b);
    bToC.setDstNode(c);
    assertTrue(valid(false, external(100, a, 1), aToB, bToC));
  }

  @Test
  public void ibgpOriginToIbgpIsInvalid() {
    // a route from an unconfigured iBGP peer cannot be passed to another iBGP peer
    Node a = new Node("a");
    Node b = new Node("b");
    assertFalse(valid(false, external(1, a, 1), link(a, 1, b, 1)));
  }

  @Test
  public void exportPrependOfReceiverAsIsInvalid() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    Edge bToC = link(b, 2, c, 3);
    exports.put(bToC, prepending(new ExplicitAs(3L)));
    assertFalse(valid(false, external(100, a, 1), link(a, 1, b, 2), bToC));
  }

  @Test
  public void exportPrependOfLocalAsIsValid() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    Edge bToC = link(b, 2, c, 3);
    exports.put(bToC, prepending(LocalAs.instance(), LocalAs.instance()));
    assertTrue(valid(false, external(100, a, 1), link(a, 1, b, 2), bToC));
  }

  @Test
  public void importPrependAffectsLaterReceivers() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    Edge aToB = link(a, 1, b, 2);
    // b prepends 3 on import, after its own loop check, so only c rejects the route
    imports.put(aToB, prepending(new ExplicitAs(3L)));
    assertTrue(valid(false, external(100, a, 1), aToB));
    assertFalse(valid(false, external(100, a, 1), aToB, link(b, 2, c, 3)));
  }

  @Test
  public void senderAsComesFromSenderConfig() {
    // a uses local-as 7 toward b, while b's config does not name a single remote AS
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    Ip aIp = freshIp();
    Ip bIp = freshIp();
    edge(b, bIp, a, aIp, 2L, 7L, false);
    Edge aToB = edge(a, aIp, b, bIp, null, 2L, false);
    assertFalse(valid(false, external(100, a, 1), aToB, link(b, 2, c, 7)));
  }

  @Test
  public void targetFirstPathIsChecked() {
    Node a = new Node("a");
    Node b = new Node("b");
    Node c = new Node("c");
    Edge in = external(100, a, 1);
    Edge aToB = link(a, 1, b, 2);
    Edge bToC = link(b, 2, c, 1);
    BgpPathValidity validity = new BgpPathValidity(imports, exports);
    assertFalse(validity.isValid(new Location[] {c, bToC, b, aToB, a, in}));
    assertTrue(validity.isValid(new Location[] {bToC, b, aToB, a, in}));
  }

  // Route reflection: a, the reflectors, and b are in AS 1 unless stated otherwise

  @Test
  public void reflectionFromClientToNonClientIsValid() {
    Node a = new Node("a");
    Node rr = new Node("rr");
    Node b = new Node("b");
    Edge aToRr = link(a, 1, rr, 1);
    Edge rrToB = link(rr, 1, b, 1);
    reflector(rr, 1);
    client(rr, a);
    assertTrue(valid(false, external(100, a, 1), aToRr, rrToB));
  }

  @Test
  public void reflectionFromNonClientToClientIsValid() {
    Node a = new Node("a");
    Node rr = new Node("rr");
    Node b = new Node("b");
    Edge aToRr = link(a, 1, rr, 1);
    Edge rrToB = link(rr, 1, b, 1);
    reflector(rr, 1);
    client(rr, b);
    assertTrue(valid(false, external(100, a, 1), aToRr, rrToB));
  }

  @Test
  public void reflectionFromNonClientToNonClientIsInvalid() {
    Node a = new Node("a");
    Node rr = new Node("rr");
    Node b = new Node("b");
    Edge aToRr = link(a, 1, rr, 1);
    Edge rrToB = link(rr, 1, b, 1);
    reflector(rr, 1);
    assertFalse(valid(false, external(100, a, 1), aToRr, rrToB));
  }

  @Test
  public void reflectionBetweenClientsNeedsClientToClient() {
    Node a = new Node("a");
    Node rr = new Node("rr");
    Node b = new Node("b");
    Edge aToRr = link(a, 1, rr, 1);
    Edge rrToB = link(rr, 1, b, 1);
    reflector(rr, 1);
    client(rr, a);
    client(rr, b);
    assertTrue(valid(false, external(100, a, 1), aToRr, rrToB));
    reflector(rr, 1, false);
    assertFalse(valid(false, external(100, a, 1), aToRr, rrToB));
  }

  @Test
  public void reflectorsInDifferentClustersAreValid() {
    // a is a client of rr1, which is a client of rr2
    Node a = new Node("a");
    Node rr1 = new Node("rr1");
    Node rr2 = new Node("rr2");
    Node b = new Node("b");
    Edge aToRr1 = link(a, 1, rr1, 1);
    Edge rr1ToRr2 = link(rr1, 1, rr2, 1);
    Edge rr2ToB = link(rr2, 1, b, 1);
    reflector(rr1, 1);
    reflector(rr2, 2);
    client(rr1, a);
    client(rr2, rr1);
    assertTrue(valid(false, external(100, a, 1), aToRr1, rr1ToRr2, rr2ToB));
  }

  @Test
  public void reflectorsInOneClusterAreInvalid() {
    // rr2 rejects the route rr1 reflects, since rr1 adds their shared cluster ID
    Node a = new Node("a");
    Node rr1 = new Node("rr1");
    Node rr2 = new Node("rr2");
    Node b = new Node("b");
    Edge aToRr1 = link(a, 1, rr1, 1);
    Edge rr1ToRr2 = link(rr1, 1, rr2, 1);
    Edge rr2ToB = link(rr2, 1, b, 1);
    reflector(rr1, 1);
    reflector(rr2, 1);
    client(rr1, a);
    client(rr2, rr1);
    assertFalse(valid(false, external(100, a, 1), aToRr1, rr1ToRr2, rr2ToB));
    assertFalse(valid(false, external(100, a, 1), aToRr1, rr1ToRr2));
  }

  @Test
  public void targetEdgeReceiverClusterIsNotChecked() {
    // the route is sent to rr2 but the target is the edge, before rr2 checks the cluster list
    Node a = new Node("a");
    Node rr1 = new Node("rr1");
    Node rr2 = new Node("rr2");
    Edge aToRr1 = link(a, 1, rr1, 1);
    Edge rr1ToRr2 = link(rr1, 1, rr2, 1);
    reflector(rr1, 1);
    reflector(rr2, 1);
    client(rr1, a);
    assertTrue(valid(true, external(100, a, 1), aToRr1, rr1ToRr2));
  }

  @Test
  public void clusterListIsClearedByEbgp() {
    // rr1 in AS 1 and rr2 in AS 2 use the same cluster ID; the route reaches rr2 over eBGP, so
    // rr1's cluster ID is no longer in its cluster list
    Node a = new Node("a");
    Node rr1 = new Node("rr1");
    Node x = new Node("x");
    Node p = new Node("p");
    Node rr2 = new Node("rr2");
    Node q = new Node("q");
    Edge aToRr1 = link(a, 1, rr1, 1);
    Edge rr1ToX = link(rr1, 1, x, 1);
    Edge xToP = link(x, 1, p, 2);
    Edge pToRr2 = link(p, 2, rr2, 2);
    Edge rr2ToQ = link(rr2, 2, q, 2);
    reflector(rr1, 1);
    reflector(rr2, 1);
    client(rr1, a);
    client(rr2, p);
    assertTrue(valid(false, external(100, a, 1), aToRr1, rr1ToX, xToP, pToRr2, rr2ToQ));
  }
}
