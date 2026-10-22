package org.batfish.minesweeper.question.reachability;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
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
}
