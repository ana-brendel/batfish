package org.batfish.minesweeper.question.isolation;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.common.collect.ImmutableSortedMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.AddressFamilyCapabilities;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.ExplicitAs;
import org.batfish.datamodel.routing_policy.expr.LiteralAsList;
import org.batfish.datamodel.routing_policy.statement.PrependAsPath;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.Networkv2;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
import org.junit.Before;
import org.junit.Test;

/// Tests that invariant inference takes BGP's AS-path loop detection into account: a route whose
/// AS path contains the receiver's AS is dropped, so the receiver's invariant need not hold for
/// it. Each test checks the property "no route at a carries 2:2". a's import from its external
/// neighbor clears all communities, so a route with 2:2 can only reach a from another router.
public class InferLoopPreventionTest {
  private static final String PERMIT_ALL = "permitAll";
  private static final String CLEAR = "clearCommunities";
  private static final String TAG = "tag";
  private static final String TAG_AND_PREPEND = "tagAndPrepend";
  private static final String COMM = "2:2";
  private static final String PREFIX = "2.4.8.0/24";
  private static final PrefixSpace PREFIX_SPACE =
      new PrefixSpace(PrefixRange.fromString(PREFIX));

  private final NetworkFactory nf = new NetworkFactory();
  private Map<NodeRecord, Configuration> configs;
  private Map<NodeRecord, Long> ases;
  private Map<NodeRecord, Map<Ip, PeerSpec>> neighbors;
  private RoutingPolicy template;
  private int nextRouter;

  @Before
  public void setup() {
    configs = new LinkedHashMap<>();
    ases = new HashMap<>();
    neighbors = new HashMap<>();
    nextRouter = 1;
  }

  /// A configured neighbor: its AS, the import and export policies for it, whether the receiver
  /// accepts routes containing its own AS from it, and whether the sender replaces the ASes in
  /// the paths it sends it
  private record PeerSpec(
      long remoteAs,
      String importPolicy,
      String exportPolicy,
      boolean allowLocalAsIn,
      boolean replaceAses) {
    PeerSpec withExport(String policy) {
      return new PeerSpec(remoteAs, importPolicy, policy, allowLocalAsIn, replaceAses);
    }

    PeerSpec allowingLocalAsIn() {
      return new PeerSpec(remoteAs, importPolicy, exportPolicy, true, replaceAses);
    }

    PeerSpec replacingAses() {
      return new PeerSpec(remoteAs, importPolicy, exportPolicy, allowLocalAsIn, true);
    }
  }

  private NodeRecord router(String name, long as) {
    NodeRecord node = new NodeRecord("10.0.0." + nextRouter++, name);
    Configuration config =
        nf.configurationBuilder()
            .setHostname(name)
            .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
            .setDefaultInboundAction(PERMIT)
            .build();
    includeCommunities(config, "^" + COMM + "$");
    template =
        nf.routingPolicyBuilder()
            .setOwner(config)
            .setName(PERMIT_ALL)
            .setStatements(permitRoute(true))
            .build();
    policy(config, CLEAR, clearCommunities());
    policy(config, TAG, addToCommunities(COMM));
    List<Statement> tagAndPrepend = new ArrayList<>();
    // the prepended AS is the one of the first router, a
    tagAndPrepend.add(new PrependAsPath(new LiteralAsList(List.of(new ExplicitAs(1L)))));
    tagAndPrepend.addAll(addToCommunities(COMM));
    policy(config, TAG_AND_PREPEND, tagAndPrepend);
    configs.put(node, config);
    ases.put(node, as);
    neighbors.put(node, new HashMap<>());
    return node;
  }

  private void policy(Configuration owner, String name, List<Statement> statements) {
    nf.routingPolicyBuilder().setOwner(owner).setName(name).setStatements(statements).build();
  }

  /// An eBGP session between a and b that permits everything
  private void session(NodeRecord a, NodeRecord b) {
    neighbors.get(a).put(b.getIp(), permitAll(ases.get(b)));
    neighbors.get(b).put(a.getIp(), permitAll(ases.get(a)));
  }

  private static PeerSpec permitAll(long remoteAs) {
    return new PeerSpec(remoteAs, PERMIT_ALL, PERMIT_ALL, false, false);
  }

  /// A session from an external neighbor into node, whose import clears all communities
  private void external(NodeRecord node, String ip, long externalAs) {
    neighbors
        .get(node)
        .put(Ip.parse(ip), new PeerSpec(externalAs, CLEAR, PERMIT_ALL, false, false));
  }

  /// Sets the policy that sender exports to receiver with
  private void export(NodeRecord sender, NodeRecord receiver, String policy) {
    neighbors.get(sender).compute(receiver.getIp(), (ip, spec) -> spec.withExport(policy));
  }

  private Networkv2 build() {
    for (NodeRecord node : configs.keySet()) {
      Vrf vrf =
          nf.vrfBuilder()
              .setOwner(configs.get(node))
              .setName(Configuration.DEFAULT_VRF_NAME)
              .build();
      Map<Ip, BgpActivePeerConfig> peers = new HashMap<>();
      neighbors
          .get(node)
          .forEach(
              (ip, spec) ->
                  peers.put(
                      ip,
                      BgpActivePeerConfig.builder()
                          .setLocalAs(ases.get(node))
                          .setRemoteAs(spec.remoteAs())
                          .setReplaceNonLocalAsesOnExport(spec.replaceAses())
                          .setIpv4UnicastAddressFamily(
                              Ipv4UnicastAddressFamily.builder()
                                  .setAddressFamilyCapabilities(
                                      AddressFamilyCapabilities.builder()
                                          .setAllowLocalAsIn(spec.allowLocalAsIn())
                                          .build())
                                  .setImportPolicy(spec.importPolicy())
                                  .setExportPolicy(spec.exportPolicy())
                                  .build())
                          .build()));
      nf.bgpProcessBuilder()
          .setRouterId(node.getIp())
          .setEbgpAdminCost(0)
          .setIbgpAdminCost(0)
          .setLocalAdminCost(0)
          .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
          .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
          .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
          .setVrf(vrf)
          .build()
          .setNeighbors(ImmutableSortedMap.copyOf(peers));
    }
    TransferBDD tbdd =
        new TransferBDD(
            getConfigAtomicPredicates(
                Set.of(RegexConstraint.parse(COMM)), Set.of(), configs.values()));
    return new Networkv2(tbdd, configs, template, List.of());
  }

  /// Whether inference verifies that no route at node carries 2:2
  private boolean noTagAt(Networkv2 net, NodeRecord node) {
    NetworkInfo info = net.getInfo(PREFIX_SPACE);
    Infer infer = info.toInfer();
    Invariant noTag =
        new Invariant(
            net.tbdd(),
            Invariant.clauseBuilder()
                .setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!" + COMM))))
                .build(net.tbdd(), net.template()));
    infer.addProperty(node.instantiate(info), noTag);
    return infer.run().verified;
  }

  @Test
  public void loopedRouteIsExcused() {
    // b's routes all come from a, so the routes b tags on its export back to a carry a's AS
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    external(a, "100.0.0.1", 100);
    session(a, b);
    export(b, a, TAG);
    assertTrue(noTagAt(build(), a));
  }

  @Test
  public void routeFromElsewhereIsNotExcused() {
    // b also has routes from its own external neighbor, which do not carry a's AS
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    external(a, "100.0.0.1", 100);
    external(b, "100.0.0.2", 200);
    session(a, b);
    export(b, a, TAG);
    assertFalse(noTagAt(build(), a));
  }

  @Test
  public void loopThroughTwoAsesIsExcused() {
    // a, b, and c form a ring; every route at c has passed through a
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    NodeRecord c = router("c", 3);
    external(a, "100.0.0.1", 100);
    session(a, b);
    session(b, c);
    session(c, a);
    export(c, a, TAG);
    export(b, a, TAG);
    assertTrue(noTagAt(build(), a));
  }

  @Test
  public void prependOfReceiverAsIsExcused() {
    // b's routes come from its own external neighbor, but b's export to a prepends a's AS
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    external(a, "100.0.0.1", 100);
    external(b, "100.0.0.2", 200);
    session(a, b);
    export(b, a, TAG_AND_PREPEND);
    assertTrue(noTagAt(build(), a));
  }

  @Test
  public void allowAsInDisablesExcuse() {
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    external(a, "100.0.0.1", 100);
    session(a, b);
    export(b, a, TAG);
    neighbors.get(a).compute(b.getIp(), (ip, spec) -> spec.allowingLocalAsIn());
    assertFalse(noTagAt(build(), a));
  }

  @Test
  public void replacedAsesDisableExcuse() {
    // b replaces the ASes in the paths it sends a with its own, so a no longer sees its AS
    NodeRecord a = router("a", 1);
    NodeRecord b = router("b", 2);
    external(a, "100.0.0.1", 100);
    session(a, b);
    export(b, a, TAG);
    neighbors.get(b).compute(a.getIp(), (ip, spec) -> spec.replacingAses());
    assertFalse(noTagAt(build(), a));
  }
}
