package org.batfish.minesweeper.question.isolation;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.DataPlanePlugin;
import org.batfish.common.plugin.IBatfishTestAdapter;
import org.batfish.common.topology.TopologyProvider;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.RouteFilterLine;
import org.batfish.datamodel.RouteFilterList;
import org.batfish.datamodel.Topology;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.answers.Schema;
import org.batfish.datamodel.bgp.BgpTopology;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.table.Row;
import org.batfish.main.Batfish;
import org.batfish.main.BatfishTestUtils;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.NodeRecord;
import org.batfish.specifier.LocationInfo;
import org.hamcrest.Matcher;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.stream.Stream;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.datamodel.matchers.RowMatchers.hasColumn;
import static org.batfish.minesweeper.question.verificationutilities.Setup.COUNTEREXAMPLE_COL;
import static org.batfish.minesweeper.question.verificationutilities.Setup.INFERRED_INVARIANTS_COL;
import static org.batfish.minesweeper.question.verificationutilities.Setup.LOCATIONS_COL;
import static org.batfish.minesweeper.question.verificationutilities.Setup.LOCATION_RELEVANCE_COL;
import static org.batfish.minesweeper.question.verificationutilities.Setup.PROVIDED_INVARIANT_COL;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.replaceCommunities;
import static org.hamcrest.Matchers.allOf;
import static org.hamcrest.Matchers.equalTo;

public class IsolationAnswererTest {
  private static final NetworkFactory nf = new NetworkFactory();
  @Rule public TemporaryFolder _tempFolder = new TemporaryFolder();

  private static ConfigAtomicPredicates getConfigAtomicPredicates(
      Collection<Configuration> configs, Set<RegexConstraint> communityRegexes) {
    return new ConfigAtomicPredicates(
        configs.stream()
            .map(
                config -> {
                  Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                  Map.Entry<Configuration, Collection<RoutingPolicy>> entry =
                      new AbstractMap.SimpleImmutableEntry<>(config, policies);
                  return entry; // need to create variables to adhere to types
                })
            .toList(),
        communityRegexes.stream()
            .flatMap(
                rc -> {
                  String regex = rc.getRegex();
                  return switch (rc.getRegexType()) {
                    case REGEX -> ImmutableList.of(CommunityVar.from(regex)).stream();
                    case STRUCTURE_NAME -> Stream.empty();
                  };
                })
            .collect(ImmutableSet.toImmutableSet()),
        new HashSet<>()); // for AS path stuff
  }

  private BgpProcess getBgpProcess(Configuration config, NodeRecord node) {
    Vrf vrf = nf.vrfBuilder().setOwner(config).setName(Configuration.DEFAULT_VRF_NAME).build();
    return nf.bgpProcessBuilder()
        .setRouterId(node.getIp())
        .setEbgpAdminCost(0)
        .setIbgpAdminCost(0)
        .setLocalAdminCost(0)
        .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
        .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
        .setVrf(vrf)
        .build();
  }

  private void setUpConfigs(Map<NodeRecord, Configuration> configs, NodeRecord... nodes) {
    for (NodeRecord node : nodes) {
      Configuration.Builder configBuilder = nf.configurationBuilder().setHostname(node.name());
      configs.put(
          node,
          configBuilder
              .setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
              .setDefaultInboundAction(PERMIT)
              .build());
    }
  }

  private Map<NodeRecord, BgpProcess> getBgpProcesses(
      Map<NodeRecord, Configuration> configs, NodeRecord... nodes) {
    Map<NodeRecord, BgpProcess> processes = new HashMap<>();
    for (NodeRecord node : nodes) {
      processes.put(node, getBgpProcess(configs.get(node), node));
    }
    return processes;
  }

  private RoutingPolicy makePolicy(Configuration owner, String name, List<Statement> body) {
    return nf.routingPolicyBuilder().setOwner(owner).setName(name).setStatements(body).build();
  }

  private TestConfigConstructionUtils.Networkv2 network(
      Ip entry,
      Ip exit,
      Ip entry_B1,
      Ip entry_B2,
      NodeRecord NODE_A,
      NodeRecord NODE_B,
      NodeRecord NODE_C,
      String p_str) {
    Map<NodeRecord, Configuration> configs = new HashMap<>();

    String plain_comm_10 = "10:10";
    String regex_comm_10_10 = "^" + plain_comm_10 + "$";

    String PREFIX_MATCH = "prefixMatch";
    PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
    RouteFilterList prefixMatch =
        new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, p_prefix)));

    // Create configs
    setUpConfigs(configs, NODE_A, NODE_B, NODE_C);

    includeCommunities(configs.get(NODE_A), regex_comm_10_10);
    configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));
    includeCommunities(configs.get(NODE_C), regex_comm_10_10);

    // Create BGP processes
    Map<NodeRecord, BgpProcess> processes = getBgpProcesses(configs, NODE_A, NODE_B, NODE_C);

    processes
        .get(NODE_A)
        .setNeighbors(
            ImmutableSortedMap.of(
                entry,
                getBgpActivePeerConfig("outside", "outsideImport", null),
                NODE_B.getIp(),
                getBgpActivePeerConfig("internalNeighbor", null, null)));

    processes
        .get(NODE_B)
        .setNeighbors(
            ImmutableSortedMap.of(
                entry_B1,
                getBgpActivePeerConfig("external", null, null),
                entry_B2,
                getBgpActivePeerConfig("external", null, null),
                NODE_A.getIp(),
                getBgpActivePeerConfig("internalNeighbor", null, null),
                NODE_C.getIp(),
                getBgpActivePeerConfig("internalNeighbor", null, null)));

    processes
        .get(NODE_C)
        .setNeighbors(
            ImmutableSortedMap.of(
                NODE_B.getIp(),
                getBgpActivePeerConfig("internalNeighbor", null, null),
                exit,
                getBgpActivePeerConfig("outside", null, "outsideExport")));

    // Creating routing policy
    RoutingPolicy templatePolicy =
        makePolicy(
            configs.get(NODE_A),
            "outsideImport",
            ifStatement(
                checkForPrefixListMatch(PREFIX_MATCH),
                replaceCommunities(plain_comm_10),
                permitRoute(true)));

    makePolicy(
        configs.get(NODE_C),
        "outsideExport",
        ifStatement(checkForCommunity(plain_comm_10), permitRoute(false), permitRoute(true)));

    // Set up the tbdd
    Set<RegexConstraint> communityRegexes =
        ImmutableSet.<RegexConstraint>builder().add(RegexConstraint.parse(plain_comm_10)).build();
    ConfigAtomicPredicates configAPs =
        getConfigAtomicPredicates(configs.values(), communityRegexes);
    TransferBDD tbdd = new TransferBDD(configAPs);

    return new TestConfigConstructionUtils.Networkv2(tbdd, configs, templatePolicy, List.of(p_str));
  }

  @Before
  public void setup() {}

  public static final class MockBatfish extends IBatfishTestAdapter {
    private final SortedMap<String, Configuration> _baseConfigs;

    public MockBatfish(SortedMap<String, Configuration> baseConfigs) {
      _baseConfigs = ImmutableSortedMap.copyOf(baseConfigs);
    }

    @Override
    public SortedMap<String, Configuration> loadConfigurations(NetworkSnapshot snapshot) {
      if (getSnapshot().equals(snapshot)) {
        return _baseConfigs;
      }
      throw new IllegalArgumentException("Unknown snapshot: " + snapshot);
    }

    @Override
    public TopologyProvider getTopologyProvider() {
      return new TopologyProviderTestAdapter(this) {
        @Override
        public Topology getInitialLayer3Topology(NetworkSnapshot networkSnapshot) {
          return Topology.EMPTY;
        }

        @Override
        public BgpTopology getBgpTopology(NetworkSnapshot snapshot) {
          DataPlanePlugin.ComputeDataPlaneResult result =
              getDataPlanePlugin().computeDataPlane(snapshot);
          return result._topologies.getBgpTopology();
        }
      };
    }

    @Override
    public Map<org.batfish.specifier.Location, LocationInfo> getLocationInfo(
        NetworkSnapshot networkSnapshot) {
      return ImmutableMap.of();
    }
  }

  private Batfish getBatfish(SortedMap<String, Configuration> configs) throws IOException {
    return BatfishTestUtils.getBatfish(configs, _tempFolder);
  }

  /// 0 is target, 1 is assumption, 2 is intermediate
  private Matcher<Row> matchRow(
      int type, String provided, String locations, String inferred, String counter) {
    assert 0 <= type && type <= 2;
    return allOf(
        hasColumn(
            LOCATION_RELEVANCE_COL,
            equalTo(type == 0 ? "Target" : type == 1 ? "Assumption" : "Internal Location"),
            Schema.STRING),
        hasColumn(PROVIDED_INVARIANT_COL, equalTo(provided), Schema.STRING),
        hasColumn(LOCATIONS_COL, equalTo(locations), Schema.STRING),
        hasColumn(INFERRED_INVARIANTS_COL, equalTo(inferred), Schema.STRING),
        hasColumn(COUNTEREXAMPLE_COL, equalTo(counter), Schema.STRING));
  }

  @Test
  public void networkNoAssumptionsTest() {
    //    Ip entry = Ip.parse("10.10.0.0");
    //    Ip exit = Ip.parse("10.10.10.0");
    //    Ip entry_B1 = Ip.parse("100.10.0.0");
    //    Ip entry_B2 = Ip.parse("100.10.10.0");
    //    NodeRecord NODE_A_R = new NodeRecord("10.10.0.1", "node_A");
    //    NodeRecord NODE_B_R = new NodeRecord("10.10.0.2", "node_B");
    //    NodeRecord NODE_C_R = new NodeRecord("10.10.0.3", "node_C");
    //    String p_str = "4.16.0.0/16";
    //
    //    TestConfigConstructionUtils.Networkv2 net =
    //        network(entry, exit, entry_B1, entry_B2, NODE_A_R, NODE_B_R, NODE_C_R, p_str);
    //
    //    IBatfish batfish = new MockBatfish(net.configInput());
    //
    //    SafetyQuestion question =
    //        new SafetyQuestion(
    //            new Invariant.Builders(
    //                List.of(
    //                    Invariant.builder()
    //                        .addClause(
    //                            Invariant.createClause(
    //                                null,
    //                                new PrefixSpace(PrefixRange.fromString(p_str)),
    //                                null,
    //                                null,
    //                                null)))),
    //            new Location.Builders(
    //                List.of(new Location.Builder(NODE_C_R.name(), exit.toString(), null))),
    //            null,
    //            null,
    //            null,
    //            true,
    //            false);
    //    SafetyAnswerer answerer = new SafetyAnswerer(question, batfish);
    //    TableAnswerElement answer = (TableAnswerElement) answerer.answer(batfish.getSnapshot());

    // TODO figure out how to get unit test to work with topology from snapshot (need IBatfish)
    //    assertThat(
    //        answer.getRows().getData(),
    //        Matchers.contains(
    //            matchRow(
    //                0, "!prefix([4.16.0.0/16])", "node_C -> 10.10.10.0", "!prefix([4.16.0.0/16])",
    // ""),
    //            matchRow(1, "true", "10.10.0.0 -> node_A", "true", ""),
    //            matchRow(
    //                1,
    //                "true",
    //                "10.10.10.0 -> node_C, 100.10.10.0 -> node_B, 100.10.0.0 -> node_B",
    //                "!prefix(4.16.0.0/16) OR comm(10:10)",
    //                "Bgpv4Route{network=4.16.0.0/16}"),
    //            matchRow(
    //                2,
    //                "",
    //                "node_A -> node_B, node_B -> node_A, node_A (10.10.0.1), node_B -> node_C,
    // node_C -> node_B, node_B (10.10.0.2), node_C (10.10.0.3)",
    //                "!prefix(4.16.0.0/16) OR comm(10:10)",
    //                "")));
  }

  @Test
  public void networkAssumptionTest() {
    //    Ip entry = Ip.parse("10.10.0.0");
    //    Ip exit = Ip.parse("10.10.10.0");
    //    Ip entry_B1 = Ip.parse("100.10.0.0");
    //    Ip entry_B2 = Ip.parse("100.10.10.0");
    //    NodeRecord NODE_A_R = new NodeRecord("10.10.0.1", "node_A");
    //    NodeRecord NODE_B_R = new NodeRecord("10.10.0.2", "node_B");
    //    NodeRecord NODE_C_R = new NodeRecord("10.10.0.3", "node_C");
    //    String p_str = "4.16.0.0/16";
    //
    //    TestConfigConstructionUtils.Networkv2 net =
    //        network(entry, exit, entry_B1, entry_B2, NODE_A_R, NODE_B_R, NODE_C_R, p_str);
    //
    //    IBatfish batfish;
    //    try {
    //      batfish = getBatfish(net.configInput());
    //    } catch (Exception e) {
    //      throw new BatfishException(e.toString());
    //    }
    //
    //    SafetyQuestion question =
    //        new SafetyQuestion(
    //            new Invariant.Builders(
    //                List.of(
    //                    Invariant.builder()
    //                        .addClause(
    //                            Invariant.createClause(
    //                                null,
    //                                new PrefixSpace(PrefixRange.fromString(p_str)),
    //                                null,
    //                                null,
    //                                null)))),
    //            new Location.Builders(
    //                List.of(new Location.Builder(NODE_C_R.name(), exit.toString(), null))),
    //            new Location.Builders(
    //                List.of(new Location.Builder(entry.toString(), NODE_A_R.name(), null))),
    //            new Invariant.Builders(List.of(Invariant.builder())),
    //            Invariant.builder()
    //                .addClause(
    //                    Invariant.createClause(
    //                        null,
    //                        null,
    //                        new RegexConstraints(List.of(RegexConstraint.parse("10:10"))),
    //                        null,
    //                        null)),
    //            true,
    //            false);
    //    SafetyAnswerer answerer = new SafetyAnswerer(question, batfish);
    //    TableAnswerElement answer = (TableAnswerElement) answerer.answer(batfish.getSnapshot());

    // TODO figure out how to get unit test to work with topology from snapshot (need IBatfish)
    //    assertThat(
    //        answer.getRows().getData(),
    //        Matchers.contains(
    //            matchRow(
    //                0, "!prefix([4.16.0.0/16])", "node_C -> 10.10.10.0", "!prefix([4.16.0.0/16])",
    // ""),
    //            matchRow(
    //                1,
    //                "comm(10:10)",
    //                "10.10.10.0 -> node_C, 100.10.10.0 -> node_B, 100.10.0.0 -> node_B",
    //                "!prefix(4.16.0.0/16) OR comm(10:10)",
    //                ""),
    //            matchRow(1, "true", "10.10.0.0 -> node_A", "true", ""),
    //            matchRow(
    //                2,
    //                "",
    //                "node_A -> node_B, node_B -> node_A, node_A (10.10.0.1), node_B -> node_C,
    // node_C -> node_B, node_B (10.10.0.2), node_C (10.10.0.3)",
    //                "!prefix(4.16.0.0/16) OR comm(10:10)",
    //                "")));
  }
}
