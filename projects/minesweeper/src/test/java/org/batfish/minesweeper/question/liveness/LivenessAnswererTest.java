package org.batfish.minesweeper.question.liveness;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.NetworkFactory;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.RouteFilterLine;
import org.batfish.datamodel.RouteFilterList;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.Setup.nonDefaultRoute;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.junit.Assert.assertTrue;

public class LivenessAnswererTest {
    private static final NetworkFactory nf = new NetworkFactory();
    private static final String prefixStr = "10.0.0.0/8";
    private static final String BASIC_PREFIX_MATCH = "prefixMatch";

    @Before
    public void setup() throws IOException { }

    private BgpProcess getBgpProcess (Configuration config, Node node) {
        Vrf vrf = nf.vrfBuilder().setOwner(config).setName(Configuration.DEFAULT_VRF_NAME).build();
        return nf.bgpProcessBuilder().setRouterId(node.getSingleIp())
                .setEbgpAdminCost(0).setIbgpAdminCost(0).setLocalAdminCost(0)
                .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
                .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setVrf(vrf).build();
    }

    private void setUpConfigs(Map<Node, Configuration> configs, Node ... nodes) {
        for (Node node : nodes) {
            Configuration.Builder configBuilder = nf.configurationBuilder().setHostname(node.getName());
            configs.put(node, configBuilder.setConfigurationFormat(ConfigurationFormat.CISCO_IOS)
                    .setDefaultInboundAction(PERMIT).build());
        }
    }

    private Map<Node,BgpProcess> getBgpProcesses(Map<Node, Configuration> configs, Node ... nodes) {
        Map<Node,BgpProcess> processes = new HashMap<>();
        for (Node node : nodes) {
            processes.put(node,getBgpProcess(configs.get(node),node));
        }
        return processes;
    }

    private RoutingPolicy makePolicy(Configuration owner, String name, List<Statement> body) {
        return nf.routingPolicyBuilder().setOwner(owner).setName(name).setStatements(body).build();
    }

    private TestConfigConstructionUtils.Networkv2 initialExample(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE,
                                                                 Ip alphaIncoming,int variation) {
        Map<Node, Configuration> configs = new HashMap<>();

        String community = "2:2";
        String regex_community = "^" + community + "$";

        String EXTERNAL = "externalNeighbor";
        String INTERNAL = "internalNeighbor";

        String externalImport = "incomingFromOutside";
        String exportBETA2GAMMA = "exportB2C";
        String importDefault = "defaultImportPolicy";
        String exportDefault = "defaultExportPolicy";

        RouteFilterList prefixMatch = new RouteFilterList(BASIC_PREFIX_MATCH,
                ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixStr)))));

        // Set up the configs and add what features they know about
        setUpConfigs(configs,ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        includeCommunities(configs.get(ALPHANODE),regex_community);
        if (variation == 1) includeCommunities(configs.get(BETANODE),regex_community);
//        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
//        includeCommunities(configs.get(BETANODE),regex_comm_100_1,regex_comm_100_2);
//        includeCommunities(configs.get(GAMMANODE),regex_comm_100_2);

        // Create the BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        processes.get(ALPHANODE).setNeighbors(ImmutableSortedMap.of(
                alphaIncoming,getBgpActivePeerConfig(EXTERNAL,externalImport,exportDefault),
                BETANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault,exportDefault),
                DELTANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault,exportDefault)));
        processes.get(BETANODE).setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault,exportDefault),
                GAMMANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault, variation == 1 ? exportBETA2GAMMA : exportDefault)));
        processes.get(GAMMANODE).setNeighbors(ImmutableSortedMap.of(
                BETANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault,exportDefault),
                DELTANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault,exportDefault)));
        processes.get(DELTANODE).setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault,exportDefault),
                GAMMANODE.getSingleIp(),getBgpActivePeerConfig(INTERNAL,importDefault,exportDefault)));

        // Create the policies
        RoutingPolicy alphaExternalImport = makePolicy(configs.get(ALPHANODE), externalImport, addToCommunities(community));
        RoutingPolicy alphaDefaultImport = makePolicy(configs.get(ALPHANODE), importDefault, permitRoute(true));
        RoutingPolicy alphaDefaultExport = makePolicy(configs.get(ALPHANODE), exportDefault, permitRoute(true));

        RoutingPolicy betaDefaultImport = makePolicy(configs.get(BETANODE), importDefault, permitRoute(true));
        RoutingPolicy betaDefaultExport = makePolicy(configs.get(BETANODE), exportDefault, permitRoute(true));
        if (variation == 1) makePolicy(configs.get(BETANODE), exportBETA2GAMMA, clearCommunities());

        RoutingPolicy gammaDefaultImport = makePolicy(configs.get(GAMMANODE), importDefault, permitRoute(true));
        RoutingPolicy gammaDefaultExport = makePolicy(configs.get(GAMMANODE), exportDefault, permitRoute(true));

        RoutingPolicy deltaDefaultImport = makePolicy(configs.get(DELTANODE), importDefault, permitRoute(true));
        RoutingPolicy deltaDefaultExport = makePolicy(configs.get(DELTANODE), exportDefault, permitRoute(true));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(community)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(communityRegexes, Set.of(), configs.values());
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,alphaDefaultImport, List.of());
    }

    @Test
    public void initialExampleTest() {
        Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
        Node BETANODE = new Node("10.0.0.2", "betaNode");
        Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
        Node DELTANODE = new Node("10.0.0.4", "deltaNode");
        Ip incoming = Ip.parse("100.0.0.10");

        TestConfigConstructionUtils.Networkv2 net = initialExample(ALPHANODE, BETANODE, GAMMANODE, DELTANODE,incoming,0);
        NetworkInfo info = net.getInfo();

        PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));
        Invariant hasPrefix = new Invariant(net.tbdd(), Invariant.clauseBuilder().matchPrefix(BASIC_PREFIX).build(net.tbdd(), net.template()));
        info.addAssumption(new Edge(incoming,ALPHANODE.getSingleIp()),hasPrefix);

        RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("2:2")));
        Invariant target = new Invariant(net.tbdd(), Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));
        LivenessAnswerer.Result result = LivenessAnswerer.run(info,BASIC_PREFIX, GAMMANODE, target);

        String goodPathStr = result.goodPath().isPresent() ? result.goodPath().get().display() : "";

        assertTrue(result.goodPath().isPresent());
        assertTrue(result.potentialInterferences().isEmpty());
    }

    @Test
    public void initialExampleV1Test() {
        Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
        Node BETANODE = new Node("10.0.0.2", "betaNode");
        Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
        Node DELTANODE = new Node("10.0.0.4", "deltaNode");
        Ip incoming = Ip.parse("100.0.0.10");

        TestConfigConstructionUtils.Networkv2 net = initialExample(ALPHANODE, BETANODE, GAMMANODE, DELTANODE,incoming,1);
        NetworkInfo info = net.getInfo();

        PrefixSpace BASIC_PREFIX = new PrefixSpace(PrefixRange.fromString(prefixStr));
        Invariant hasPrefix = new Invariant(net.tbdd(), Invariant.clauseBuilder().matchPrefix(BASIC_PREFIX).build(net.tbdd(), net.template()));
        info.addAssumption(new Edge(incoming,ALPHANODE.getSingleIp()),hasPrefix);

        RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("2:2")));
        Invariant target = new Invariant(net.tbdd(), Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(), net.template()));
        LivenessAnswerer.Result result = LivenessAnswerer.run(info,BASIC_PREFIX, GAMMANODE, target);

        String goodPathStr = result.goodPath().isPresent() ? result.goodPath().get().display() : "";
        List<String> potentialInterferenceStr = result.potentialInterferences()
                .map(locationBgpv4RouteMap -> locationBgpv4RouteMap.entrySet().stream()
                        .map(entry -> entry.getKey() + " - " + nonDefaultRoute(entry.getValue())).toList())
                .orElseGet(List::of);

        assertTrue(result.goodPath().isPresent());
        assertTrue(result.potentialInterferences().isPresent());
    }
}
