package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
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
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.junit.Test;

import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.permitRoute;
import static org.batfish.minesweeper.question.verify.TestConfigConstructionUtils.replaceCommunities;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class VerifierTest {
    private static final NetworkFactory nf = new NetworkFactory();

    private static final String IMPORT_POLICY_NAME = "from_entering";
    private static final String EXPORT_POLICY_NAME = "to_leaving";
    private static final String NEXT_DOOR = "nextDoor";

    private static final String PREFIX_MATCH = "prefixMatch";
    private static final String prefixStr = "25.13.0.0/16";
    private static final PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefixStr)));

    private static ConfigAtomicPredicates getConfigAtomicPredicates(Collection<Configuration> configs, Set<RegexConstraint> communityRegexes) {
        return new ConfigAtomicPredicates(
                configs.stream().map(config -> {
                    Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                    Map.Entry<Configuration, Collection<RoutingPolicy>> entry = new AbstractMap.SimpleImmutableEntry<>(config, policies);
                    return entry; // need to create variables to adhere to types
                } ).toList(),
                communityRegexes.stream().flatMap(rc -> {
                    String regex = rc.getRegex();
                    return switch (rc.getRegexType()) {
                        case REGEX -> ImmutableList.of(CommunityVar.from(regex)).stream();
                        case STRUCTURE_NAME -> Stream.empty();
                    };}).collect(ImmutableSet.toImmutableSet()),
                new HashSet<>()); // for AS path stuff
    }

    private BgpProcess getBgpProcess (Configuration config, Node node) {
        Vrf vrf = nf.vrfBuilder().setOwner(config).setName(Configuration.DEFAULT_VRF_NAME).build();
        return nf.bgpProcessBuilder().setRouterId(node.getIp())
                .setEbgpAdminCost(0).setIbgpAdminCost(0).setLocalAdminCost(0)
                .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
                .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setVrf(vrf).build();
    }

    private static Map<String,Configuration> configInput(Map<Node, Configuration> configs) {
        Map<String,Configuration> result = new HashMap<>();
        for (Node node: configs.keySet()) {
            result.put(node.getName(),configs.get(node));
        }
        return result;
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

    private TestConfigConstructionUtils.Network originalExample(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE) {
        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        String plain_comm_1 = "100:1";
        String plain_comm_2 = "100:2";
        String regex_comm_100_1 = "^" + plain_comm_1 + "$";
        String regex_comm_100_2 = "^" + plain_comm_2 + "$";

        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH,
                ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixStr)))));

        // Set up the configs and add what features they know about
        setUpConfigs(configs,ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        includeCommunities(configs.get(ALPHANODE),regex_comm_100_1);
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(BETANODE),regex_comm_100_1,regex_comm_100_2);
        includeCommunities(configs.get(GAMMANODE),regex_comm_100_2);

        // Create the BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        processes.get(ALPHANODE).setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(BETANODE).setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(GAMMANODE).setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(DELTANODE).setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Create the policies
        RoutingPolicy alphaImport = makePolicy(configs.get(ALPHANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy alphaExport = makePolicy(configs.get(ALPHANODE), EXPORT_POLICY_NAME,
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(plain_comm_1),permitRoute(true)));

        RoutingPolicy betaImport = makePolicy(configs.get(BETANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy betaExport = makePolicy(configs.get(BETANODE), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_1),replaceCommunities(plain_comm_2),permitRoute(true)));

        RoutingPolicy gammaImport = makePolicy(configs.get(GAMMANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy gammaExport = makePolicy(configs.get(GAMMANODE), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_2),permitRoute(false),permitRoute(true)));

        RoutingPolicy deltaImport = makePolicy(configs.get(DELTANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy deltaExport = makePolicy(configs.get(DELTANODE), EXPORT_POLICY_NAME, permitRoute(true));

        // Store the policies
        imports.put(ALPHANODE,alphaImport);
        imports.put(BETANODE,betaImport);
        imports.put(GAMMANODE,gammaImport);
        imports.put(DELTANODE,deltaImport);

        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,deltaExport);

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_1))
                .add(RegexConstraint.parse(plain_comm_2)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Network(tbdd,configs,imports,exports);
    }

    @Test
    public void originalExampleTest() {
        Node ALPHANODE = new Node("10.0.0.1","alphaNode");
        Node BETANODE = new Node("10.0.0.2","betaNode");
        Node GAMMANODE = new Node("10.0.0.3","gammaNode");
        Node DELTANODE = new Node("10.0.0.4","deltaNode");
        TestConfigConstructionUtils.Network net = originalExample(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        Verifier verifier_1 = new Verifier(net.tbdd(),configInput(net.configs()));
        Invariant property_1 = new Invariant(net.tbdd(),
                Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(), net.imports().get(DELTANODE)));
        verifier_1.addProperty(DELTANODE,property_1).addAnchor(ALPHANODE);
        Verifier.Result result_1 = verifier_1.run();
        assertTrue(result_1.verified());

        Verifier verifier_2 = new Verifier(net.tbdd(),configInput(net.configs()));
        Invariant property_2 = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.imports().get(DELTANODE)));
        verifier_2.addProperty(DELTANODE,property_2).addAnchor(new Edge(ALPHANODE,BETANODE));
        Verifier.Result result_2 = verifier_2.run();
        assertFalse(result_2.verified());

        Verifier verifier_3 = new Verifier(net.tbdd(),configInput(net.configs()));
        RegexConstraints comm = new RegexConstraints(List.of(RegexConstraint.parse("100:2")));
        Invariant property_3 = new Invariant(net.tbdd(),Invariant.clauseBuilder().setCommunities(comm).build(net.tbdd(),net.imports().get(DELTANODE)));
        verifier_3.addProperty(DELTANODE,property_3).addAnchor(ALPHANODE);
        Verifier.Result result_3 = verifier_3.run();
        assertFalse(result_3.verified());

        Verifier verifier_4 = new Verifier(net.tbdd(),configInput(net.configs()));
        RegexConstraints comm_ = new RegexConstraints(List.of(RegexConstraint.parse("100:1"),RegexConstraint.parse("!100:2")));
        Invariant property_4 = new Invariant(net.tbdd(),Invariant.clauseBuilder().setCommunities(comm_).build(net.tbdd(),net.imports().get(DELTANODE)));
        verifier_4.addProperty(DELTANODE,property_4).addAnchor(ALPHANODE);
        Verifier.Result result_4 = verifier_4.run();
        assertFalse(result_4.verified());

        Verifier verifier_5 = new Verifier(net.tbdd(),configInput(net.configs()));
        RegexConstraints comm__ = new RegexConstraints(List.of(RegexConstraint.parse("100:1"),RegexConstraint.parse("!100:2")));
        Invariant property_5 = new Invariant(net.tbdd(),Invariant.clauseBuilder().setCommunities(comm__).build(net.tbdd(),net.imports().get(GAMMANODE)));
        verifier_5.addProperty(GAMMANODE,property_5).addAnchor(ALPHANODE);
        Verifier.Result result_5 = verifier_5.run();
        assertFalse(result_5.verified());
    }

    @Test
    public void originalExampleInvariantsAsExpectedTest() {
        Node ALPHANODE = new Node("10.0.0.10","alphaNode");
        Node BETANODE = new Node("10.0.0.20","betaNode");
        Node GAMMANODE = new Node("10.0.0.30","gammaNode");
        Node DELTANODE = new Node("10.0.0.40","deltaNode");
        TestConfigConstructionUtils.Network net = originalExample(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        Verifier verifier = new Verifier(net.tbdd(),configInput(net.configs()));
        Invariant property = new Invariant(net.tbdd(),
                Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(), net.imports().get(DELTANODE)));
        verifier.addProperty(DELTANODE,property).addAnchor(ALPHANODE);
        Verifier.Result result = verifier.run();
        Map<Location, Invariant> inferred = result.invariants();

        Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
        Invariant.ClauseBuilder match_100_1 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
        Invariant.ClauseBuilder match_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));

        Invariant.Builder not_prefix = Invariant.builder().addClause(avoidPrefix);
        Invariant.Builder prefix_implies_100_2 = Invariant.builder().addClause(avoidPrefix).addClause(match_100_2);
        Invariant.Builder prefix_implies_100_1_2 = Invariant.builder().addClause(avoidPrefix).addClause(match_100_2).addClause(match_100_1);

        // Node Invariants
        Invariant betaNode = prefix_implies_100_1_2.build(net.tbdd(),net.imports().get(BETANODE));
        Invariant gammaNode = prefix_implies_100_2.build(net.tbdd(),net.imports().get(GAMMANODE));
        Invariant deltaNode = not_prefix.build(net.tbdd(),net.imports().get(DELTANODE));

        // Edge Invariants
        Invariant alpha_beta = prefix_implies_100_1_2.build(net.tbdd(),net.exports().get(ALPHANODE));
        Invariant beta_gamma = prefix_implies_100_2.build(net.tbdd(),net.exports().get(BETANODE));
        Invariant gamma_beta = prefix_implies_100_1_2.build(net.tbdd(),net.exports().get(GAMMANODE));
        Invariant gamma_delta = not_prefix.build(net.tbdd(),net.exports().get(GAMMANODE));
        Invariant delta_gamma = prefix_implies_100_2.build(net.tbdd(),net.exports().get(DELTANODE));

        assertEquals(10,inferred.size());

        // Node Checks -- all off by one?
        assertTrue(inferred.get(ALPHANODE).isTrue());
        assertEquals(inferred.get(BETANODE),betaNode);
        assertEquals(inferred.get(GAMMANODE),gammaNode);
        assertEquals(inferred.get(DELTANODE),deltaNode);

        // Edge Checks
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),gamma_delta);
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),delta_gamma);
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),beta_gamma);
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),alpha_beta);
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),gamma_beta);
        assertTrue(inferred.get(new Edge(BETANODE,ALPHANODE)).isTrue());
    }

    private TestConfigConstructionUtils.Network faultyOriginalExample(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE,
                                                                      int faulty) {
        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        String plain_comm_1 = "100:1";
        String plain_comm_2 = "100:2";
        String plain_comm_3 = "100:3";
        String regex_comm_100_1 = "^" + plain_comm_1 + "$";
        String regex_comm_100_2 = "^" + plain_comm_2 + "$";
        String regex_comm_100_3 = "^" + plain_comm_3 + "$";

        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH,
                ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixStr)))));

        // Set up the configs and add what features they know about
        setUpConfigs(configs,ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        includeCommunities(configs.get(ALPHANODE),faulty == 4 ? regex_comm_100_3 : regex_comm_100_1);
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(BETANODE),regex_comm_100_1, faulty == 5 ? regex_comm_100_3 : regex_comm_100_2);
        includeCommunities(configs.get(GAMMANODE),faulty == 3 ? regex_comm_100_3 : regex_comm_100_2);

        // Create the BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,ALPHANODE,BETANODE,GAMMANODE,DELTANODE);

        processes.get(ALPHANODE).setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(BETANODE).setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(GAMMANODE).setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(DELTANODE).setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Create the policies
        RoutingPolicy alphaImport = makePolicy(configs.get(ALPHANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy alphaExport = makePolicy(configs.get(ALPHANODE), EXPORT_POLICY_NAME,
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),
                        replaceCommunities(faulty == 4 ? plain_comm_3 : plain_comm_1),permitRoute(true)));

        RoutingPolicy betaImport = makePolicy(configs.get(BETANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy betaExport;
        if (faulty == 2) {
            betaExport = makePolicy(configs.get(BETANODE), EXPORT_POLICY_NAME, permitRoute(true));
        } else {
            betaExport = makePolicy(configs.get(BETANODE), EXPORT_POLICY_NAME,
                    ifStatement(checkForCommunity(plain_comm_1),
                            replaceCommunities(faulty == 5 ? plain_comm_3 : plain_comm_2),permitRoute(true)));
        }

        RoutingPolicy gammaImport = makePolicy(configs.get(GAMMANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy gammaExport;
        if (faulty == 3) {
            gammaExport = makePolicy(configs.get(GAMMANODE), EXPORT_POLICY_NAME,
                    ifStatement(checkForCommunity(plain_comm_3),permitRoute(false),permitRoute(true)));
        } else {
            gammaExport = makePolicy(configs.get(GAMMANODE), EXPORT_POLICY_NAME,
                    ifStatement(checkForCommunity(plain_comm_2),permitRoute(faulty == 1),permitRoute(faulty != 1)));
        }

        RoutingPolicy deltaImport = makePolicy(configs.get(DELTANODE), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy deltaExport = makePolicy(configs.get(DELTANODE), EXPORT_POLICY_NAME, permitRoute(true));

        // Store the policies
        imports.put(ALPHANODE,alphaImport);
        imports.put(BETANODE,betaImport);
        imports.put(GAMMANODE,gammaImport);
        imports.put(DELTANODE,deltaImport);

        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,deltaExport);

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_1))
                .add(RegexConstraint.parse(plain_comm_2))
                .add(RegexConstraint.parse(plain_comm_3)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Network(tbdd,configs,imports,exports);
    }
    @Test
    public void faultyOriginalExampleTest() {
        Node ALPHANODE = new Node("10.0.0.11", "alphaNode");
        Node BETANODE = new Node("10.0.0.22", "betaNode");
        Node GAMMANODE = new Node("10.0.0.33", "gammaNode");
        Node DELTANODE = new Node("10.0.0.44", "deltaNode");
        Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);

        for (int i = 1; i <= 5; i++) {
            TestConfigConstructionUtils.Network net = faultyOriginalExample(ALPHANODE, BETANODE, GAMMANODE, DELTANODE,i);
            Invariant property = new Invariant(net.tbdd(), Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(), net.imports().get(DELTANODE)));
            Invariant not_prefix = Invariant.builder().addClause(avoidPrefix).build(net.tbdd(), net.imports().get(ALPHANODE));
            Verifier verifier = new Verifier(net.tbdd(), configInput(net.configs()));
            verifier.addProperty(DELTANODE, property).addAnchor(ALPHANODE);
            Verifier.Result result = verifier.run();
            assertFalse(result.verified());
            assertEquals(result.invariants().get(DELTANODE), not_prefix);
            //Map<Location,String> pp = result.weakDisplay(ImmutableList.of(prefixStr));
        }
    }

    private TestConfigConstructionUtils.Network meshNetworkExample(Node A1, Node B1, Node G1, Node D1,
                                                                   Node A2, Node B2, Node G2, Node D2, int faulty) {
        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        String plain_comm_1 = "100:1";
        String plain_comm_2 = "100:2";
        String plain_comm_3 = "100:3";
        String regex_comm_100_1 = "^" + plain_comm_1 + "$";
        String regex_comm_100_2 = "^" + plain_comm_2 + "$";
        String regex_comm_100_3 = "^" + plain_comm_3 + "$";

        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH,
                ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse(prefixStr)))));

        // Set up the configs and add what features they know about
        setUpConfigs(configs,A1,B1,G1,D1,A2,B2,G2,D2);

        includeCommunities(configs.get(A1),regex_comm_100_1);
        configs.get(A1).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(B1),regex_comm_100_1,regex_comm_100_2);
        includeCommunities(configs.get(G1),regex_comm_100_2);

        includeCommunities(configs.get(A2),faulty == 3 ? regex_comm_100_3 : regex_comm_100_1);
        configs.get(A2).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(B2),regex_comm_100_1,faulty == 2 ? regex_comm_100_3 : regex_comm_100_2);
        includeCommunities(configs.get(G2),faulty == 3 ? regex_comm_100_1 :regex_comm_100_2);

        // Create the BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,A1,B1,G1,D1,A2,B2,G2,D2);

        processes.get(A1).setNeighbors(ImmutableSortedMap.of(
                B1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                B2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(A2).setNeighbors(ImmutableSortedMap.of(
                B1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                B2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(B1).setNeighbors(ImmutableSortedMap.of(
                A1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                A2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                G1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                G2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(B2).setNeighbors(ImmutableSortedMap.of(
                A1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                A2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                G1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                G2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(G1).setNeighbors(ImmutableSortedMap.of(
                B1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                B2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                D1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                D2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(G2).setNeighbors(ImmutableSortedMap.of(
                B1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                B2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                D1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                D2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(D1).setNeighbors(ImmutableSortedMap.of(
                G1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                G2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(D2).setNeighbors(ImmutableSortedMap.of(
                G1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                G2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Create the policies
        RoutingPolicy a1_Import = makePolicy(configs.get(A1), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy a1_Export = makePolicy(configs.get(A1), EXPORT_POLICY_NAME,
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(plain_comm_1),permitRoute(true)));

        RoutingPolicy a2_Import = makePolicy(configs.get(A2), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy a2_Export = makePolicy(configs.get(A2), EXPORT_POLICY_NAME,
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(faulty == 3 ? plain_comm_3 : plain_comm_1),permitRoute(true)));

        RoutingPolicy b1_Import = makePolicy(configs.get(B1), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy b1_Export = makePolicy(configs.get(B1), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_1),replaceCommunities(plain_comm_2),permitRoute(true)));

        RoutingPolicy b2_Import = makePolicy(configs.get(B2), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy b2_Export = makePolicy(configs.get(B2), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_1),
                        replaceCommunities(faulty == 2 ? plain_comm_3 : plain_comm_2),permitRoute(true)));

        RoutingPolicy g1_Import = makePolicy(configs.get(G1), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy g1_Export = makePolicy(configs.get(G1), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_2),permitRoute(false),permitRoute(true)));

        RoutingPolicy g2_Import = makePolicy(configs.get(G2), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy g2_Export = makePolicy(configs.get(G2), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(faulty == 3 ? plain_comm_1 : plain_comm_2),permitRoute(false),permitRoute(true)));

        RoutingPolicy d1_Import = makePolicy(configs.get(D1), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy d1_Export = makePolicy(configs.get(D1), EXPORT_POLICY_NAME, permitRoute(true));

        RoutingPolicy d2_Import = makePolicy(configs.get(D2), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy d2_Export = makePolicy(configs.get(D2), EXPORT_POLICY_NAME, permitRoute(true));

        // Store the policies
        imports.put(A1,a1_Import);
        imports.put(A2,a2_Import);
        imports.put(B1,b1_Import);
        imports.put(B2,b2_Import);
        imports.put(G1,g1_Import);
        imports.put(G2,g2_Import);
        imports.put(D1,d1_Import);
        imports.put(D2,d2_Import);

        exports.put(A1,a1_Export);
        exports.put(A2,a2_Export);
        exports.put(B1,b1_Export);
        exports.put(B2,b2_Export);
        exports.put(G1,g1_Export);
        exports.put(G2,g2_Export);
        exports.put(D1,d1_Export);
        exports.put(D2,d2_Export);

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_1))
                .add(RegexConstraint.parse(plain_comm_2))
                .add(RegexConstraint.parse(plain_comm_3)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Network(tbdd,configs,imports,exports);
    }

    @Test
    public void meshNetworkTest() {
        Node A1 = new Node("100.0.0.11", "a1Node");
        Node B1 = new Node("100.0.0.22", "b1Node");
        Node G1 = new Node("100.0.0.33", "g1Node");
        Node D1 = new Node("100.0.0.44", "d1Node");
        Node A2 = new Node("101.0.0.11", "a2Node");
        Node B2 = new Node("101.0.0.22", "b2Node");
        Node G2 = new Node("101.0.0.33", "g2Node");
        Node D2 = new Node("101.0.0.44", "d2Node");
        Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
        Invariant.ClauseBuilder match_100_1 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
        Invariant.ClauseBuilder match_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));

        TestConfigConstructionUtils.Network net_0 = meshNetworkExample(A1,B1,G1,D1,A2,B2,G2,D2,0);
        Invariant property_0 = new Invariant(net_0.tbdd(), Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net_0.tbdd(), net_0.imports().get(D1)));
        Verifier verifier_0 = new Verifier(net_0.tbdd(), configInput(net_0.configs()));
        verifier_0.addProperty(D1, property_0).addProperty(D2, property_0).addAnchor(A1).addAnchor(A2);
        Verifier.Result result_0 = verifier_0.run();
        assertTrue(result_0.verified());
        //Map<Location,String> pp = result.weakDisplay(ImmutableList.of(prefixStr));

        TestConfigConstructionUtils.Network net_1 = meshNetworkExample(A1,B1,G1,D1,A2,B2,G2,D2,1);
        Invariant property_1 = new Invariant(net_1.tbdd(), Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net_1.tbdd(), net_1.imports().get(D1)));
        Verifier verifier_1 = new Verifier(net_1.tbdd(), configInput(net_1.configs()));
        verifier_1.addProperty(D1, property_1).addAnchor(A1).addAnchor(A2);
        Verifier.Result result_1 = verifier_1.run();
        assertTrue(result_1.verified());
        //Map<Location,String> pp = result.weakDisplay(ImmutableList.of(prefixStr));

        TestConfigConstructionUtils.Network net_2 = meshNetworkExample(A1,B1,G1,D1,A2,B2,G2,D2,2);
        Invariant property_2 = new Invariant(net_2.tbdd(), Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net_2.tbdd(), net_2.imports().get(D1)));
        Invariant not_prefix_2 = Invariant.builder().addClause(avoidPrefix).build(net_2.tbdd(), net_2.imports().get(A1));
        Verifier verifier_2 = new Verifier(net_2.tbdd(), configInput(net_2.configs()));
        verifier_2.addProperty(D1, property_2).addProperty(D2, property_2).addAnchor(A1).addAnchor(A2);
        Verifier.Result result_2 = verifier_2.run();
        assertFalse(result_2.verified());
        assertEquals(result_2.invariants().get(A1), not_prefix_2);
        assertEquals(result_2.invariants().get(A2), not_prefix_2);
        //Map<Location,String> pp = result.weakDisplay(ImmutableList.of(prefixStr));

        TestConfigConstructionUtils.Network net_3 = meshNetworkExample(A1,B1,G1,D1,A2,B2,G2,D2,3);
        Invariant property_3 = new Invariant(net_3.tbdd(), Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net_3.tbdd(), net_3.imports().get(D1)));
        Invariant not_prefix_3 = Invariant.builder().addClause(avoidPrefix).build(net_3.tbdd(), net_3.imports().get(A1));
        Verifier verifier_3 = new Verifier(net_3.tbdd(), configInput(net_3.configs()));
        verifier_3.addProperty(D1, property_3).addProperty(D2, property_3).addAnchor(A1).addAnchor(A2);
        Verifier.Result result_3 = verifier_3.run();
        assertFalse(result_3.verified());
        assertEquals(result_3.invariants().get(A1), not_prefix_3);
        assertEquals(result_3.invariants().get(A2), not_prefix_3);
        //Map<Location,String> pp = result.weakDisplay(ImmutableList.of(prefixStr));

        TestConfigConstructionUtils.Network net_4 = meshNetworkExample(A1,B1,G1,D1,A2,B2,G2,D2,0);
        Invariant property_4 = new Invariant(net_4.tbdd(), Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net_4.tbdd(), net_4.imports().get(D1)));
        Invariant property_alt = new Invariant(net_4.tbdd(), Invariant.clauseBuilder().matchPrefix(PREFIX).build(net_4.tbdd(), net_4.imports().get(D1)));
        Invariant expected = Invariant.builder().addClause(Invariant.clauseBuilder().matchPrefix(PREFIX)).addClause(match_100_1).addClause(match_100_2).build(net_4.tbdd(), net_4.imports().get(A1));
        Verifier verifier_4 = new Verifier(net_4.tbdd(), configInput(net_4.configs()));
        verifier_4.addProperty(D1, property_4).addProperty(D2, property_alt).addAnchor(A1).addAnchor(A2);
        Verifier.Result result_4 = verifier_4.run();
        assertFalse(result_4.verified());
        Map<Location,String> pp = result_4.weakDisplay(ImmutableList.of(prefixStr));
        assertEquals(result_4.invariants().get(A1), expected);
        assertEquals(result_4.invariants().get(A2), expected);

    }

    private TestConfigConstructionUtils.Network threeProngedNetwork(Node a0, Node b0, Node c0, Node node1,
                                                                        Node node2, Node node3, Node node4, int faulty) {
        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        String plain_comm_1_10 = "1:10";
        String plain_comm_1_20 = "1:20";
        String plain_comm_1_30 = "1:30";
        String plain_comm_10_10 = "10:10";
        String plain_comm_10_20 = "10:20";
        String plain_comm_10_30 = "10:30";
        String plain_comm_20_10 = "20:10";
        String plain_comm_20_20 = "20:20";
        String plain_comm_20_30 = "20:30";
        String regex_comm_1_10 = "^" + plain_comm_1_10 + "$";
        String regex_comm_1_20 = "^" + plain_comm_1_20 + "$";
        String regex_comm_1_30 = "^" + plain_comm_1_30 + "$";
        String regex_comm_10_10 = "^" + plain_comm_10_10 + "$";
        String regex_comm_10_20 = "^" + plain_comm_10_20 + "$";
        String regex_comm_10_30 = "^" + plain_comm_10_30 + "$";
        String regex_comm_20_10 = "^" + plain_comm_20_10 + "$";
        String regex_comm_20_20 = "^" + plain_comm_20_20 + "$";
        String regex_comm_20_30 = "^" + plain_comm_20_30 + "$";

        setUpConfigs(configs,a0,b0,c0,node1,node2,node3,node4);

        includeCommunities(configs.get(a0),regex_comm_1_10);
        includeCommunities(configs.get(b0),regex_comm_1_20);
        includeCommunities(configs.get(c0),regex_comm_1_30);

        includeCommunities(configs.get(node1),regex_comm_1_10,regex_comm_1_20,regex_comm_1_30,
                regex_comm_10_10,regex_comm_10_20,regex_comm_10_30);
        includeCommunities(configs.get(node2),regex_comm_1_10,regex_comm_1_20,regex_comm_1_30,
                regex_comm_20_10,regex_comm_20_20,regex_comm_20_30);

        includeCommunities(configs.get(node3),regex_comm_10_10,regex_comm_10_30, regex_comm_20_10,regex_comm_20_30);

        Map<Node,BgpProcess> processes = getBgpProcesses(configs,a0,b0,c0,node1,node2,node3,node4);

        processes.get(a0).setNeighbors(ImmutableSortedMap.of(
                node1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                node2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(b0).setNeighbors(ImmutableSortedMap.of(
                node1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                node2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(c0).setNeighbors(ImmutableSortedMap.of(
                node1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                node2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(node1).setNeighbors(ImmutableSortedMap.of(
                a0.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                b0.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                c0.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                node3.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(node2).setNeighbors(ImmutableSortedMap.of(
                a0.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                b0.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                c0.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                node3.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(node3).setNeighbors(ImmutableSortedMap.of(
                node1.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                node2.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                node4.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(node4).setNeighbors(ImmutableSortedMap.of(
                node3.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        RoutingPolicy a0_Import = makePolicy(configs.get(a0), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy a0_Export = makePolicy(configs.get(a0), EXPORT_POLICY_NAME,replaceCommunities(plain_comm_1_10));
        RoutingPolicy b0_Import = makePolicy(configs.get(b0), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy b0_Export = makePolicy(configs.get(b0), EXPORT_POLICY_NAME,replaceCommunities(plain_comm_1_20));
        RoutingPolicy c0_Import = makePolicy(configs.get(c0), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy c0_Export = makePolicy(configs.get(c0), EXPORT_POLICY_NAME,replaceCommunities(plain_comm_1_30));

        RoutingPolicy node1_Import = makePolicy(configs.get(node1), IMPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_1_10),addToCommunities(plain_comm_10_10),
                        ifStatement(checkForCommunity(plain_comm_1_20),addToCommunities(plain_comm_10_20),
                                faulty == 2 ? permitRoute(true) :
                                ifStatement(checkForCommunity(plain_comm_1_30),addToCommunities(plain_comm_10_30),
                                permitRoute(true)))));
        RoutingPolicy node1_Export = makePolicy(configs.get(node1), EXPORT_POLICY_NAME, permitRoute(true));

        RoutingPolicy node2_Import = makePolicy(configs.get(node2), IMPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_1_10),addToCommunities(plain_comm_20_10),
                        ifStatement(checkForCommunity(plain_comm_1_20),addToCommunities(plain_comm_20_20),
                                ifStatement(checkForCommunity(plain_comm_1_30),addToCommunities(plain_comm_20_30),
                                        permitRoute(true)))));
        RoutingPolicy node2_Export = makePolicy(configs.get(node2), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_20_10),permitRoute(true),
                        ifStatement(checkForCommunity(plain_comm_20_30),permitRoute(true),permitRoute(false))));

        RoutingPolicy node3_Import = makePolicy(configs.get(node3), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node3_Export = makePolicy(configs.get(node3), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_10_10),permitRoute(false),
                        ifStatement(checkForCommunity(plain_comm_10_30),permitRoute(faulty == 1),
                                ifStatement(checkForCommunity(plain_comm_20_10),permitRoute(false),
                                        ifStatement(checkForCommunity(plain_comm_20_30),permitRoute(false),permitRoute(true))))));

        RoutingPolicy node4_Import = makePolicy(configs.get(node4), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node4_Export = makePolicy(configs.get(node4), EXPORT_POLICY_NAME, permitRoute(true));

        imports.put(a0,a0_Import);
        imports.put(b0,b0_Import);
        imports.put(c0,c0_Import);
        imports.put(node1,node1_Import);
        imports.put(node2,node2_Import);
        imports.put(node3,node3_Import);
        imports.put(node4,node4_Import);

        exports.put(a0,a0_Export);
        exports.put(b0,b0_Export);
        exports.put(c0,c0_Export);
        exports.put(node1,node1_Export);
        exports.put(node2,node2_Export);
        exports.put(node3,node3_Export);
        exports.put(node4,node4_Export);

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_1_10))
                .add(RegexConstraint.parse(plain_comm_1_20))
                .add(RegexConstraint.parse(plain_comm_1_30))
                .add(RegexConstraint.parse(plain_comm_10_10))
                .add(RegexConstraint.parse(plain_comm_10_20))
                .add(RegexConstraint.parse(plain_comm_10_30))
                .add(RegexConstraint.parse(plain_comm_20_10))
                .add(RegexConstraint.parse(plain_comm_20_20))
                .add(RegexConstraint.parse(plain_comm_20_30)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Network(tbdd,configs,imports,exports);
    }

    @Test
    public void threeProngedNetworkTest() {
        Node A0 = new Node("100.0.1.11", "entryA");
        Node B0 = new Node("100.0.1.22", "entryB");
        Node C0 = new Node("100.0.1.33", "entryC");
        Node NODE1 = new Node("100.0.1.44", "node_1");
        Node NODE2 = new Node("101.0.1.11", "node_2");
        Node NODE3 = new Node("101.0.1.22", "node_3");
        Node NODE4 = new Node("101.0.1.33", "node_4");
        Invariant.ClauseBuilder avoidPrefix = Invariant.clauseBuilder().avoidPrefix(PREFIX);
        Invariant.ClauseBuilder match_100_1 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:1"))));
        Invariant.ClauseBuilder match_100_2 = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("100:2"))));
        Invariant.ClauseBuilder avoidBoth = Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(
                RegexConstraint.parse("!1:10"),
                RegexConstraint.parse("!1:30"))));

        TestConfigConstructionUtils.Network net_0 = threeProngedNetwork(A0,B0,C0,NODE1,NODE2,NODE3,NODE4,0);
        Invariant property_0 = Invariant.builder().addClause(avoidBoth).build(net_0.tbdd(), net_0.imports().get(NODE4));
        Verifier verifier_0 = new Verifier(net_0.tbdd(), configInput(net_0.configs()));
        verifier_0.addProperty(NODE4, property_0);
        Verifier.Result result_0 = verifier_0.run();
        assertTrue(result_0.verified());

        TestConfigConstructionUtils.Network net_1 = threeProngedNetwork(A0,B0,C0,NODE1,NODE2,NODE3,NODE4,1);
        Invariant property_1 = Invariant.builder().addClause(avoidBoth).build(net_1.tbdd(), net_1.imports().get(NODE4));
        Verifier verifier_1 = new Verifier(net_1.tbdd(), configInput(net_1.configs()));
        verifier_1.addProperty(NODE4, property_1).addAnchor(A0).addAnchor(B0).addAnchor(C0);
        Verifier.Result result_1 = verifier_1.run();
        assertFalse(result_1.verified());
        assertTrue(result_1.invariants().get(C0).isFalse());
        assertTrue(result_1.counter().isPresent());

        TestConfigConstructionUtils.Network net_2 = threeProngedNetwork(A0,B0,C0,NODE1,NODE2,NODE3,NODE4,2);
        Invariant property_2 = Invariant.builder().addClause(avoidBoth).build(net_2.tbdd(), net_2.imports().get(NODE4));
        Verifier verifier_2 = new Verifier(net_2.tbdd(), configInput(net_2.configs()));
        verifier_2.addProperty(NODE4, property_2).addAnchor(A0).addAnchor(B0).addAnchor(C0);
        Verifier.Result result_2 = verifier_2.run();
        assertFalse(result_2.verified());
        assertTrue(result_2.invariants().get(C0).isFalse());
        assertTrue(result_2.counter().isPresent());
    }

    private TestConfigConstructionUtils.Network twoPathNetwork(Node NODE_1A, Node NODE_1B,
                                                                       Node NODE_2A, Node NODE_2B,
                                                                       Node NODE_3, Node NODE_4,
                                                                       int faulty) {
        // Initialize constants
        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        String plain_comm_1 = "100:1";
        String plain_comm_2 = "100:2";
        String plain_comm_3 = "100:3";

        String regex_comm_100_1 = "^" + plain_comm_1 + "$";
        String regex_comm_100_2 = "^" + plain_comm_2 + "$";
        String regex_comm_100_3 = "^" + plain_comm_3 + "$";

        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));

        // Create configs
        setUpConfigs(configs,NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4);

        includeCommunities(configs.get(NODE_1A),regex_comm_100_1);
        configs.get(NODE_1A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        includeCommunities(configs.get(NODE_1B),regex_comm_100_1);
        configs.get(NODE_1B).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        includeCommunities(configs.get(NODE_2A),regex_comm_100_1,regex_comm_100_2);

        if (faulty == 1 || faulty == 2) {
            includeCommunities(configs.get(NODE_2B),regex_comm_100_1,regex_comm_100_3);
        } else {
            includeCommunities(configs.get(NODE_2B),regex_comm_100_1,regex_comm_100_2);
        }

        if (faulty == 2) {
            includeCommunities(configs.get(NODE_3),regex_comm_100_2,regex_comm_100_3);
        } else {
            includeCommunities(configs.get(NODE_3),regex_comm_100_2);
        }

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4);

        processes.get(NODE_1A).setNeighbors(ImmutableSortedMap.of(
                NODE_2A.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(NODE_2A).setNeighbors(ImmutableSortedMap.of(
                NODE_1A.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_3.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(NODE_1B).setNeighbors(ImmutableSortedMap.of(
                NODE_2B.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(NODE_2B).setNeighbors(ImmutableSortedMap.of(
                NODE_1B.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_3.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(NODE_3).setNeighbors(ImmutableSortedMap.of(
                NODE_4.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2A.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2B.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(NODE_4).setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Create policies
        RoutingPolicy node_1A_import = makePolicy(configs.get(NODE_1A), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node_1A_export = makePolicy(configs.get(NODE_1A), EXPORT_POLICY_NAME,
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(plain_comm_1),permitRoute(true)));

        RoutingPolicy node_1B_import = makePolicy(configs.get(NODE_1B), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node_1B_export = makePolicy(configs.get(NODE_1B), EXPORT_POLICY_NAME,
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(plain_comm_1),permitRoute(true)));

        RoutingPolicy node_2A_import = makePolicy(configs.get(NODE_2A), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node_2A_export = makePolicy(configs.get(NODE_2A), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_1),replaceCommunities(plain_comm_2),permitRoute(true)));

        RoutingPolicy node_2B_import = makePolicy(configs.get(NODE_2B), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node_2B_export = makePolicy(configs.get(NODE_2B), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_1),
                        replaceCommunities(faulty == 1 || faulty == 2 ? plain_comm_3 : plain_comm_2),permitRoute(true)));

        RoutingPolicy node_3_import = makePolicy(configs.get(NODE_3), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node_3_export = makePolicy(configs.get(NODE_3), EXPORT_POLICY_NAME,
                ifStatement(checkForCommunity(plain_comm_2),permitRoute(false), faulty == 2 ?
                        ifStatement(checkForCommunity(plain_comm_3),permitRoute(false),permitRoute(true))
                        : permitRoute(true)));

        RoutingPolicy node_4_import = makePolicy(configs.get(NODE_4), IMPORT_POLICY_NAME, permitRoute(true));
        RoutingPolicy node_4_export = makePolicy(configs.get(NODE_4), EXPORT_POLICY_NAME, permitRoute(true));

        // Store the policies
        imports.put(NODE_1A,node_1A_import);
        imports.put(NODE_1B,node_1B_import);
        imports.put(NODE_2A,node_2A_import);
        imports.put(NODE_2B,node_2B_import);
        imports.put(NODE_3,node_3_import);
        imports.put(NODE_4,node_4_import);

        exports.put(NODE_1A,node_1A_export);
        exports.put(NODE_1B,node_1B_export);
        exports.put(NODE_2A,node_2A_export);
        exports.put(NODE_2B,node_2B_export);
        exports.put(NODE_3,node_3_export);
        exports.put(NODE_4,node_4_export);


        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_1))
                .add(RegexConstraint.parse(plain_comm_2))
                .add(RegexConstraint.parse(plain_comm_3)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Network(tbdd,configs,imports,exports);
    }

    @Test
    public void originalTwoPathNetworkTest() {
        String prefix = "25.13.0.0/16";
        List<String> prefixesConsidered = ImmutableList.of(prefix);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefix)));

        Node NODE_1A = new Node("10.0.1.1","node_1_a");
        Node NODE_1B = new Node("10.0.1.2","node_1_b");
        Node NODE_2A = new Node("10.0.2.1","node_2_a");
        Node NODE_2B = new Node("10.0.2.2","node_2_b");
        Node NODE_3 = new Node("10.0.3.0","node_3_");
        Node NODE_4 = new Node("10.0.4.0","node_4_");

        TestConfigConstructionUtils.Network net = twoPathNetwork(NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4,0);
        Verifier verifier = new Verifier(net.tbdd(),configInput(net.configs()));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.imports().get(NODE_4)));
        verifier.addProperty(NODE_4,property).addAnchor(NODE_1A).addAnchor(NODE_1B);
        Verifier.Result result = verifier.run();
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());

        TestConfigConstructionUtils.Network net_1 = twoPathNetwork(NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4,1);
        Verifier verifier_1 = new Verifier(net_1.tbdd(),configInput(net_1.configs()));
        Invariant property_1 = new Invariant(net_1.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net_1.tbdd(),net_1.imports().get(NODE_4)));
        verifier_1.addProperty(NODE_4,property_1).addAnchor(NODE_1A).addAnchor(NODE_1B);
        Verifier.Result result_1 = verifier_1.run();
        assertFalse(result_1.verified());
        assertTrue(result_1.inferredTrue());
        assertTrue(result_1.counter().isEmpty());

        TestConfigConstructionUtils.Network net_2 = twoPathNetwork(NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4,2);
        Verifier verifier_2 = new Verifier(net_2.tbdd(),configInput(net_2.configs()));
        Invariant property_2 = new Invariant(net_2.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net_2.tbdd(),net_2.imports().get(NODE_4)));
        verifier_2.addProperty(NODE_4,property_2).addAnchor(NODE_1A).addAnchor(NODE_1B);
        Verifier.Result result_2 = verifier_2.run();
        assertTrue(result_2.verified());
        assertTrue(result_2.inferredTrue());
        assertTrue(result_2.counter().isEmpty());
    }

    private TestConfigConstructionUtils.Network simpleNetwork(Ip entry, Ip exit,
                                                              Node NODE_A, Node NODE_B, Node NODE_C, int faulty) {
        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        String plain_comm_1 = "100:1";
        String plain_comm_2 = "100:2";

        String regex_comm_100_1 = "^" + plain_comm_1 + "$";
        String regex_comm_100_2 = "^" + plain_comm_2 + "$";

        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        if (faulty == 2) { includeCommunities(configs.get(NODE_A),regex_comm_100_2);
        } else if (faulty != 1){ includeCommunities(configs.get(NODE_A),regex_comm_100_1); }
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        includeCommunities(configs.get(NODE_C),regex_comm_100_1);
        if (faulty == 5) { includeCommunities(configs.get(NODE_A),regex_comm_100_2);
        } else if (faulty != 6){ includeCommunities(configs.get(NODE_A),regex_comm_100_1); }

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_B.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_C.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                exit,getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Creating routing policy
        RoutingPolicy node_A_import;
        RoutingPolicy node_A_export;
        RoutingPolicy node_B_import;
        RoutingPolicy node_B_export;
        RoutingPolicy node_C_import;
        RoutingPolicy node_C_export;

        node_A_import = faulty == 1 ? makePolicy(configs.get(NODE_A), IMPORT_POLICY_NAME, permitRoute(true)) :
                makePolicy(configs.get(NODE_A), IMPORT_POLICY_NAME, ifStatement(checkForPrefixListMatch(PREFIX_MATCH),
                        faulty == 7 ?
                                addToCommunities(plain_comm_2)
                                : replaceCommunities(faulty == 2 ? plain_comm_2 : plain_comm_1),
                        permitRoute(true)));
        node_A_export = makePolicy(configs.get(NODE_A), EXPORT_POLICY_NAME, permitRoute(true));

        node_B_import = makePolicy(configs.get(NODE_B), IMPORT_POLICY_NAME, permitRoute(true));
        // if faulty == 3, this export should clear communities
        node_B_export = makePolicy(configs.get(NODE_B), EXPORT_POLICY_NAME, permitRoute(true));

        if (faulty == 5) {
            node_C_import = makePolicy(configs.get(NODE_C),IMPORT_POLICY_NAME,
                    ifStatement(checkForCommunity(plain_comm_2), permitRoute(false), permitRoute(true)));
        } else if (faulty == 6 || faulty == 8) {
            node_C_import = makePolicy(configs.get(NODE_C), IMPORT_POLICY_NAME, permitRoute(true));
        } else {
            node_C_import = makePolicy(configs.get(NODE_C), IMPORT_POLICY_NAME,
                    ifStatement(checkForCommunity(plain_comm_1),permitRoute(faulty == 4),permitRoute(faulty != 4)));
        }
        if (faulty == 8) {
            node_C_export = makePolicy(configs.get(NODE_C),EXPORT_POLICY_NAME,
                    ifStatement(checkForCommunity(plain_comm_1), permitRoute(false), permitRoute(true)));
        } else {
            node_C_export = makePolicy(configs.get(NODE_C), EXPORT_POLICY_NAME, permitRoute(true));
        }

        // Store the policies
        imports.put(NODE_A,node_A_import);
        imports.put(NODE_B,node_B_import);
        imports.put(NODE_C,node_C_import);

        exports.put(NODE_A,node_A_export);
        exports.put(NODE_B,node_B_export);
        exports.put(NODE_C,node_C_export);

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_1))
                .add(RegexConstraint.parse(plain_comm_2)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Network(tbdd,configs,imports,exports);
    }

    @Test
    public void simpleNetworkTest() {
        String prefix = "25.13.0.0/16";
        List<String> prefixesConsidered = ImmutableList.of(prefix);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefix)));

        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");
        Edge target = new Edge(NODE_C.getIp(),exit);

        TestConfigConstructionUtils.Network net = simpleNetwork(entry,exit,NODE_A,NODE_B,NODE_C,0);
        Verifier verifier = new Verifier(net.tbdd(),configInput(net.configs()));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.imports().get(NODE_C)));
        verifier.addProperty(target,property);
        Verifier.Result result = verifier.run();

        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());
    }
}
