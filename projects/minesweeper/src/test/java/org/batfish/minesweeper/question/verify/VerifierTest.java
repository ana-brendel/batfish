package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
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

}
