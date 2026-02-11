package org.batfish.minesweeper.question.verificationutilities;

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
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.replaceCommunities;
import static org.junit.Assert.assertTrue;

public class LightyearTest {
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
                BETANODE.getSingleIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(BETANODE).setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getSingleIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getSingleIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(GAMMANODE).setNeighbors(ImmutableSortedMap.of(
                BETANODE.getSingleIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                DELTANODE.getSingleIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        processes.get(DELTANODE).setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getSingleIp(),getBgpActivePeerConfig(NEXT_DOOR,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

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
        RegexConstraints comm_1 = new RegexConstraints(List.of(RegexConstraint.parse("100:1")));
        RegexConstraints comm_2 = new RegexConstraints(List.of(RegexConstraint.parse("100:2")));

        TestConfigConstructionUtils.Network net = originalExample(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);
        Invariant notPrefix = new Invariant(net.tbdd(),
                Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(), net.imports().get(DELTANODE)));
        Invariant notPrefix_or_100_2 = Invariant.builder().addClause(Invariant.clauseBuilder().avoidPrefix(PREFIX))
                .addClause(Invariant.clauseBuilder().setCommunities(comm_2))
                .build(net.tbdd(), net.imports().get(DELTANODE));
        Invariant notPrefix_or_100_1_or_100_2 = Invariant.builder().addClause(Invariant.clauseBuilder().avoidPrefix(PREFIX))
                .addClause(Invariant.clauseBuilder().setCommunities(comm_1))
                .addClause(Invariant.clauseBuilder().setCommunities(comm_2))
                .build(net.tbdd(), net.imports().get(DELTANODE));

        Optional<Map.Entry<Location, Location>> l1 = net.getInfo().checker().check(Map.of(
                ALPHANODE, new Invariant(net.tbdd()),
                BETANODE, notPrefix_or_100_1_or_100_2.copy(),
                GAMMANODE, notPrefix_or_100_2.copy(),
                DELTANODE, notPrefix.copy(),
                new Edge(ALPHANODE,BETANODE),notPrefix_or_100_1_or_100_2.copy(),
                new Edge(BETANODE,ALPHANODE),new Invariant(net.tbdd()),
                new Edge(BETANODE,GAMMANODE),notPrefix_or_100_2.copy(),
                new Edge(GAMMANODE,BETANODE),notPrefix_or_100_1_or_100_2.copy(),
                new Edge(GAMMANODE,DELTANODE),notPrefix.copy(),
                new Edge(DELTANODE,GAMMANODE),notPrefix_or_100_2.copy()
        ));

        assertTrue(l1.isEmpty());
    }
}
