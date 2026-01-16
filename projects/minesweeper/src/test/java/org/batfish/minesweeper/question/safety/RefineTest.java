package org.batfish.minesweeper.question.safety;

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
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.metricGreaterThan;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.permitRoute;
import static org.batfish.minesweeper.question.safety.TestConfigConstructionUtils.replaceCommunities;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class RefineTest {
    private static final NetworkFactory nf = new NetworkFactory();

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


    private TestConfigConstructionUtils.Networkv2 networkA(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";

        String PREFIX_MATCH = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(NODE_C),regex_comm_10_10);

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside",null,"outsideExport")));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(plain_comm_10),permitRoute(true)));

        makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_10), permitRoute(false), permitRoute(true)));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkB(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";
        String plain_comm_20 = "20:20";
        String regex_comm_20_20 = "^" + plain_comm_20 + "$";

        String PREFIX_MATCH = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(NODE_C),regex_comm_10_10,regex_comm_20_20);

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside","outsideImport","outsideExport")));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(plain_comm_10),permitRoute(true)));

        makePolicy(configs.get(NODE_C),"outsideImport",clearCommunities());
        makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_10), permitRoute(false),
                        ifStatement(checkForCommunity(plain_comm_20),permitRoute(false),permitRoute(true))));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkC(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";
        String plain_comm_20 = "20:20";
        String regex_comm_20_20 = "^" + plain_comm_20 + "$";

        String PREFIX_MATCH = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(NODE_B),regex_comm_10_10,regex_comm_20_20);
        includeCommunities(configs.get(NODE_C),regex_comm_20_20);

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor","rightImport","rightExport")));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside",null,"outsideExport")));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),addToCommunities(plain_comm_10),permitRoute(true)));

        makePolicy(configs.get(NODE_B),"rightImport",
                ifStatement(checkForCommunity(plain_comm_20),addToCommunities(plain_comm_10),permitRoute(true)));
        makePolicy(configs.get(NODE_B),"rightExport",
                ifStatement(checkForCommunity(plain_comm_10),addToCommunities(plain_comm_20),permitRoute(true)));

        makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_20), permitRoute(false),permitRoute(true)));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkD(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";
        String plain_comm_20 = "20:20";
        String regex_comm_20_20 = "^" + plain_comm_20 + "$";

        String PREFIX_MATCH = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(NODE_B),regex_comm_10_10,regex_comm_20_20);
        includeCommunities(configs.get(NODE_C),regex_comm_20_20);

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor","rightImport","rightExport")));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside",null,"outsideExport")));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),replaceCommunities(plain_comm_10),clearCommunities()));

        makePolicy(configs.get(NODE_B),"rightImport",
                ifStatement(checkForCommunity(plain_comm_20),replaceCommunities(plain_comm_10),permitRoute(true)));
        makePolicy(configs.get(NODE_B),"rightExport",
                ifStatement(checkForCommunity(plain_comm_10),replaceCommunities(plain_comm_20),permitRoute(true)));

        //makePolicy(configs.get(NODE_C),"outsideImport",clearCommunities());
        makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_20), permitRoute(false),permitRoute(true)));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkE(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";
        String plain_comm_20 = "20:20";
        String regex_comm_20_20 = "^" + plain_comm_20 + "$";

        String PREFIX_MATCH = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(NODE_C),regex_comm_20_20);
        configs.get(NODE_C).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside","outsideImport",null)));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),permitRoute(false),addToCommunities(plain_comm_10)));

        makePolicy(configs.get(NODE_C),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),permitRoute(false),addToCommunities(plain_comm_20)));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkF(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";
        String plain_comm_20 = "20:20";
        String regex_comm_20_20 = "^" + plain_comm_20 + "$";
        String plain_comm_30 = "30:30";
        String regex_comm_30_30 = "^" + plain_comm_30 + "$";

        String PREFIX_MATCH = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(NODE_B),regex_comm_30_30);
        includeCommunities(configs.get(NODE_C),regex_comm_20_20);
        configs.get(NODE_C).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor","neighborImport",null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor","neighborImport",null)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside","outsideImport",null)));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),permitRoute(false),addToCommunities(plain_comm_10)));

        makePolicy(configs.get(NODE_B),"neighborImport",
                ifStatement(checkForCommunity(plain_comm_30),permitRoute(false),permitRoute(true)));

        makePolicy(configs.get(NODE_C),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),permitRoute(false),addToCommunities(plain_comm_20)));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20))
                .add(RegexConstraint.parse(plain_comm_30)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkG(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";

        String PREFIX_MATCH = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        includeCommunities(configs.get(NODE_C),regex_comm_10_10);
        configs.get(NODE_C).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside","outsideImport",null)));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),permitRoute(false),
                        ifStatement(metricGreaterThan(10L),permitRoute(false),permitRoute(true))));

        makePolicy(configs.get(NODE_C),"outsideImport",
                ifStatement(checkForCommunity(plain_comm_10),permitRoute(false),
                        ifStatement(checkForPrefixListMatch(PREFIX_MATCH),permitRoute(false),permitRoute(true))));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkH(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str,String q_str,
                                                           boolean preventBackwards) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";
        String plain_comm_20 = "20:20";
        String regex_comm_20_20 = "^" + plain_comm_10 + "$";
        String plain_comm_30 = "30:30";
        String regex_comm_30_30 = "^" + plain_comm_10 + "$";

        String PREFIX_MATCH_P = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList pPrefixMatch = new RouteFilterList(PREFIX_MATCH_P, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        String PREFIX_MATCH_Q = "prefixMatch";
        PrefixRange q_prefix = PrefixRange.fromPrefix(Prefix.parse(q_str));
        RouteFilterList qPrefixMatch = new RouteFilterList(PREFIX_MATCH_Q, ImmutableList.of(new RouteFilterLine(PERMIT,q_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10,regex_comm_30_30);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH_P,pPrefixMatch));
        includeCommunities(configs.get(NODE_B),regex_comm_20_20);
        configs.get(NODE_B).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH_Q,qPrefixMatch));
        includeCommunities(configs.get(NODE_C),regex_comm_10_10,regex_comm_20_20);

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",preventBackwards ? "rightImport" : null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor","leftImport",null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",preventBackwards ? "rightImport" : null,null)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside",null,"outsideExport")));

        // Creating routing policy
        if (preventBackwards) makePolicy(configs.get(NODE_A),"rightImport",permitRoute(false));
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH_P),replaceCommunities(plain_comm_10),replaceCommunities(plain_comm_30)));

        makePolicy(configs.get(NODE_B),"leftImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH_Q),replaceCommunities(plain_comm_20),permitRoute(true)));
        if (preventBackwards) makePolicy(configs.get(NODE_B),"rightImport",permitRoute(false));

        makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_10),permitRoute(true),
                        ifStatement(checkForCommunity(plain_comm_20),permitRoute(true),permitRoute(false))));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20))
                .add(RegexConstraint.parse(plain_comm_30)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str,q_str));
    }

    private TestConfigConstructionUtils.Networkv2 networkI(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C,String p_str,String q_str) {
        Map<Node, Configuration> configs = new HashMap<>();

        String plain_comm_10 = "10:10";
        String regex_comm_10_10 = "^" + plain_comm_10 + "$";

        String PREFIX_MATCH_P = "prefixMatch";
        PrefixRange p_prefix = PrefixRange.fromPrefix(Prefix.parse(p_str));
        RouteFilterList pPrefixMatch = new RouteFilterList(PREFIX_MATCH_P, ImmutableList.of(new RouteFilterLine(PERMIT,p_prefix)));

        String PREFIX_MATCH_Q = "prefixMatch";
        PrefixRange q_prefix = PrefixRange.fromPrefix(Prefix.parse(q_str));
        RouteFilterList qPrefixMatch = new RouteFilterList(PREFIX_MATCH_Q, ImmutableList.of(new RouteFilterLine(PERMIT,q_prefix)));

        // Create configs
        setUpConfigs(configs,NODE_A,NODE_B,NODE_C);

        includeCommunities(configs.get(NODE_A),regex_comm_10_10);
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH_P,pPrefixMatch));
        includeCommunities(configs.get(NODE_B),regex_comm_10_10);
        configs.get(NODE_B).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH_Q,qPrefixMatch));
        includeCommunities(configs.get(NODE_C),regex_comm_10_10);

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor","leftImport",null),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside",null,"outsideExport")));

        // Creating routing policy
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH_P),replaceCommunities(plain_comm_10),permitRoute(true)));

        makePolicy(configs.get(NODE_B),"leftImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH_Q),replaceCommunities(plain_comm_10),permitRoute(true)));

        makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_10),permitRoute(false),permitRoute(true)));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str,q_str));
    }

    @Test
    public void networkATest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkA(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertFalse(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkBTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkB(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertFalse(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkCTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkC(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertFalse(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkDTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkD(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);
        Map<Location,String> interpolants = refiner.displayInterpolants(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertFalse(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkETest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkE(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(NODE_B,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkFTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkF(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(NODE_B,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkGTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkG(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(NODE_B,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkHTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        String q_str = "13.25.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkH(entry,exit,NODE_A,NODE_B,NODE_C,p_str,q_str,true);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        Invariant.ClauseBuilder PREFIX_P = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str))));
        Invariant.ClauseBuilder PREFIX_Q = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(q_str))));
        Invariant property = Invariant.builder().addClause(PREFIX_P).addClause(PREFIX_Q).build(net.tbdd(),net.template());
        verifier.addProperty(new Edge(NODE_C.getSingleIp(),exit),property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertFalse(result.verified());
        assertTrue(result.inferredTrue());
    }
    @Test
    public void networkITest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        String q_str = "13.25.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkI(entry,exit,NODE_A,NODE_B,NODE_C,p_str,q_str);
        Infer verifier = new Infer(net.tbdd(),configInput(net.configs()));
        Lightyear lightyear = verifier.checker();

        Invariant.ClauseBuilder PREFIX_P = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str))));
        Invariant.ClauseBuilder PREFIX_Q = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(q_str))));
        Invariant property = Invariant.builder().addClause(PREFIX_P).addClause(PREFIX_Q).build(net.tbdd(),net.template()).negate();
        verifier.addProperty(new Edge(NODE_C.getSingleIp(),exit),property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        Map<Location,String> initials = refiner.displayInitial(verifier.shortcuts);
        Map<Location,String> refinements = refiner.displayRefinement(verifier.shortcuts);
        Map<Location,String> interpolants = refiner.displayInterpolants(verifier.shortcuts);

        assertTrue(lightyear.check(refiner.initial()));
        assertTrue(lightyear.check(refiner.refined()));
        assertFalse(result.verified());
        assertTrue(result.inferredTrue());
    }
}
