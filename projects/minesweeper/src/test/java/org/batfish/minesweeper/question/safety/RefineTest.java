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
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraints;
import org.batfish.minesweeper.question.verificationutilities.Edge;
import org.batfish.minesweeper.question.verificationutilities.Invariant;
import org.batfish.minesweeper.question.verificationutilities.Lightyear;
import org.batfish.minesweeper.question.verificationutilities.Location;
import org.batfish.minesweeper.question.verificationutilities.NetworkInfo;
import org.batfish.minesweeper.question.verificationutilities.Node;
import org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils;
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
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.addToCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForCommunity;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.clearCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.getBgpActivePeerConfig;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.ifStatement;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.includeCommunities;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.metricGreaterThan;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.permitRoute;
import static org.batfish.minesweeper.question.verificationutilities.TestConfigConstructionUtils.replaceCommunities;
import static org.junit.Assert.assertEquals;
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


    private TestConfigConstructionUtils.Networkv2 networkA(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C, String p_str) {
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
        if (preventBackwards) {
            makePolicy(configs.get(NODE_A),"rightImport",permitRoute(false));
        }
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH_P),replaceCommunities(plain_comm_10),replaceCommunities(plain_comm_30)));

        makePolicy(configs.get(NODE_B),"leftImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH_Q),replaceCommunities(plain_comm_20),permitRoute(true)));
        if (preventBackwards) {
            makePolicy(configs.get(NODE_B),"rightImport",permitRoute(false));
        }

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

    // All the "validNetwork*Test()" functions don't explicitly check refinement behavior
    @Test
    public void validityNetworkATest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkA(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();
        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertFalse(result.verified);
    }
    @Test
    public void validityNetworkBTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkB(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();
        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertFalse(result.verified);
    }
    @Test
    public void validityNetworkCTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkC(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();

        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertFalse(result.verified);
    }
    @Test
    public void validityNetworkDTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkD(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(target,property);

        Infer.Result result = verifier.run();

        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertFalse(result.verified);
    }
    @Test
    public void validityNetworkETest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkE(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(NODE_B,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        assertTrue(lightyear.check(refiner.initial).isEmpty());
        assertTrue(lightyear.check(refiner.refined).isEmpty());
        assertTrue(result.verified);
        assertTrue(result.inferredTrue());
    }
    @Test
    public void validityNetworkFTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkF(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(NODE_B,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        assertTrue(lightyear.check(refiner.initial).isEmpty());
        assertTrue(lightyear.check(refiner.refined).isEmpty());
        assertTrue(result.verified);
        assertTrue(result.inferredTrue());
    }
    @Test
    public void validityNetworkGTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkG(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        verifier.addProperty(NODE_B,property);

        Infer.Result result = verifier.run();

        Refine.Result refiner = verifier.refiner().refine();

        assertTrue(lightyear.check(refiner.initial).isEmpty());
        assertTrue(lightyear.check(refiner.refined).isEmpty());
        assertTrue(result.verified);
        assertTrue(result.inferredTrue());
    }
    @Test
    public void validityNetworkHTest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        String q_str = "13.25.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkH(entry,exit,NODE_A,NODE_B,NODE_C,p_str,q_str,true);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Invariant.ClauseBuilder PREFIX_P = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str))));
        Invariant.ClauseBuilder PREFIX_Q = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(q_str))));
        Invariant property = Invariant.builder().addClause(PREFIX_P).addClause(PREFIX_Q).build(net.tbdd(),net.template());
        verifier.addProperty(new Edge(NODE_C.getSingleIp(),exit),property);

        Infer.Result result = verifier.run();

        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertFalse(result.verified);
    }
    @Test
    public void validityNetworkITest() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        String q_str = "13.25.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = networkI(entry,exit,NODE_A,NODE_B,NODE_C,p_str,q_str);
        NetworkInfo info = net.getInfo();
        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Invariant.ClauseBuilder PREFIX_P = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str))));
        Invariant.ClauseBuilder PREFIX_Q = Invariant.clauseBuilder().matchPrefix(new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(q_str))));
        Invariant property = Invariant.builder().addClause(PREFIX_P).addClause(PREFIX_Q).build(net.tbdd(),net.template()).negate();
        verifier.addProperty(new Edge(NODE_C.getSingleIp(),exit),property);

        Infer.Result result = verifier.run();

        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertFalse(result.verified);
    }

    // The "refineNetwork*()" tests explicit check for what the expected refinements are, these might change if we change refinement
    private TestConfigConstructionUtils.Networkv2 refineNetwork1(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C, String p_str) {
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
        includeCommunities(configs.get(NODE_C),regex_comm_10_10,regex_comm_20_20,regex_comm_30_30);

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
        makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),addToCommunities(plain_comm_10),permitRoute(true)));

        // Adds extra communities
        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_10), permitRoute(false),
                        ifStatement(checkForCommunity(plain_comm_20),permitRoute(false),
                                ifStatement(checkForCommunity(plain_comm_30),permitRoute(false),permitRoute(true)))));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20))
                .add(RegexConstraint.parse(plain_comm_30)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    @Test
    public void refineNetwork1Test() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = refineNetwork1(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        info.addAssumption(new Edge(exit,NODE_C.getSingleIp()),property.copy());

        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        verifier.addProperty(target,property.copy());

        Infer.Result result = verifier.run();
        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertTrue(result.verified);

        Refine.Result refiner = verifier.refiner().refine();
        assertTrue(lightyear.check(refiner.refined).isEmpty());
        assertTrue(refiner.verified);

        Invariant refined_property = Invariant.builder()
                .addClause(Invariant.clauseBuilder().avoidPrefix(PREFIX))
                .addClause(Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("10:10")))))
                .build(net.tbdd(),net.template());
        for (Location location : refiner.refined.keySet()) {
            if (location.equals(new Edge(exit,NODE_C.getSingleIp())) || location.equals(new Edge(NODE_C.getSingleIp(),exit))) {
                assertEquals(property.copy(),refiner.refined.get(location));
            } else if (location.equals(new Edge(entry,NODE_A.getSingleIp()))) {
                assertTrue(refiner.refined.get(location).isTrue());
            } else {
                assertEquals(refined_property.copy(),refiner.refined.get(location));
            }
        }
    }

    private TestConfigConstructionUtils.Networkv2 refineNetwork2(Ip entry, Ip exit, Node NODE_A, Node NODE_B, Node NODE_C, String p_str) {
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
        includeCommunities(configs.get(NODE_B),regex_comm_10_10,regex_comm_20_20);
        includeCommunities(configs.get(NODE_C),regex_comm_10_10,regex_comm_20_20,regex_comm_30_30);

        // Create BGP processes
        Map<Node,BgpProcess> processes = getBgpProcesses(configs,NODE_A,NODE_B,NODE_C);

        processes.get(NODE_A).setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig("outside","outsideImport",null),
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null)));

        processes.get(NODE_B).setNeighbors(ImmutableSortedMap.of(
                NODE_A.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,"outToA"),
                NODE_C.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,"outToC")));

        processes.get(NODE_C).setNeighbors(ImmutableSortedMap.of(
                NODE_B.getSingleIp(),getBgpActivePeerConfig("internalNeighbor",null,null),
                exit,getBgpActivePeerConfig("outside",null,"outsideExport")));

        // Creating routing policy
        makePolicy(configs.get(NODE_A),"outsideImport",
                ifStatement(checkForPrefixListMatch(PREFIX_MATCH),addToCommunities(plain_comm_10),permitRoute(true)));

        makePolicy(configs.get(NODE_B),"outToC",
                ifStatement(checkForCommunity(plain_comm_10),addToCommunities(plain_comm_20),permitRoute(true)));
        makePolicy(configs.get(NODE_B),"outToA",
                ifStatement(checkForCommunity(plain_comm_20),addToCommunities(plain_comm_10),permitRoute(true)));

        RoutingPolicy templatePolicy = makePolicy(configs.get(NODE_C),"outsideExport",
                ifStatement(checkForCommunity(plain_comm_20), permitRoute(false),permitRoute(true)));

        // Set up the tbdd
        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse(plain_comm_10))
                .add(RegexConstraint.parse(plain_comm_20))
                .add(RegexConstraint.parse(plain_comm_30)).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new TestConfigConstructionUtils.Networkv2(tbdd,configs,templatePolicy,List.of(p_str));
    }

    @Test
    public void refineNetwork2Test() {
        Ip entry = Ip.parse("10.10.0.0");
        Ip exit = Ip.parse("10.10.10.0");
        Node NODE_A = new Node("10.10.0.1","node_A");
        Node NODE_B = new Node("10.10.0.2","node_B");
        Node NODE_C = new Node("10.10.0.3","node_C");

        String p_str = "25.13.0.0/16";
        TestConfigConstructionUtils.Networkv2 net = refineNetwork2(entry,exit,NODE_A,NODE_B,NODE_C,p_str);
        NetworkInfo info = net.getInfo();

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(p_str)));
        Invariant property = new Invariant(net.tbdd(),Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd(),net.template()));
        info.addAssumption(new Edge(exit,NODE_C.getSingleIp()),property.copy());

        Infer verifier = info.toInfer();
        Lightyear lightyear = info.checker();

        Edge target = new Edge(NODE_C.getSingleIp(),exit);
        verifier.addProperty(target,property.copy());

        Infer.Result result = verifier.run();
        assertTrue(lightyear.check(result.invariants).isEmpty());
        assertTrue(result.verified);

        Refine.Result refiner = verifier.refiner().refine();
        assertTrue(lightyear.check(refiner.refined).isEmpty());
        assertTrue(refiner.verified);

        Invariant prefix_or_1010 = Invariant.builder()
                .addClause(Invariant.clauseBuilder().avoidPrefix(PREFIX))
                .addClause(Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("10:10")))))
                .build(net.tbdd(),net.template());
        Invariant prefix_or_2020 = Invariant.builder()
                .addClause(Invariant.clauseBuilder().avoidPrefix(PREFIX))
                .addClause(Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("20:20")))))
                .build(net.tbdd(),net.template());
        Invariant prefix_or_1010_or_2020 = Invariant.builder()
                .addClause(Invariant.clauseBuilder().avoidPrefix(PREFIX))
                .addClause(Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("10:10")))))
                .addClause(Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("20:20")))))
                .build(net.tbdd(),net.template());
        Invariant prefix_20_20_or_1010 = Invariant.builder()
                .addClause(Invariant.clauseBuilder().avoidPrefix(PREFIX).setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("!20:20")))))
                .addClause(Invariant.clauseBuilder().setCommunities(new RegexConstraints(List.of(RegexConstraint.parse("10:10")))))
                .build(net.tbdd(),net.template());
        for (Location location : refiner.refined.keySet()) {
            if (location.equals(new Edge(exit,NODE_C.getSingleIp())) || location.equals(new Edge(NODE_C.getSingleIp(),exit))) {
                assertEquals(property.copy(),refiner.refined.get(location));
            } else if (location.equals(new Edge(entry,NODE_A.getSingleIp()))) {
                assertTrue(refiner.refined.get(location).isTrue());
            } else if (location.equals(NODE_B)) {
                assertEquals(prefix_or_1010_or_2020.copy(),refiner.refined.get(location));
            } else if (location.equals(NODE_A) || location.equals(new Edge(NODE_A,NODE_B))) {
                assertEquals(prefix_or_1010.copy(),refiner.refined.get(location));
            } else if (location.equals(new Edge(NODE_B,NODE_A))) {
                assertEquals(prefix_20_20_or_1010.copy(),refiner.refined.get(location));
            } else {
                assertEquals(prefix_or_2020.copy(),refiner.refined.get(location));
            }
        }
    }
}
