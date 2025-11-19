package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.batfish.datamodel.BgpActivePeerConfig;
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
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.bgp.LocalOriginationTypeTieBreaker;
import org.batfish.datamodel.bgp.NextHopIpTieBreaker;
import org.batfish.datamodel.bgp.community.StandardCommunity;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.communities.ColonSeparatedRendering;
import org.batfish.datamodel.routing_policy.communities.CommunityIs;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchExpr;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchRegex;
import org.batfish.datamodel.routing_policy.communities.CommunitySet;
import org.batfish.datamodel.routing_policy.communities.HasCommunity;
import org.batfish.datamodel.routing_policy.communities.InputCommunities;
import org.batfish.datamodel.routing_policy.communities.LiteralCommunitySet;
import org.batfish.datamodel.routing_policy.communities.MatchCommunities;
import org.batfish.datamodel.routing_policy.communities.SetCommunities;
import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.datamodel.routing_policy.expr.DestinationNetwork;
import org.batfish.datamodel.routing_policy.expr.MatchPrefixSet;
import org.batfish.datamodel.routing_policy.expr.NamedPrefixSet;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements;
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
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.junit.Assert.assertTrue;

public class NetworkThreadTest {
    private static final NetworkFactory nf = new NetworkFactory();

    public record Network(TransferBDD tbdd, Map<Node, Configuration> configs, Map<Node, RoutingPolicy> imports,
                          Map<Node, RoutingPolicy> exports) {
        private Map<String, Configuration> configInput() {
            Map<String, Configuration> result = new HashMap<>();
            for (Node node : configs.keySet()) {
                result.put(node.getName(), configs.get(node));
            }
            return result;
        }
    }

    private static ConfigAtomicPredicates getConfigAtomicPredicates(Collection<Configuration> configs, Set<RegexConstraint> communityRegexes) {
        return new ConfigAtomicPredicates(
                configs.stream().map(config -> {
                    Collection<RoutingPolicy> policies = config.getRoutingPolicies().values();
                    Map.Entry<Configuration, Collection<RoutingPolicy>> entry = new AbstractMap.SimpleImmutableEntry<>(config, policies);
                    return entry; // need to create variables to adhere to types
                }).toList(),
                communityRegexes.stream().flatMap(rc -> {
                    String regex = rc.getRegex();
                    return switch (rc.getRegexType()) {
                        case REGEX -> ImmutableList.of(CommunityVar.from(regex)).stream();
                        case STRUCTURE_NAME -> Stream.empty();
                    };
                }).collect(ImmutableSet.toImmutableSet()),
                new HashSet<>()); // for AS path stuff
    }

    private BgpProcess getBgpProcess(Map<Node, Configuration> configs, Node node) {
        Vrf vrf = nf.vrfBuilder().setOwner(configs.get(node)).setName(Configuration.DEFAULT_VRF_NAME).build();
        return nf.bgpProcessBuilder().setRouterId(node.getIp())
                .setEbgpAdminCost(0).setIbgpAdminCost(0).setLocalAdminCost(0)
                .setLocalOriginationTypeTieBreaker(LocalOriginationTypeTieBreaker.NO_PREFERENCE)
                .setNetworkNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setRedistributeNextHopIpTieBreaker(NextHopIpTieBreaker.HIGHEST_NEXT_HOP_IP)
                .setVrf(vrf).build();
    }

    private BgpActivePeerConfig getBgpActivePeerConfig(Node node, String importPolicy, String exportPolicy) {
        BgpActivePeerConfig.Builder builder = BgpActivePeerConfig.builder().setGroup("nextDoor");
        if (importPolicy != null && exportPolicy != null) {
            return builder.setIpv4UnicastAddressFamily(Ipv4UnicastAddressFamily.builder().setImportPolicy(importPolicy).setExportPolicy(exportPolicy).build()).build();
        } else if (importPolicy != null) {
            return builder.setIpv4UnicastAddressFamily(Ipv4UnicastAddressFamily.builder().setImportPolicy(importPolicy).build()).build();
        } else if (exportPolicy != null) {
            return builder.setIpv4UnicastAddressFamily(Ipv4UnicastAddressFamily.builder().setExportPolicy(exportPolicy).build()).build();
        } else {
            return builder.build();
        }
    }

    private RoutingPolicy getPermitDefault(Configuration config, String name) {
        return nf.routingPolicyBuilder().setOwner(config).setName(name)
                .setStatements(ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue))).build();
    }

    private RoutingPolicy getDenyDefault(Configuration config, String name) {
        return nf.routingPolicyBuilder().setOwner(config).setName(name)
                .setStatements(ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse))).build();
    }

    public Network originalNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE) {
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(), "^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(), "^100:2$");
        CommunityMatchExpr comm_100_3 = new CommunityMatchRegex(ColonSeparatedRendering.instance(), "^100:3$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH, prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2", comm_100_2, "comm_100_3", comm_100_3));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))), "comm_100_3", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:3")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1", comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2", comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs, ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(), getBgpActivePeerConfig(ALPHANODE, null, EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs, BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(), getBgpActivePeerConfig(BETANODE, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME),
                GAMMANODE.getIp(), getBgpActivePeerConfig(BETANODE, IMPORT_POLICY_NAME, EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs, GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(), getBgpActivePeerConfig(GAMMANODE, null, EXPORT_POLICY_NAME),
                DELTANODE.getIp(), getBgpActivePeerConfig(GAMMANODE, null, EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(configs, DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(), getBgpActivePeerConfig(DELTANODE, null, null)));

        BooleanExpr check_comm_100_1 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1"))));
        BooleanExpr check_comm_100_2 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))));
        BooleanExpr checkPrefixMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_MATCH));

        List<Statement> add_100_1 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:1")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_100_2 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:2")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_100_3 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:3")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> permit = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue));
        List<Statement> deny = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));

        // original now
        RoutingPolicy alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(checkPrefixMatch, add_100_1, permit))).build();
        RoutingPolicy betaImport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(IMPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1, add_100_2, permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1, add_100_2, permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2, deny, permit))).build();

        imports.put(ALPHANODE, new RoutingPolicy("BLANK", configs.get(ALPHANODE)));
        imports.put(BETANODE, betaImport);
        imports.put(GAMMANODE, new RoutingPolicy("BLANK", configs.get(GAMMANODE)));
        imports.put(DELTANODE, new RoutingPolicy("BLANK", configs.get(DELTANODE)));
        exports.put(ALPHANODE, alphaExport);
        exports.put(BETANODE, betaExport);
        exports.put(GAMMANODE, gammaExport);
        exports.put(DELTANODE, new RoutingPolicy("BLANK", configs.get(DELTANODE)));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2")).add(RegexConstraint.parse("100:3")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd, configs, imports, exports);
    }

    @Test
    public void originalVerificationTest() {
        String prefix = "25.13.0.0/16";
        List<String> prefixesConsidered = ImmutableList.of(prefix);
        Node ALPHANODE = new Node("10.0.0.1", "alphaNode");
        Node BETANODE = new Node("10.0.0.2", "betaNode");
        Node GAMMANODE = new Node("10.0.0.3", "gammaNode");
        Node DELTANODE = new Node("10.0.0.4", "deltaNode");
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefix)));

        Network net = originalNetwork(ALPHANODE, BETANODE, GAMMANODE, DELTANODE);
        Verifier verifier = new Verifier(net.tbdd, net.configInput());
        Invariant property = new Invariant(net.tbdd, Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd, net.imports.get(DELTANODE)));
        verifier.addProperty(DELTANODE, property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        Set<NetworkThread> threads = NetworkThread.getThreadsFromVerifier(verifier);
        Set<Set<String>> threadStrings = threads.stream().map(t -> t.dirtyString(prefixesConsidered)).collect(Collectors.toSet());

        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());
    }
}
