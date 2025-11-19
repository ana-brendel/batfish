package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSortedMap;
import org.batfish.datamodel.BgpActivePeerConfig;
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
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.batfish.datamodel.LineAction.PERMIT;
import static org.batfish.minesweeper.question.verify.Development.addToCommunities;
import static org.batfish.minesweeper.question.verify.Development.checkForCommunity;
import static org.batfish.minesweeper.question.verify.Development.checkForPrefixListMatch;
import static org.batfish.minesweeper.question.verify.Development.clearCommunities;
import static org.batfish.minesweeper.question.verify.Development.includeCommunities;
import static org.batfish.minesweeper.question.verify.Development.permitRoute;
import static org.batfish.minesweeper.question.verify.Development.replaceCommunities;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class DevelopmentTest {
    private static final NetworkFactory nf = new NetworkFactory();

    public record Network(TransferBDD tbdd,Map<Node, Configuration> configs,Map<Node, RoutingPolicy> imports,Map<Node, RoutingPolicy> exports) {
        private Map<String,Configuration> configInput() {
            Map<String,Configuration> result = new HashMap<>();
            for (Node node: configs.keySet()) {
                result.put(node.getName(),configs.get(node));
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
                } ).toList(),
                communityRegexes.stream().flatMap(rc -> {
                    String regex = rc.getRegex();
                    return switch (rc.getRegexType()) {
                        case REGEX -> ImmutableList.of(CommunityVar.from(regex)).stream();
                        case STRUCTURE_NAME -> Stream.empty();
                    };}).collect(ImmutableSet.toImmutableSet()),
                new HashSet<>()); // for AS path stuff
    }

    private BgpProcess getBgpProcess (Map<Node, Configuration> configs, Node node) {
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
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        CommunityMatchExpr comm_100_3 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:3$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2,"comm_100_3",comm_100_3));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))),"comm_100_3", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:3")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(configs,DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE,null,null)));

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
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();
        RoutingPolicy betaImport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(IMPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2,deny,permit))).build();

        imports.put(ALPHANODE,new RoutingPolicy("BLANK",configs.get(ALPHANODE)));
        imports.put(BETANODE,betaImport);
        imports.put(GAMMANODE,new RoutingPolicy("BLANK",configs.get(GAMMANODE)));
        imports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2")).add(RegexConstraint.parse("100:3")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }
    @Test
    public void originalVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("10.0.0.1","alphaNode");
        Node BETANODE = new Node("10.0.0.2","betaNode");
        Node GAMMANODE = new Node("10.0.0.3","gammaNode");
        Node DELTANODE = new Node("10.0.0.4","deltaNode");
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = originalNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        verifier.addProperty(DELTANODE,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());

        Verifier.VerificationResult forwards = verifier.runForwards(ALPHANODE);
        //List<String> pp = forwards.dirtyReadableResults(prefixesConsidered);
        assertTrue(forwards.verified());
    }

    public Network weakNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE) {
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        CommunityMatchExpr comm_100_3 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:3$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));

        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_3",comm_100_3));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_3", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:3")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(configs,DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE,null,null)));

        BooleanExpr check_comm_100_1 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1"))));
        BooleanExpr check_comm_100_3 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:3"))));
        BooleanExpr checkPrefixMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_MATCH));

        List<Statement> add_100_1 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:1")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_100_2 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:2")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> permit = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue));
        List<Statement> deny = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));

        RoutingPolicy alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_3,deny,permit))).build();

        imports.put(ALPHANODE,getPermitDefault(configs.get(ALPHANODE), IMPORT_POLICY_NAME));
        imports.put(BETANODE,getPermitDefault(configs.get(BETANODE), IMPORT_POLICY_NAME));
        imports.put(GAMMANODE,getPermitDefault(configs.get(GAMMANODE), IMPORT_POLICY_NAME));
        imports.put(DELTANODE,getPermitDefault(configs.get(DELTANODE), IMPORT_POLICY_NAME));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,getPermitDefault(configs.get(DELTANODE), EXPORT_POLICY_NAME));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2"))
                .add(RegexConstraint.parse("100:3")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }
    @Test
    public void weakVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("11.0.0.1","alphaNode_1");
        Node BETANODE = new Node("11.0.0.2","betaNode_1");
        Node GAMMANODE = new Node("11.0.0.3","gammaNode_1");
        Node DELTANODE = new Node("11.0.0.4","deltaNode_1");
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = weakNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        verifier.addProperty(DELTANODE,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());

        Invariant trueI = new Invariant(net.tbdd);
        Invariant tester = trueI.strongestPostcondition(net.exports.get(ALPHANODE));
        List<String> p = tester.dirtyReadability(prefixesConsidered);

        Verifier.VerificationResult forwards = verifier.runForwards(ALPHANODE);
        List<String> pp = forwards.dirtyReadableResults(prefixesConsidered);
        assertTrue(forwards.verified());
    }

    public Network noTaggingNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE) {
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(configs,DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE,null,null)));

        BooleanExpr check_comm_100_1 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1"))));
        BooleanExpr check_comm_100_2 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))));
        BooleanExpr checkPrefixMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_MATCH));

        List<Statement> add_100_1 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:1")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_100_2 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:2")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> permit = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue));
        List<Statement> deny = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));

        RoutingPolicy alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,permit,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2,deny,permit))).build();

        imports.put(ALPHANODE,getPermitDefault(configs.get(ALPHANODE), IMPORT_POLICY_NAME));
        imports.put(BETANODE,getPermitDefault(configs.get(BETANODE), IMPORT_POLICY_NAME));
        imports.put(GAMMANODE,getPermitDefault(configs.get(GAMMANODE), IMPORT_POLICY_NAME));
        imports.put(DELTANODE,getPermitDefault(configs.get(DELTANODE), IMPORT_POLICY_NAME));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,getPermitDefault(configs.get(DELTANODE), EXPORT_POLICY_NAME));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }
    @Test
    public void noTaggingVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("12.0.0.1","alphaNode_2");
        Node BETANODE = new Node("12.0.0.2","betaNode_2");
        Node GAMMANODE = new Node("12.0.0.3","gammaNode_2");
        Node DELTANODE = new Node("12.0.0.4","deltaNode_2");
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = noTaggingNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        verifier.addProperty(DELTANODE,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        Optional<Location> o = verifier.bugLocator(ALPHANODE,result);
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
    }

    public Network wrongCheckNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE) {
         String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(configs,DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE,null,null)));

        BooleanExpr check_comm_100_1 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1"))));
        BooleanExpr check_comm_100_2 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))));
        BooleanExpr checkPrefixMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_MATCH));

        List<Statement> add_100_1 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:1")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_100_2 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("100:2")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> permit = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue));
        List<Statement> deny = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));

        RoutingPolicy alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2,permit,deny))).build();

        imports.put(ALPHANODE,getPermitDefault(configs.get(ALPHANODE), IMPORT_POLICY_NAME));
        imports.put(BETANODE,getPermitDefault(configs.get(BETANODE), IMPORT_POLICY_NAME));
        imports.put(GAMMANODE,getPermitDefault(configs.get(GAMMANODE), IMPORT_POLICY_NAME));
        imports.put(DELTANODE,getPermitDefault(configs.get(DELTANODE), IMPORT_POLICY_NAME));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,getPermitDefault(configs.get(DELTANODE), EXPORT_POLICY_NAME));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }
    @Test
    public void wrongCheckVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("13.0.0.1","alphaNode_3");
        Node BETANODE = new Node("13.0.0.2","betaNode_3");
        Node GAMMANODE = new Node("13.0.0.3","gammaNode_3");
        Node DELTANODE = new Node("13.0.0.4","deltaNode_3");
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = wrongCheckNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        verifier.addProperty(DELTANODE,property);
//        verifier.addProperty(ALPHANODE,new Invariant(net.tbdd));
        Verifier.VerificationResult result = verifier.run();
        List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
    }

    public Network wrongSetEntryNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE) {
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        CommunityMatchExpr comm_100_3 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:3$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2,"comm_100_3",comm_100_3));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))),"comm_100_3", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:3")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(configs,DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE,null,null)));

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
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_3,permit))).build();
        RoutingPolicy betaImport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(IMPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2,deny,permit))).build();

        imports.put(ALPHANODE,new RoutingPolicy("BLANK",configs.get(ALPHANODE)));
        imports.put(BETANODE,betaImport);
        imports.put(GAMMANODE,new RoutingPolicy("BLANK",configs.get(GAMMANODE)));
        imports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2")).add(RegexConstraint.parse("100:3")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }
    @Test
    public void wrongSetEntryVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("15.0.0.1","alphaNode");
        Node BETANODE = new Node("15.0.0.2","betaNode");
        Node GAMMANODE = new Node("15.0.0.3","gammaNode");
        Node DELTANODE = new Node("15.0.0.4","deltaNode");
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = wrongSetEntryNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        verifier.addProperty(DELTANODE,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
    }

    public Network wrongSetMiddleNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE) {
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        CommunityMatchExpr comm_100_3 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:3$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2,"comm_100_3",comm_100_3));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2"))),"comm_100_3", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:3")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess deltaBgp = getBgpProcess(configs,DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE,null,null)));

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
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_3,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2,deny,permit))).build();

        imports.put(ALPHANODE,new RoutingPolicy("BLANK",configs.get(ALPHANODE)));
        imports.put(BETANODE,new RoutingPolicy("BLANK",configs.get(BETANODE)));
        imports.put(GAMMANODE,new RoutingPolicy("BLANK",configs.get(GAMMANODE)));
        imports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2")).add(RegexConstraint.parse("100:3")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }
    @Test
    public void wrongSetMiddleVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("16.0.0.1","alphaNode");
        Node BETANODE = new Node("16.0.0.2","betaNode");
        Node GAMMANODE = new Node("16.0.0.3","gammaNode");
        Node DELTANODE = new Node("16.0.0.4","deltaNode");
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = wrongSetMiddleNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        verifier.addProperty(DELTANODE,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
    }

    public Network meshNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE, Node DELTANODE,
                               Node ALPHANODE_, Node BETANODE_, Node GAMMANODE_, Node DELTANODE_,
                               int faulty) {
        // String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();
        // Instantiate configurations
        CommunityMatchExpr comm_100_1 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:1$");
        CommunityMatchExpr comm_100_2 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^100:2$");
        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));

        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder deltaCB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE, deltaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        Configuration.Builder alpha_CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE_, alpha_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE_).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));
        configs.get(ALPHANODE_).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(ALPHANODE_).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder beta_CB = nf.configurationBuilder().setHostname(BETANODE.getName());
        configs.put(BETANODE_, beta_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE_).setCommunityMatchExprs(ImmutableMap.of("comm_100_1",comm_100_1));
        configs.get(BETANODE_).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_1", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:1")))));
        Configuration.Builder gamma_CB = nf.configurationBuilder().setHostname(GAMMANODE.getName());
        configs.put(GAMMANODE_, gamma_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE_).setCommunityMatchExprs(ImmutableMap.of("comm_100_2",comm_100_2));
        configs.get(GAMMANODE_).setCommunitySetMatchExprs(ImmutableMap.of("comm_100_2", new HasCommunity(new CommunityIs(StandardCommunity.parse("100:2")))));
        Configuration.Builder delta_CB = nf.configurationBuilder().setHostname(DELTANODE.getName());
        configs.put(DELTANODE_, delta_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME),
                BETANODE_.getIp(),getBgpActivePeerConfig(ALPHANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess alpha_Bgp = getBgpProcess(configs,ALPHANODE_);
        alpha_Bgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(ALPHANODE_,null,EXPORT_POLICY_NAME),
                BETANODE_.getIp(),getBgpActivePeerConfig(ALPHANODE_,null,EXPORT_POLICY_NAME)));

        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME),
                ALPHANODE_.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME),
                GAMMANODE_.getIp(),getBgpActivePeerConfig(BETANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess beta_Bgp = getBgpProcess(configs,BETANODE_);
        beta_Bgp.setNeighbors(ImmutableSortedMap.of(
                ALPHANODE.getIp(),getBgpActivePeerConfig(BETANODE_,null,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(BETANODE_,null,EXPORT_POLICY_NAME),
                ALPHANODE_.getIp(),getBgpActivePeerConfig(BETANODE_,null,EXPORT_POLICY_NAME),
                GAMMANODE_.getIp(),getBgpActivePeerConfig(BETANODE_,null,EXPORT_POLICY_NAME)));

        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                BETANODE_.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME),
                DELTANODE_.getIp(),getBgpActivePeerConfig(GAMMANODE,null,EXPORT_POLICY_NAME)));
        BgpProcess gamma_Bgp = getBgpProcess(configs,GAMMANODE_);
        gamma_Bgp.setNeighbors(ImmutableSortedMap.of(
                BETANODE.getIp(),getBgpActivePeerConfig(GAMMANODE_,null,EXPORT_POLICY_NAME),
                DELTANODE.getIp(),getBgpActivePeerConfig(GAMMANODE_,null,EXPORT_POLICY_NAME),
                BETANODE_.getIp(),getBgpActivePeerConfig(GAMMANODE_,null,EXPORT_POLICY_NAME),
                DELTANODE_.getIp(),getBgpActivePeerConfig(GAMMANODE_,null,EXPORT_POLICY_NAME)));

        BgpProcess deltaBgp = getBgpProcess(configs,DELTANODE);
        deltaBgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE,null,null),
                GAMMANODE_.getIp(),getBgpActivePeerConfig(DELTANODE,null,null)));
        BgpProcess delta_Bgp = getBgpProcess(configs,DELTANODE_);
        delta_Bgp.setNeighbors(ImmutableSortedMap.of(
                GAMMANODE.getIp(),getBgpActivePeerConfig(DELTANODE_,null,null),
                GAMMANODE_.getIp(),getBgpActivePeerConfig(DELTANODE_,null,null)));

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

        RoutingPolicy alphaExport;
        if (faulty == 2) {
            alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_3,permit))).build();
        } else {
            alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();
        }

        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(check_comm_100_2,deny,permit))).build();
        RoutingPolicy alpha_Export = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE_)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(new If(checkPrefixMatch,add_100_1,permit))).build();

        RoutingPolicy beta_Export;
        if (faulty == 1) {
            // CHANGING 100:2 --> 100:3
            beta_Export = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE_)).setName(EXPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_3,permit))).build();
        } else {
            beta_Export = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE_)).setName(EXPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(new If(check_comm_100_1,add_100_2,permit))).build();
        }

        RoutingPolicy gamma_Export;
        if (faulty == 2 || faulty == 3) {
            gamma_Export = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE_)).setName(EXPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(new If(check_comm_100_1,deny,permit))).build();
        } else {
            gamma_Export = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE_)).setName(EXPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(new If(check_comm_100_2,deny,permit))).build();
        }

        imports.put(ALPHANODE,new RoutingPolicy("BLANK",configs.get(ALPHANODE)));
        imports.put(BETANODE,new RoutingPolicy("BLANK",configs.get(BETANODE)));
        imports.put(GAMMANODE,new RoutingPolicy("BLANK",configs.get(GAMMANODE)));
        imports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));
        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);
        exports.put(DELTANODE,new RoutingPolicy("BLANK",configs.get(DELTANODE)));

        imports.put(ALPHANODE_,new RoutingPolicy("BLANK",configs.get(ALPHANODE_)));
        imports.put(BETANODE_,new RoutingPolicy("BLANK",configs.get(BETANODE_)));
        imports.put(GAMMANODE_,new RoutingPolicy("BLANK",configs.get(GAMMANODE_)));
        imports.put(DELTANODE_,new RoutingPolicy("BLANK",configs.get(DELTANODE_)));
        exports.put(ALPHANODE_,alpha_Export);
        exports.put(BETANODE_,beta_Export);
        exports.put(GAMMANODE_,gamma_Export);
        exports.put(DELTANODE_,new RoutingPolicy("BLANK",configs.get(DELTANODE_)));

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("100:1")).add(RegexConstraint.parse("100:2"))
                .add(RegexConstraint.parse("100:3")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }
    @Test
    public void meshVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("100.0.0.1","alphaNode_a");
        Node BETANODE = new Node("100.0.0.2","betaNode_a");
        Node GAMMANODE = new Node("100.0.0.3","gammaNode_a");
        Node DELTANODE = new Node("100.0.0.4","deltaNode_a");
        Node ALPHANODE_ = new Node("100.0.0.11","alphaNode_b");
        Node BETANODE_ = new Node("100.0.0.22","betaNode_b");
        Node GAMMANODE_ = new Node("100.0.0.33","gammaNode_b");
        Node DELTANODE_ = new Node("100.0.0.44","deltaNode_b");

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = meshNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE,ALPHANODE_,BETANODE_,GAMMANODE_,DELTANODE_,0);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        Invariant property_ = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE_)));
        verifier.addProperty(DELTANODE,property);
        verifier.addProperty(DELTANODE_,property_);
        Verifier.VerificationResult result = verifier.run();
        assertTrue(result.verified());
        Collection<Location> trues = result.inferredTrueAt();
        Map<Location,Invariant> inferred = result.invariants();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        assertEquals(inferred.get(ALPHANODE),inferred.get(ALPHANODE_));
        assertEquals(inferred.get(BETANODE),inferred.get(BETANODE_));
        assertEquals(inferred.get(GAMMANODE),inferred.get(GAMMANODE_));
        assertEquals(inferred.get(DELTANODE),inferred.get(DELTANODE_));

        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE,ALPHANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE,GAMMANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE_)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE,GAMMANODE_)));

        assertTrue(result.inferredTrue());
    }

    @Test
    public void faultyMeshVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("101.0.0.1","alphaNode_a");
        Node BETANODE = new Node("101.0.0.2","betaNode_a");
        Node GAMMANODE = new Node("101.0.0.3","gammaNode_a");
        Node DELTANODE = new Node("101.0.0.4","deltaNode_a");
        Node ALPHANODE_ = new Node("101.0.0.11","alphaNode_b");
        Node BETANODE_ = new Node("101.0.0.22","betaNode_b");
        Node GAMMANODE_ = new Node("101.0.0.33","gammaNode_b");
        Node DELTANODE_ = new Node("100.1.0.44","deltaNode_b");

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = meshNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE,ALPHANODE_,BETANODE_,GAMMANODE_,DELTANODE_,1);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        Invariant property_ = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE_)));
        verifier.addProperty(DELTANODE,property);
        verifier.addProperty(DELTANODE_,property_);
        Verifier.VerificationResult result = verifier.run();
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
        Collection<Location> trues = result.inferredTrueAt();
        Map<Location,Invariant> inferred = result.invariants();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        // Even in buggy mesh -- the equalities are still upheld
        assertEquals(inferred.get(ALPHANODE),inferred.get(ALPHANODE_));
        assertEquals(inferred.get(BETANODE),inferred.get(BETANODE_));
        assertEquals(inferred.get(GAMMANODE),inferred.get(GAMMANODE_));
        assertEquals(inferred.get(DELTANODE),inferred.get(DELTANODE_));

        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE,ALPHANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE,GAMMANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE_)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE,GAMMANODE_)));
    }

    @Test
    public void faultyMeshDeny2VerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("97.0.0.1","alphaNode_a");
        Node BETANODE = new Node("97.0.0.2","betaNode_a");
        Node GAMMANODE = new Node("97.0.0.3","gammaNode_a");
        Node DELTANODE = new Node("97.0.0.4","deltaNode_a");
        Node ALPHANODE_ = new Node("97.0.0.11","alphaNode_b");
        Node BETANODE_ = new Node("97.0.0.22","betaNode_b");
        Node GAMMANODE_ = new Node("97.0.0.33","gammaNode_b");
        Node DELTANODE_ = new Node("97.1.0.44","deltaNode_b");

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = meshNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE,ALPHANODE_,BETANODE_,GAMMANODE_,DELTANODE_,2);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        Invariant property_ = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE_)));
        verifier.addProperty(DELTANODE,property);
        verifier.addProperty(DELTANODE_,property_);
        Verifier.VerificationResult result = verifier.run();
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
        Collection<Location> trues = result.inferredTrueAt();
        Map<Location,Invariant> inferred = result.invariants();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        // Even in buggy mesh -- the equalities are still upheld
        assertEquals(inferred.get(ALPHANODE),inferred.get(ALPHANODE_));
        assertEquals(inferred.get(BETANODE),inferred.get(BETANODE_));
        //assertEquals(inferred.get(GAMMANODE),inferred.get(GAMMANODE_)); --> not equal
        assertEquals(inferred.get(DELTANODE),inferred.get(DELTANODE_));

        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE,ALPHANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE_)),inferred.get(new Edge(BETANODE_,GAMMANODE_)));
        //assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE,GAMMANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE_)),inferred.get(new Edge(DELTANODE_,GAMMANODE_)));
        //assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE,GAMMANODE_)));
    }

    @Test
    public void faultyMeshDenyVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("98.0.0.1","alphaNode_a");
        Node BETANODE = new Node("98.0.0.2","betaNode_a");
        Node GAMMANODE = new Node("98.0.0.3","gammaNode_a");
        Node DELTANODE = new Node("98.0.0.4","deltaNode_a");
        Node ALPHANODE_ = new Node("98.0.0.11","alphaNode_b");
        Node BETANODE_ = new Node("98.0.0.22","betaNode_b");
        Node GAMMANODE_ = new Node("98.0.0.33","gammaNode_b");
        Node DELTANODE_ = new Node("98.1.0.44","deltaNode_b");

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = meshNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE,ALPHANODE_,BETANODE_,GAMMANODE_,DELTANODE_,3);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        Invariant property_ = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE_)));
        verifier.addProperty(DELTANODE,property);
        verifier.addProperty(DELTANODE_,property_);
        Verifier.VerificationResult result = verifier.run();
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
        Collection<Location> trues = result.inferredTrueAt();
        Map<Location,Invariant> inferred = result.invariants();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        // Even in buggy mesh -- the equalities are still upheld
        assertEquals(inferred.get(ALPHANODE),inferred.get(ALPHANODE_));
        assertEquals(inferred.get(BETANODE),inferred.get(BETANODE_));
        //assertEquals(inferred.get(GAMMANODE),inferred.get(GAMMANODE_)); --> not equal
        assertEquals(inferred.get(DELTANODE),inferred.get(DELTANODE_));

        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE,ALPHANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE_)),inferred.get(new Edge(BETANODE_,GAMMANODE_)));
        //assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE,GAMMANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE_)),inferred.get(new Edge(DELTANODE_,GAMMANODE_)));
        //assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE,GAMMANODE_)));
    }

    @Test
    public void faultyMeshConflictTargetVerificationTest() {
        List<String> prefixesConsidered = ImmutableList.of("25.13.0.0/16");
        Node ALPHANODE = new Node("99.0.0.1","alphaNode_a");
        Node BETANODE = new Node("99.0.0.2","betaNode_a");
        Node GAMMANODE = new Node("99.0.0.3","gammaNode_a");
        Node DELTANODE = new Node("99.0.0.4","deltaNode_a");
        Node ALPHANODE_ = new Node("99.0.0.11","alphaNode_b");
        Node BETANODE_ = new Node("99.0.0.22","betaNode_b");
        Node GAMMANODE_ = new Node("99.0.0.33","gammaNode_b");
        Node DELTANODE_ = new Node("99.1.0.44","deltaNode_b");

        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")));

        Network net = meshNetwork(ALPHANODE,BETANODE,GAMMANODE,DELTANODE,ALPHANODE_,BETANODE_,GAMMANODE_,DELTANODE_,0);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE)));
        Invariant property_ = new Invariant(net.tbdd,Invariant.clauseBuilder().matchPrefix(PREFIX).build(net.tbdd,net.imports.get(DELTANODE_)));
        verifier.addProperty(DELTANODE,property);
        verifier.addProperty(DELTANODE_,property_);
        Verifier.VerificationResult result = verifier.run();
        assertTrue(result.verified());
        assertFalse(result.inferredTrue());
        Collection<Location> trues = result.inferredTrueAt();
        Map<Location,Invariant> inferred = result.invariants();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        // Even in buggy mesh -- the equalities are still upheld
        assertEquals(inferred.get(ALPHANODE),inferred.get(ALPHANODE_));
        assertEquals(inferred.get(BETANODE),inferred.get(BETANODE_));
        assertEquals(inferred.get(GAMMANODE),inferred.get(GAMMANODE_));
        // assertEquals(inferred.get(DELTANODE),inferred.get(DELTANODE_)); --> not equal by design

        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(ALPHANODE,BETANODE)),inferred.get(new Edge(ALPHANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE_,ALPHANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,ALPHANODE)),inferred.get(new Edge(BETANODE,ALPHANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE_)));
        assertEquals(inferred.get(new Edge(GAMMANODE,BETANODE)),inferred.get(new Edge(GAMMANODE_,BETANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE_,GAMMANODE_)));
        assertEquals(inferred.get(new Edge(BETANODE,GAMMANODE)),inferred.get(new Edge(BETANODE,GAMMANODE_)));

        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE)));
        assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE_)),inferred.get(new Edge(GAMMANODE_,DELTANODE_)));
        //assertEquals(inferred.get(new Edge(GAMMANODE,DELTANODE)),inferred.get(new Edge(GAMMANODE_,DELTANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE_,GAMMANODE_)));
        assertEquals(inferred.get(new Edge(DELTANODE,GAMMANODE)),inferred.get(new Edge(DELTANODE,GAMMANODE_)));
    }

    public Network prongedNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE,
                                  Node NODE_1, Node NODE_2, Node NODE_3, Node NODE_4,
                                  int faulty) {
        List<String> prefixesConsidered = ImmutableList.of("24.4.0.0/16","36.6.0.0/16","42.7.0.0/16");
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_A_MATCH = "prefixAMatch";
        String PREFIX_B_MATCH = "prefixBMatch";
        String PREFIX_C_MATCH = "prefixCMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        // Instantiate configurations
        CommunityMatchExpr comm_10_10 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^10:10$");
        CommunityMatchExpr comm_10_20 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^10:20$");
        CommunityMatchExpr comm_10_30 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^10:30$");
        CommunityMatchExpr comm_20_10 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^20:10$");
        CommunityMatchExpr comm_20_20 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^20:20$");
        CommunityMatchExpr comm_20_30 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^20:30$");
        RouteFilterList prefixAMatch = new RouteFilterList(PREFIX_A_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("24.4.0.0/16")))));
        RouteFilterList prefixBMatch = new RouteFilterList(PREFIX_B_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("42.7.0.0/16")))));
        RouteFilterList prefixCMatch = new RouteFilterList(PREFIX_C_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("36.6.0.0/16")))));

        // Set entry configs which don't do anything besides permit or deny
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Set internal node configs
        Configuration.Builder node1CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_1, node1CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(NODE_1).setRouteFilterLists(ImmutableMap.of(
                PREFIX_A_MATCH,prefixAMatch,PREFIX_B_MATCH,prefixBMatch,PREFIX_C_MATCH,prefixCMatch));
        configs.get(NODE_1).setCommunityMatchExprs(ImmutableMap.of(
                "comm_10_10",comm_10_10,"comm_10_20",comm_10_20,"comm_10_30",comm_10_30));
        configs.get(NODE_1).setCommunitySetMatchExprs(ImmutableMap.of(
                "comm_10_10", new HasCommunity(comm_10_10),"comm_10_20", new HasCommunity(comm_10_20),"comm_10_30", new HasCommunity(comm_10_30)));

        Configuration.Builder node2CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_2, node2CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(NODE_2).setRouteFilterLists(ImmutableMap.of(
                PREFIX_A_MATCH,prefixAMatch,PREFIX_B_MATCH,prefixBMatch,PREFIX_C_MATCH,prefixCMatch));
        configs.get(NODE_2).setCommunityMatchExprs(ImmutableMap.of(
                "comm_20_10",comm_20_10,"comm_20_20",comm_20_20,"comm_20_30",comm_20_30));
        configs.get(NODE_2).setCommunitySetMatchExprs(ImmutableMap.of(
                "comm_20_10", new HasCommunity(comm_20_10),"comm_20_20", new HasCommunity(comm_20_20),"comm_20_30", new HasCommunity(comm_20_30)));

        Configuration.Builder node3CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_3, node3CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(NODE_3).setCommunityMatchExprs(ImmutableMap.of(
                "comm_10_10",comm_10_10,"comm_10_20",comm_10_20,"comm_10_30",comm_10_30,
                "comm_20_10",comm_20_10,"comm_20_20",comm_20_20,"comm_20_30",comm_20_30));
        configs.get(NODE_3).setCommunitySetMatchExprs(ImmutableMap.of(
                "comm_10_10", new HasCommunity(comm_10_10),"comm_10_20", new HasCommunity(comm_10_20),"comm_10_30", new HasCommunity(comm_10_30),
                "comm_20_10", new HasCommunity(comm_20_10),"comm_20_20", new HasCommunity(comm_20_20),"comm_20_30", new HasCommunity(comm_20_30)));

        Configuration.Builder node4CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_4, node4CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP Processes (entry nodes)
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(ALPHANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(ALPHANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(GAMMANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(GAMMANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Create BGP Processes (internal nodes)
        BgpProcess node1Bgp = getBgpProcess(configs,NODE_1);
        node1Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                ALPHANODE.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                BETANODE.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node2Bgp = getBgpProcess(configs,NODE_2);
        node2Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                ALPHANODE.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                BETANODE.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node3Bgp = getBgpProcess(configs,NODE_3);
        node3Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_4.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node4Bgp = getBgpProcess(configs,NODE_4);
        node4Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_4,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        BooleanExpr check_comm_10_10 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("10:10"))));
        BooleanExpr check_comm_10_20 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("10:20"))));
        BooleanExpr check_comm_10_30 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("10:30"))));
        BooleanExpr check_comm_20_10 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("20:10"))));
        BooleanExpr check_comm_20_20 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("20:20"))));
        BooleanExpr check_comm_20_30 = new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse("20:30"))));

        BooleanExpr checkPrefixAMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_A_MATCH));
        BooleanExpr checkPrefixBMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_B_MATCH));
        BooleanExpr checkPrefixCMatch = new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(PREFIX_C_MATCH));

        List<Statement> add_10_10 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("10:10")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_10_20 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("10:20")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_10_30 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("10:30")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_20_10 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("20:10")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_20_20 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("20:20")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> add_20_30 = ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse("20:30")))),
                new Statements.StaticStatement(Statements.ReturnTrue));

        List<Statement> permit = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue));
        List<Statement> deny = ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));

        RoutingPolicy node1Import = nf.routingPolicyBuilder().setOwner(configs.get(NODE_1)).setName(IMPORT_POLICY_NAME)
                    .setStatements(
                            ImmutableList.of(new If(checkPrefixAMatch, add_10_10,
                                    ImmutableList.of(new If(checkPrefixBMatch, add_10_20,
                                            ImmutableList.of(new If(checkPrefixCMatch,add_10_30,permit))))))).build();
        RoutingPolicy node1Export = getPermitDefault(configs.get(NODE_1),EXPORT_POLICY_NAME);

        RoutingPolicy node2Import = nf.routingPolicyBuilder().setOwner(configs.get(NODE_2)).setName(IMPORT_POLICY_NAME)
                .setStatements(
                        ImmutableList.of(new If(checkPrefixAMatch, add_20_10,
                                ImmutableList.of(new If(checkPrefixBMatch, add_20_20,
                                        ImmutableList.of(new If(checkPrefixCMatch,add_20_30,permit))))))).build();
        RoutingPolicy node2Export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_2)).setName(EXPORT_POLICY_NAME)
                .setStatements(
                        ImmutableList.of(new If(check_comm_20_10, permit,
                                        ImmutableList.of(new If(check_comm_20_20,permit,deny))))).build();

        RoutingPolicy node3Import = getPermitDefault(configs.get(NODE_3),IMPORT_POLICY_NAME);
        RoutingPolicy node3Export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_3)).setName(EXPORT_POLICY_NAME)
                .setStatements(
                        ImmutableList.of(new If(check_comm_10_10, deny,
                                ImmutableList.of(new If(check_comm_10_30, deny,
                                        ImmutableList.of(new If(check_comm_20_10,deny,
                                                ImmutableList.of(new If(check_comm_20_30,deny, permit))))))))).build();

        RoutingPolicy node4Import = getPermitDefault(configs.get(NODE_4),IMPORT_POLICY_NAME);
        RoutingPolicy node4Export = getPermitDefault(configs.get(NODE_4),EXPORT_POLICY_NAME);

        // entry node policies
        imports.put(ALPHANODE,getPermitDefault(configs.get(ALPHANODE),IMPORT_POLICY_NAME));
        exports.put(ALPHANODE,getPermitDefault(configs.get(ALPHANODE),EXPORT_POLICY_NAME));
        imports.put(BETANODE,getPermitDefault(configs.get(BETANODE),IMPORT_POLICY_NAME));
        exports.put(BETANODE,getPermitDefault(configs.get(BETANODE),EXPORT_POLICY_NAME));
        imports.put(GAMMANODE,getPermitDefault(configs.get(GAMMANODE),IMPORT_POLICY_NAME));
        exports.put(GAMMANODE,getPermitDefault(configs.get(GAMMANODE),EXPORT_POLICY_NAME));

        // internal node policies
        imports.put(NODE_1, node1Import);
        imports.put(NODE_2, node2Import);
        imports.put(NODE_3, node3Import);
        imports.put(NODE_4, node4Import);

        exports.put(NODE_1, node1Export);
        exports.put(NODE_2, node2Export);
        exports.put(NODE_3, node3Export);
        exports.put(NODE_4, node4Export);

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("10:10")).add(RegexConstraint.parse("20:10"))
                .add(RegexConstraint.parse("10:20")).add(RegexConstraint.parse("20:20"))
                .add(RegexConstraint.parse("10:30")).add(RegexConstraint.parse("20:30")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }

    @Test
    public void prongedNetworkVerificationTest() {
        Node ALPHANODE = new Node("211.0.0.1","alphaNode_entry");
        Node BETANODE = new Node("211.0.0.2","betaNode_entry");
        Node GAMMANODE = new Node("211.0.0.3","gammaNode_entry");
        Node NODE_1 = new Node("37.0.0.1","node_1_one");
        Node NODE_2 = new Node("37.0.0.2","node_2_two");
        Node NODE_3 = new Node("37.0.0.3","node_3_three");
        Node NODE_4 = new Node("37.0.0.4","node_4_four");

        PrefixSpace PREFIX_A = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("24.4.0.0/16")));
        PrefixSpace PREFIX_B = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("42.7.0.0/16")));
        PrefixSpace PREFIX_C = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse("36.6.0.0/16")));

        Network net = prongedNetwork(ALPHANODE,BETANODE,GAMMANODE,NODE_1,NODE_2,NODE_3,NODE_4,0);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant.ClauseBuilder avoidA_avoidC = Invariant.clauseBuilder().avoidPrefix(PREFIX_C).avoidPrefix(PREFIX_A);
        Invariant.ClauseBuilder matchB_avoidA = Invariant.clauseBuilder().avoidPrefix(PREFIX_A).matchPrefix(PREFIX_B);
        Invariant property = Invariant.builder().addClause(avoidA_avoidC).addClause(matchB_avoidA).build(net.tbdd,net.imports.get(NODE_4));
        verifier.addProperty(NODE_4,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> ppp = result.dirtyReadableResults(ImmutableList.of("24.4.0.0/16","36.6.0.0/16","42.7.0.0/16"));
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
    }

    public Network commBasedProngedNetwork(Node ALPHANODE, Node BETANODE, Node GAMMANODE,
                                  Node NODE_1, Node NODE_2, Node NODE_3, Node NODE_4,
                                  int faulty) {
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        // Instantiate configurations
        CommunityMatchExpr comm_1_10 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^1:10$");
        CommunityMatchExpr comm_1_20 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^1:20$");
        CommunityMatchExpr comm_1_30 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^1:30$");
        CommunityMatchExpr comm_10_10 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^10:10$");
        CommunityMatchExpr comm_10_20 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^10:20$");
        CommunityMatchExpr comm_10_30 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^10:30$");
        CommunityMatchExpr comm_20_10 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^20:10$");
        CommunityMatchExpr comm_20_20 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^20:20$");
        CommunityMatchExpr comm_20_30 = new CommunityMatchRegex(ColonSeparatedRendering.instance(),"^20:30$");

        //String PREFIX_A_MATCH = "prefixAMatch";
        //String PREFIX_B_MATCH = "prefixBMatch";
        //String PREFIX_C_MATCH = "prefixCMatch";
        //RouteFilterList prefixAMatch = new RouteFilterList(PREFIX_A_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("24.4.0.0/16")))));
        //RouteFilterList prefixBMatch = new RouteFilterList(PREFIX_B_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("42.7.0.0/16")))));
        //RouteFilterList prefixCMatch = new RouteFilterList(PREFIX_C_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("36.6.0.0/16")))));

        // Set entry configs which don't do anything besides permit or deny
        Configuration.Builder alphaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(ALPHANODE, alphaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(ALPHANODE).setCommunityMatchExprs(ImmutableMap.of("comm_1_10",comm_1_10));
        configs.get(ALPHANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_1_10", new HasCommunity(comm_1_10)));

        Configuration.Builder betaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(BETANODE, betaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(BETANODE).setCommunityMatchExprs(ImmutableMap.of("comm_1_20",comm_1_20));
        configs.get(BETANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_1_20", new HasCommunity(comm_1_20)));

        Configuration.Builder gammaCB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(GAMMANODE, gammaCB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(GAMMANODE).setCommunityMatchExprs(ImmutableMap.of("comm_1_30",comm_1_30));
        configs.get(GAMMANODE).setCommunitySetMatchExprs(ImmutableMap.of("comm_1_30", new HasCommunity(comm_1_30)));

        // Set internal node configs
        Configuration.Builder node1CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_1, node1CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        //configs.get(NODE_1).setRouteFilterLists(ImmutableMap.of(
                //PREFIX_A_MATCH,prefixAMatch,PREFIX_B_MATCH,prefixBMatch,PREFIX_C_MATCH,prefixCMatch));
        configs.get(NODE_1).setCommunityMatchExprs(ImmutableMap.of(
                "comm_1_10",comm_1_10,"comm_1_20",comm_1_20,"comm_1_30",comm_1_30,
                "comm_10_10",comm_10_10,"comm_10_20",comm_10_20,"comm_10_30",comm_10_30));
        configs.get(NODE_1).setCommunitySetMatchExprs(ImmutableMap.of(
                "comm_1_10", new HasCommunity(comm_1_10),"comm_1_20", new HasCommunity(comm_1_20),"comm_1_30", new HasCommunity(comm_1_30),
                "comm_10_10", new HasCommunity(comm_10_10),"comm_10_20", new HasCommunity(comm_10_20),"comm_10_30", new HasCommunity(comm_10_30)));

        Configuration.Builder node2CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_2, node2CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        //configs.get(NODE_2).setRouteFilterLists(ImmutableMap.of(
                //PREFIX_A_MATCH,prefixAMatch,PREFIX_B_MATCH,prefixBMatch,PREFIX_C_MATCH,prefixCMatch));
        configs.get(NODE_2).setCommunityMatchExprs(ImmutableMap.of(
                "comm_1_10",comm_1_10,"comm_1_20",comm_1_20,"comm_1_30",comm_1_30,
                "comm_20_10",comm_20_10,"comm_20_20",comm_20_20,"comm_20_30",comm_20_30));
        configs.get(NODE_2).setCommunitySetMatchExprs(ImmutableMap.of(
                "comm_1_10", new HasCommunity(comm_1_10),"comm_1_20", new HasCommunity(comm_1_20),"comm_1_30", new HasCommunity(comm_1_30),
                "comm_20_10", new HasCommunity(comm_20_10),"comm_20_20", new HasCommunity(comm_20_20),"comm_20_30", new HasCommunity(comm_20_30)));

        Configuration.Builder node3CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_3, node3CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        configs.get(NODE_3).setCommunityMatchExprs(ImmutableMap.of(
                "comm_10_10",comm_10_10,"comm_10_20",comm_10_20,"comm_10_30",comm_10_30,
                "comm_20_10",comm_20_10,"comm_20_20",comm_20_20,"comm_20_30",comm_20_30));
        configs.get(NODE_3).setCommunitySetMatchExprs(ImmutableMap.of(
                "comm_10_10", new HasCommunity(comm_10_10),"comm_10_20", new HasCommunity(comm_10_20),"comm_10_30", new HasCommunity(comm_10_30),
                "comm_20_10", new HasCommunity(comm_20_10),"comm_20_20", new HasCommunity(comm_20_20),"comm_20_30", new HasCommunity(comm_20_30)));

        Configuration.Builder node4CB = nf.configurationBuilder().setHostname(ALPHANODE.getName());
        configs.put(NODE_4, node4CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP Processes (entry nodes)
        BgpProcess alphaBgp = getBgpProcess(configs,ALPHANODE);
        alphaBgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(ALPHANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(ALPHANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess betaBgp = getBgpProcess(configs,BETANODE);
        betaBgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(BETANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess gammaBgp = getBgpProcess(configs,GAMMANODE);
        gammaBgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(GAMMANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(GAMMANODE,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Create BGP Processes (internal nodes)
        BgpProcess node1Bgp = getBgpProcess(configs,NODE_1);
        node1Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                ALPHANODE.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                BETANODE.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(NODE_1,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node2Bgp = getBgpProcess(configs,NODE_2);
        node2Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                ALPHANODE.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                BETANODE.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                GAMMANODE.getIp(),getBgpActivePeerConfig(NODE_2,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node3Bgp = getBgpProcess(configs,NODE_3);
        node3Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_1.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_4.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node4Bgp = getBgpProcess(configs,NODE_4);
        node4Bgp.setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_4,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        RoutingPolicy node1Import = nf.routingPolicyBuilder().setOwner(configs.get(NODE_1)).setName(IMPORT_POLICY_NAME)
                .setStatements(
                        ImmutableList.of(new If(checkForCommunity("1:10"), addToCommunities("10:10"),
                                ImmutableList.of(new If(checkForCommunity("1:20"), addToCommunities("10:20"),
                                        ImmutableList.of(new If(checkForCommunity("1:30"),addToCommunities("10:30"),permitRoute(true)))))))).build();
        RoutingPolicy node1Export = getPermitDefault(configs.get(NODE_1),EXPORT_POLICY_NAME);

        RoutingPolicy node2Import = nf.routingPolicyBuilder().setOwner(configs.get(NODE_2)).setName(IMPORT_POLICY_NAME)
                .setStatements(
                        ImmutableList.of(new If(checkForCommunity("1:10"), faulty == 1 ? addToCommunities("20:20") : addToCommunities("20:10"),
                                ImmutableList.of(new If(checkForCommunity("1:20"), faulty == 1 ? addToCommunities("20:10") : addToCommunities("20:20"),
                                        ImmutableList.of(new If(checkForCommunity("1:30"),addToCommunities("20:30"),permitRoute(true)))))))).build();
        RoutingPolicy node2Export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_2)).setName(EXPORT_POLICY_NAME)
                .setStatements(
                        ImmutableList.of(new If(checkForCommunity("20:10"), permitRoute(true),
                                ImmutableList.of(new If(checkForCommunity("20:20"),permitRoute(true),permitRoute(false)))))).build();

        RoutingPolicy node3Import = getPermitDefault(configs.get(NODE_3),IMPORT_POLICY_NAME);
        RoutingPolicy node3Export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_3)).setName(EXPORT_POLICY_NAME)
                .setStatements(
                        ImmutableList.of(new If(checkForCommunity("10:10"), permitRoute(false),
                                ImmutableList.of(new If(checkForCommunity("10:30"), permitRoute(faulty == 2),
                                        ImmutableList.of(new If(checkForCommunity("20:10"),permitRoute(false),
                                                ImmutableList.of(new If(checkForCommunity("20:30"),permitRoute(false), permitRoute(true)))))))))).build();

        RoutingPolicy node4Import = getPermitDefault(configs.get(NODE_4),IMPORT_POLICY_NAME);
        RoutingPolicy node4Export = getPermitDefault(configs.get(NODE_4),EXPORT_POLICY_NAME);

        RoutingPolicy alphaExport = nf.routingPolicyBuilder().setOwner(configs.get(ALPHANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(replaceCommunities("1:10")).build();
        RoutingPolicy betaExport = nf.routingPolicyBuilder().setOwner(configs.get(BETANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(replaceCommunities("1:20")).build();
        RoutingPolicy gammaExport = nf.routingPolicyBuilder().setOwner(configs.get(GAMMANODE)).setName(EXPORT_POLICY_NAME)
                .setStatements(replaceCommunities("1:30")).build();

        // entry node policies
        imports.put(ALPHANODE,getPermitDefault(configs.get(ALPHANODE),IMPORT_POLICY_NAME));
        imports.put(BETANODE,getPermitDefault(configs.get(BETANODE),IMPORT_POLICY_NAME));
        imports.put(GAMMANODE,getPermitDefault(configs.get(GAMMANODE),IMPORT_POLICY_NAME));

        exports.put(ALPHANODE,alphaExport);
        exports.put(BETANODE,betaExport);
        exports.put(GAMMANODE,gammaExport);

        // internal node policies
        imports.put(NODE_1, node1Import);
        imports.put(NODE_2, node2Import);
        imports.put(NODE_3, node3Import);
        imports.put(NODE_4, node4Import);

        exports.put(NODE_1, node1Export);
        exports.put(NODE_2, node2Export);
        exports.put(NODE_3, node3Export);
        exports.put(NODE_4, node4Export);

        Set<RegexConstraint> communityRegexes = ImmutableSet.<RegexConstraint>builder()
                .add(RegexConstraint.parse("1:10")).add(RegexConstraint.parse("1:20")).add(RegexConstraint.parse("1:30"))
                .add(RegexConstraint.parse("10:10")).add(RegexConstraint.parse("20:10"))
                .add(RegexConstraint.parse("10:20")).add(RegexConstraint.parse("20:20"))
                .add(RegexConstraint.parse("10:30")).add(RegexConstraint.parse("20:30")).build();
        ConfigAtomicPredicates configAPs = getConfigAtomicPredicates(configs.values(), communityRegexes);
        TransferBDD tbdd = new TransferBDD(configAPs);

        return new Network(tbdd,configs,imports,exports);
    }

    @Test
    public void commBasedProngedNetworkVerificationTest() {
        Node ALPHANODE = new Node("241.0.0.1","alphaNode_entry");
        Node BETANODE = new Node("241.0.0.2","betaNode_entry");
        Node GAMMANODE = new Node("241.0.0.3","gammaNode_entry");
        Node NODE_1 = new Node("47.0.0.1","node_1_one");
        Node NODE_2 = new Node("47.0.0.2","node_2_two");
        Node NODE_3 = new Node("47.0.0.3","node_3_three");
        Node NODE_4 = new Node("47.0.0.4","node_4_four");

        RegexConstraint not_comm_1_10 = RegexConstraint.parse("!1:10");
        RegexConstraint not_comm_1_30 = RegexConstraint.parse("!1:30");
        Invariant.ClauseBuilder both = Invariant.createClause(null,null,new RegexConstraints(List.of(not_comm_1_10,not_comm_1_30)));

        Network net = commBasedProngedNetwork(ALPHANODE,BETANODE,GAMMANODE,NODE_1,NODE_2,NODE_3,NODE_4,0);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = Invariant.builder().addClause(both).build(net.tbdd,net.imports.get(NODE_4));
        verifier.addProperty(NODE_4,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> p = result.dirtyReadableResults(ImmutableList.of());
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
    }

    @Test
    public void commBasedProngedFault1VerificationTest() {
        Node ALPHANODE = new Node("241.0.0.1","alphaNode_entry");
        Node BETANODE = new Node("241.0.0.2","betaNode_entry");
        Node GAMMANODE = new Node("241.0.0.3","gammaNode_entry");
        Node NODE_1 = new Node("47.0.0.1","node_1_one");
        Node NODE_2 = new Node("47.0.0.2","node_2_two");
        Node NODE_3 = new Node("47.0.0.3","node_3_three");
        Node NODE_4 = new Node("47.0.0.4","node_4_four");

        RegexConstraint not_comm_1_10 = RegexConstraint.parse("!1:10");
        RegexConstraint not_comm_1_30 = RegexConstraint.parse("!1:30");
        Invariant.ClauseBuilder both = Invariant.createClause(null,null,new RegexConstraints(List.of(not_comm_1_10,not_comm_1_30)));

        Network net = commBasedProngedNetwork(ALPHANODE,BETANODE,GAMMANODE,NODE_1,NODE_2,NODE_3,NODE_4,1);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = Invariant.builder().addClause(both).build(net.tbdd,net.imports.get(NODE_4));

        verifier.addProperty(NODE_4,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> p = result.dirtyReadableResults(ImmutableList.of());
        assertFalse(result.verified());
    }

    @Test
    public void commBasedProngedFault2VerificationTest() {
        Node ALPHANODE = new Node("241.0.0.1","alphaNode_entry");
        Node BETANODE = new Node("241.0.0.2","betaNode_entry");
        Node GAMMANODE = new Node("241.0.0.3","gammaNode_entry");
        Node NODE_1 = new Node("47.0.0.1","node_1_one");
        Node NODE_2 = new Node("47.0.0.2","node_2_two");
        Node NODE_3 = new Node("47.0.0.3","node_3_three");
        Node NODE_4 = new Node("47.0.0.4","node_4_four");

        RegexConstraint not_comm_1_10 = RegexConstraint.parse("!1:10");
        RegexConstraint not_comm_1_30 = RegexConstraint.parse("!1:30");
        Invariant.ClauseBuilder both = Invariant.createClause(null,null,new RegexConstraints(List.of(not_comm_1_10,not_comm_1_30)));

        Network net = commBasedProngedNetwork(ALPHANODE,BETANODE,GAMMANODE,NODE_1,NODE_2,NODE_3,NODE_4,2);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = Invariant.builder().addClause(both).build(net.tbdd,net.imports.get(NODE_4));

        verifier.addProperty(NODE_4,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> p = result.dirtyReadableResults(ImmutableList.of());
        assertFalse(result.verified());
    }

    public Network twoPathNetwork(Node NODE_1A, Node NODE_1B,
                                  Node NODE_2A, Node NODE_2B,
                                  Node NODE_3, Node NODE_4,
                                  int faulty) {
        // Initialize constants
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

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
        Configuration.Builder node1A_CB = nf.configurationBuilder().setHostname(NODE_1A.getName());
        configs.put(NODE_1A, node1A_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        includeCommunities(configs.get(NODE_1A),regex_comm_100_1);
        configs.get(NODE_1A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        Configuration.Builder node1B_CB = nf.configurationBuilder().setHostname(NODE_1B.getName());
        configs.put(NODE_1B, node1B_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        includeCommunities(configs.get(NODE_1B),regex_comm_100_1);
        configs.get(NODE_1B).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        Configuration.Builder node2A_CB = nf.configurationBuilder().setHostname(NODE_2A.getName());
        configs.put(NODE_2A, node2A_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        includeCommunities(configs.get(NODE_2A),regex_comm_100_1,regex_comm_100_2);

        Configuration.Builder node2B_CB = nf.configurationBuilder().setHostname(NODE_2B.getName());
        configs.put(NODE_2B, node2B_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        if (faulty == 1 || faulty == 2) {
            includeCommunities(configs.get(NODE_2B),regex_comm_100_1,regex_comm_100_3);
        } else {
            includeCommunities(configs.get(NODE_2B),regex_comm_100_1,regex_comm_100_2);
        }

        Configuration.Builder node3_CB = nf.configurationBuilder().setHostname(NODE_3.getName());
        configs.put(NODE_3, node3_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        if (faulty == 2) {
            includeCommunities(configs.get(NODE_3),regex_comm_100_2,regex_comm_100_3);
        } else {
            includeCommunities(configs.get(NODE_3),regex_comm_100_2);
        }

        Configuration.Builder node4_CB = nf.configurationBuilder().setHostname(NODE_4.getName());
        configs.put(NODE_4, node4_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        // Create BGP processes
        BgpProcess node_1A_BGP = getBgpProcess(configs,NODE_1A);
        node_1A_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_2A.getIp(),getBgpActivePeerConfig(NODE_1A,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node_2A_BGP = getBgpProcess(configs,NODE_2A);
        node_2A_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_1A.getIp(),getBgpActivePeerConfig(NODE_2A,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_2A,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        BgpProcess node_1B_BGP = getBgpProcess(configs,NODE_1B);
        node_1B_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_2B.getIp(),getBgpActivePeerConfig(NODE_1B,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));
        BgpProcess node_2B_BGP = getBgpProcess(configs,NODE_2B);
        node_2B_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_1B.getIp(),getBgpActivePeerConfig(NODE_2B,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_2B,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        BgpProcess node_3_BGP = getBgpProcess(configs,NODE_3);
        node_3_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_4.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2A.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_2B.getIp(),getBgpActivePeerConfig(NODE_3,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        BgpProcess node_4_BGP = getBgpProcess(configs,NODE_4);
        node_4_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_3.getIp(),getBgpActivePeerConfig(NODE_4,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Create policies
        RoutingPolicy node_1A_import = getPermitDefault(configs.get(NODE_1A),IMPORT_POLICY_NAME);
        RoutingPolicy node_1A_export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_1A)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(
                        new If(checkForPrefixListMatch(PREFIX_MATCH), replaceCommunities("100:1"),
                                permitRoute(true)))).build();

        RoutingPolicy node_1B_import = getPermitDefault(configs.get(NODE_1B),IMPORT_POLICY_NAME);
        RoutingPolicy node_1B_export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_1B)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(
                        new If(checkForPrefixListMatch(PREFIX_MATCH), replaceCommunities("100:1"),
                                permitRoute(true)))).build();

        RoutingPolicy node_2A_import = getPermitDefault(configs.get(NODE_2A),IMPORT_POLICY_NAME);
        RoutingPolicy node_2A_export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_2A)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(
                        new If(checkForCommunity("100:1"), replaceCommunities("100:2"),
                                permitRoute(true)))).build();

        RoutingPolicy node_2B_import = getPermitDefault(configs.get(NODE_2B),IMPORT_POLICY_NAME);
        RoutingPolicy node_2B_export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_2B)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(
                        new If(checkForCommunity("100:1"), replaceCommunities(faulty == 1 || faulty == 2 ? "100:3" : "100:2"),
                                permitRoute(true)))).build();

        RoutingPolicy node_3_import = getPermitDefault(configs.get(NODE_3),IMPORT_POLICY_NAME);
        RoutingPolicy node_3_export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_3)).setName(EXPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(
                        new If(checkForCommunity("100:2"), permitRoute(false), ImmutableList.of(
                                new If(checkForCommunity("100:3"), permitRoute(false), permitRoute(true)))))).build();

        RoutingPolicy node_4_import = getPermitDefault(configs.get(NODE_4),IMPORT_POLICY_NAME);
        RoutingPolicy node_4_export = getPermitDefault(configs.get(NODE_4),EXPORT_POLICY_NAME);

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

        return new Network(tbdd,configs,imports,exports);
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

        Network net = twoPathNetwork(NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4,0);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(NODE_4)));
        verifier.addProperty(NODE_4,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        Set<NetworkThread> threads = NetworkThread.getThreadsFromVerifier(verifier);
        Set<Set<String>> threadStrings = threads.stream().map(t -> t.dirtyString(prefixesConsidered)).collect(Collectors.toSet());

        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());
    }

    @Test
    public void faulty1TwoPathNetworkTest() {
        String prefix = "25.13.0.0/16";
        List<String> prefixesConsidered = ImmutableList.of(prefix);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefix)));

        Node NODE_1A = new Node("10.0.1.1","node_1_a");
        Node NODE_1B = new Node("10.0.1.2","node_1_b");
        Node NODE_2A = new Node("10.0.2.1","node_2_a");
        Node NODE_2B = new Node("10.0.2.2","node_2_b");
        Node NODE_3 = new Node("10.0.3.0","node_3_");
        Node NODE_4 = new Node("10.0.4.0","node_4_");

        Network net = twoPathNetwork(NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4,1);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(NODE_4)));
        verifier.addProperty(NODE_4,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());
    }

    @Test
    public void faulty2TwoPathNetworkTest() {
        String prefix = "25.13.0.0/16";
        List<String> prefixesConsidered = ImmutableList.of(prefix);
        PrefixSpace PREFIX = new PrefixSpace(PrefixRange.fromPrefix(Prefix.parse(prefix)));

        Node NODE_1A = new Node("10.0.1.1","node_1_a");
        Node NODE_1B = new Node("10.0.1.2","node_1_b");
        Node NODE_2A = new Node("10.0.2.1","node_2_a");
        Node NODE_2B = new Node("10.0.2.2","node_2_b");
        Node NODE_3 = new Node("10.0.3.0","node_3_");
        Node NODE_4 = new Node("10.0.4.0","node_4_");

        Network net = twoPathNetwork(NODE_1A,NODE_1B,NODE_2A,NODE_2B,NODE_3,NODE_4,2);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(NODE_4)));
        verifier.addProperty(NODE_4,property);
        Verifier.VerificationResult result = verifier.run();
        //List<String> pp = result.dirtyReadableResults(prefixesConsidered);
        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());
    }

    public Network simpleNetwork(Ip entry, Ip exit,
                                 Node NODE_A, Node NODE_B, Node NODE_C, int faulty) {
        String IMPORT_POLICY_NAME = "from_entering";
        String EXPORT_POLICY_NAME = "to_leaving";
        String PREFIX_MATCH = "prefixMatch";

        Map<Node, Configuration> configs = new HashMap<>();
        Map<Node, RoutingPolicy> imports = new HashMap<>();
        Map<Node, RoutingPolicy> exports = new HashMap<>();

        String plain_comm_1 = "100:1";
        String plain_comm_2 = "100:2";

        String regex_comm_100_1 = "^" + plain_comm_1 + "$";
        String regex_comm_100_2 = "^" + plain_comm_2 + "$";

        RouteFilterList prefixMatch = new RouteFilterList(PREFIX_MATCH, ImmutableList.of(new RouteFilterLine(PERMIT, PrefixRange.fromPrefix(Prefix.parse("25.13.0.0/16")))));

        // Create configs
        Configuration.Builder nodeA_CB = nf.configurationBuilder().setHostname(NODE_A.getName());
        configs.put(NODE_A, nodeA_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        if (faulty == 2) { includeCommunities(configs.get(NODE_A),regex_comm_100_2);
        } else if (faulty != 1){ includeCommunities(configs.get(NODE_A),regex_comm_100_1); }
        configs.get(NODE_A).setRouteFilterLists(ImmutableMap.of(PREFIX_MATCH,prefixMatch));

        Configuration.Builder nodeB_CB = nf.configurationBuilder().setHostname(NODE_B.getName());
        configs.put(NODE_B, nodeB_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());

        Configuration.Builder nodeC_CB = nf.configurationBuilder().setHostname(NODE_C.getName());
        configs.put(NODE_C, nodeC_CB.setConfigurationFormat(ConfigurationFormat.CISCO_IOS).build());
        includeCommunities(configs.get(NODE_C),regex_comm_100_1);
        if (faulty == 5) { includeCommunities(configs.get(NODE_A),regex_comm_100_2);
        } else if (faulty != 6){ includeCommunities(configs.get(NODE_A),regex_comm_100_1); }

        // Create BGP processes
        BgpProcess node_A_BGP = getBgpProcess(configs,NODE_A);
        node_A_BGP.setNeighbors(ImmutableSortedMap.of(
                entry,getBgpActivePeerConfig(NODE_A,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_B.getIp(),getBgpActivePeerConfig(NODE_A,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        BgpProcess node_B_BGP = getBgpProcess(configs,NODE_B);
        node_B_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_A.getIp(),getBgpActivePeerConfig(NODE_B,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                NODE_C.getIp(),getBgpActivePeerConfig(NODE_B,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        BgpProcess node_C_BGP = getBgpProcess(configs,NODE_C);
        node_C_BGP.setNeighbors(ImmutableSortedMap.of(
                NODE_B.getIp(),getBgpActivePeerConfig(NODE_C,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME),
                exit,getBgpActivePeerConfig(NODE_C,IMPORT_POLICY_NAME,EXPORT_POLICY_NAME)));

        // Creating routing policy
        RoutingPolicy node_A_import;
        RoutingPolicy node_A_export;
        RoutingPolicy node_B_import;
        RoutingPolicy node_B_export;
        RoutingPolicy node_C_import;
        RoutingPolicy node_C_export;

        node_A_import = faulty == 1 ? getPermitDefault(configs.get(NODE_A),IMPORT_POLICY_NAME) :
                nf.routingPolicyBuilder().setOwner(configs.get(NODE_A)).setName(IMPORT_POLICY_NAME)
                .setStatements(ImmutableList.of(
                        new If(checkForPrefixListMatch(PREFIX_MATCH),
                                faulty == 7 ? addToCommunities(plain_comm_2)
                                : replaceCommunities(faulty == 2 ? plain_comm_2 : plain_comm_1),
                                permitRoute(true)))).build();
        node_A_export = getPermitDefault(configs.get(NODE_A),EXPORT_POLICY_NAME);

        node_B_import = getPermitDefault(configs.get(NODE_B),IMPORT_POLICY_NAME);
        node_B_export = faulty == 3 ?
                nf.routingPolicyBuilder().setOwner(configs.get(NODE_B)).setName(EXPORT_POLICY_NAME).setStatements(clearCommunities()).build()
                : getPermitDefault(configs.get(NODE_B),EXPORT_POLICY_NAME);

        if (faulty == 5) {
            node_C_import = nf.routingPolicyBuilder().setOwner(configs.get(NODE_C)).setName(IMPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(
                            new If(checkForCommunity(plain_comm_2), permitRoute(false), permitRoute(true)))).build();
        } else if (faulty == 6 || faulty == 8) {
            node_C_import = getPermitDefault(configs.get(NODE_C),IMPORT_POLICY_NAME);
        } else {
            node_C_import = nf.routingPolicyBuilder().setOwner(configs.get(NODE_C)).setName(IMPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(
                            new If(checkForCommunity(plain_comm_1), permitRoute(faulty == 4), permitRoute(faulty != 4)))).build();
        }
        if (faulty == 8) {
            node_C_export = nf.routingPolicyBuilder().setOwner(configs.get(NODE_C)).setName(EXPORT_POLICY_NAME)
                    .setStatements(ImmutableList.of(
                            new If(checkForCommunity(plain_comm_1), permitRoute(false), permitRoute(true)))).build();
        } else {
            node_C_export = getPermitDefault(configs.get(NODE_C),EXPORT_POLICY_NAME);
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

        return new Network(tbdd,configs,imports,exports);
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

        Network net = simpleNetwork(entry,exit,NODE_A,NODE_B,NODE_C,3);
        Verifier verifier = new Verifier(net.tbdd,net.configInput());
        Invariant property = new Invariant(net.tbdd,Invariant.clauseBuilder().avoidPrefix(PREFIX).build(net.tbdd,net.imports.get(NODE_C)));
        verifier.addProperty(target,property);
        //Verifier.VerificationResult result = verifier.run();
        Verifier.VerificationResult result = verifier.runForwards(new Edge(entry,NODE_A.getIp()));
        List<String> pp = result.dirtyReadableResults(prefixesConsidered);

        assertTrue(result.verified());
        assertTrue(result.inferredTrue());
        assertTrue(result.counter().isEmpty());
    }
}
