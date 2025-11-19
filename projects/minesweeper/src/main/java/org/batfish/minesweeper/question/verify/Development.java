package org.batfish.minesweeper.question.verify;

import com.google.common.collect.ImmutableList;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.bgp.community.StandardCommunity;
import org.batfish.datamodel.routing_policy.communities.AllStandardCommunities;
import org.batfish.datamodel.routing_policy.communities.ColonSeparatedRendering;
import org.batfish.datamodel.routing_policy.communities.CommunityIs;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchExpr;
import org.batfish.datamodel.routing_policy.communities.CommunityMatchRegex;
import org.batfish.datamodel.routing_policy.communities.CommunitySet;
import org.batfish.datamodel.routing_policy.communities.CommunitySetDifference;
import org.batfish.datamodel.routing_policy.communities.CommunitySetMatchExpr;
import org.batfish.datamodel.routing_policy.communities.CommunitySetUnion;
import org.batfish.datamodel.routing_policy.communities.HasCommunity;
import org.batfish.datamodel.routing_policy.communities.InputCommunities;
import org.batfish.datamodel.routing_policy.communities.LiteralCommunitySet;
import org.batfish.datamodel.routing_policy.communities.MatchCommunities;
import org.batfish.datamodel.routing_policy.communities.SetCommunities;
import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.datamodel.routing_policy.expr.DestinationNetwork;
import org.batfish.datamodel.routing_policy.expr.MatchPrefixSet;
import org.batfish.datamodel.routing_policy.expr.NamedPrefixSet;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Development {
    public static List<Statement> addToCommunities(String regex) {
        return ImmutableList.of(
                new SetCommunities(CommunitySetUnion.of(InputCommunities.instance(),
                        new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse(regex))))),
                new Statements.StaticStatement(Statements.ReturnTrue));
    }

    ///  unclear if this works
    public static List<Statement> clearCommunities() {
//        throw new BatfishException("INCORRECTLY IMPLEMENTED");
        return ImmutableList.of(
                new SetCommunities(new CommunitySetDifference(InputCommunities.instance(), AllStandardCommunities.instance())),
                new Statements.StaticStatement(Statements.ReturnTrue));
    }

    public static List<Statement> replaceCommunities(String regex) {
        return ImmutableList.of(
                new SetCommunities(new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse(regex)))),
                new Statements.StaticStatement(Statements.ReturnTrue));
    }

    public static BooleanExpr checkForCommunity(String regex) {
        return new MatchCommunities(new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse(regex))));
    }

    public static BooleanExpr checkForPrefixListMatch(String prefixListLabel) {
        return new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(prefixListLabel));
    }

    public static List<Statement> permitRoute(boolean permit) {
        return permit ? ImmutableList.of(new Statements.StaticStatement(Statements.ReturnTrue))
          : ImmutableList.of(new Statements.StaticStatement(Statements.ReturnFalse));
    }

    public static void includeCommunities(Configuration config, String ... regexes) {
        Map<String, CommunityMatchExpr> matchMap = new HashMap<>();
        Map<String, CommunitySetMatchExpr> setMap = new HashMap<>();
        for (String regex : regexes) {
            String label = "comm_" + matchMap.size();
            CommunityMatchExpr comm = new CommunityMatchRegex(ColonSeparatedRendering.instance(),regex);
            matchMap.put(label,comm);
            setMap.put(label,new HasCommunity(comm));
        }
        config.setCommunityMatchExprs(matchMap);
        config.setCommunitySetMatchExprs(setMap);
        //return config;
    }
}
