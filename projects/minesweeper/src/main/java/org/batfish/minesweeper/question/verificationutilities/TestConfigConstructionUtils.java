package org.batfish.minesweeper.question.verificationutilities;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSortedMap;
import org.batfish.datamodel.BgpActivePeerConfig;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.bgp.community.StandardCommunity;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
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
import org.batfish.datamodel.routing_policy.expr.IntComparator;
import org.batfish.datamodel.routing_policy.expr.LiteralLong;
import org.batfish.datamodel.routing_policy.expr.MatchMetric;
import org.batfish.datamodel.routing_policy.expr.MatchPrefixSet;
import org.batfish.datamodel.routing_policy.expr.NamedPrefixSet;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements;
import org.batfish.minesweeper.bdd.TransferBDD;

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;

/// Class created to help construct unit tests using Batfishes AST classes
public class TestConfigConstructionUtils {
  public record Network(
      TransferBDD tbdd,
      Map<Node, Configuration> configs,
      Map<Node, RoutingPolicy> imports,
      Map<Node, RoutingPolicy> exports) {
    private Map<String, Configuration> configInput() {
      Map<String, Configuration> result = new HashMap<>();
      for (Node node : configs.keySet()) {
        result.put(node.getName(), configs.get(node));
      }
      return result;
    }

    public NetworkInfo getInfo() {
      return new NetworkInfo(this.tbdd(), configInput());
    }
  }

  public record Networkv2(
      TransferBDD tbdd,
      Map<Node, Configuration> configs,
      RoutingPolicy template,
      List<String> prefixes) {
    public SortedMap<String, Configuration> configInput() {
      ImmutableSortedMap.Builder<String, Configuration> builder =
          new ImmutableSortedMap.Builder<>(Comparator.naturalOrder());
      for (Node node : configs.keySet()) {
        builder.put(node.getName(), configs.get(node));
      }
      return builder.build();
    }

    public NetworkInfo getInfo() {
      return new NetworkInfo(this.tbdd(), configInput());
    }

    public NetworkInfo getInfo(PrefixSpace prefix) {
      return new NetworkInfo(
          this.tbdd(),
          configInput(),
          Invariant.builder()
              .addClause(Invariant.clauseBuilder().matchPrefix(prefix))
              .build(tbdd, null));
    }
  }

  /**
   * Used to create policy where the provided community should be added to the list of communities
   *
   * @param regex Regex of communities to add (ex. 100:1)
   * @return statements to include in RoutingPolicy construction
   */
  public static List<Statement> addToCommunities(String regex) {
    return ImmutableList.of(
        new SetCommunities(
            CommunitySetUnion.of(
                InputCommunities.instance(),
                new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse(regex))))),
        new Statements.StaticStatement(Statements.ReturnTrue));
  }

  ///  Intended to return statements which clear all communities on a route
  public static List<Statement> clearCommunities() {
    return ImmutableList.of(
        new SetCommunities(
            new CommunitySetDifference(
                InputCommunities.instance(), AllStandardCommunities.instance())),
        new Statements.StaticStatement(Statements.ReturnTrue));
  }

  /**
   * Used to create policy where the provided community should replace existing communities
   *
   * @param regex Regex of communities to replace existing (ex. 100:1)
   * @return statements to include in RoutingPolicy construction
   */
  public static List<Statement> replaceCommunities(String regex) {
    return ImmutableList.of(
        new SetCommunities(
            new LiteralCommunitySet(CommunitySet.of(StandardCommunity.parse(regex)))),
        new Statements.StaticStatement(Statements.ReturnTrue));
  }

  /**
   * Used when creating a policy to check if the route has the provided community
   *
   * @param regex Regex of communities to replace existing (ex. "100:1")
   * @return condition to provide to if statement
   */
  public static BooleanExpr checkForCommunity(String regex) {
    return new MatchCommunities(
        new InputCommunities(), new HasCommunity(new CommunityIs(StandardCommunity.parse(regex))));
  }

  /**
   * Used when creating a policy to check if the route has a prefix within the provided set
   *
   * @param prefixListLabel name of prefix set to check
   * @return condition to provide to if statement
   */
  public static BooleanExpr checkForPrefixListMatch(String prefixListLabel) {
    return new MatchPrefixSet(DestinationNetwork.instance(), new NamedPrefixSet(prefixListLabel));
  }

  public static BooleanExpr metricGreaterThan(Long met) {
    return new MatchMetric(IntComparator.GT, new LiteralLong(met));
  }

  public static BooleanExpr metricLessThan(Long met) {
    return new MatchMetric(IntComparator.LT, new LiteralLong(met));
  }

  /**
   * Used when creating a policy to accept or reject a route (based on provided boolean)
   *
   * @param permit true if route is permitted (false if denied)
   * @return statements to include in RoutingPolicy construction
   */
  public static List<Statement> permitRoute(boolean permit) {
    return permit
        ? ImmutableList.of(new Statements.StaticStatement(Statements.ExitAccept))
        : ImmutableList.of(new Statements.StaticStatement(Statements.ExitReject));
  }

  /**
   * Used when creating a policy to include an if statement (new stanza
   *
   * @param guard condition checked
   * @param trues statements executed in true branch
   * @param falses statements executed in false branch
   * @return statements to include in RoutingPolicy construction
   */
  public static List<Statement> ifStatement(
      BooleanExpr guard, List<Statement> trues, List<Statement> falses) {
    return ImmutableList.of(new If(guard, trues, falses));
  }

  /**
   * Adds the provided communities to be considered by the config provided
   *
   * @param config config to update
   * @param regexes communities to include (ex. "^100:1$")
   */
  public static void includeCommunities(Configuration config, String... regexes) {
    Map<String, CommunityMatchExpr> matchMap = new HashMap<>();
    Map<String, CommunitySetMatchExpr> setMap = new HashMap<>();
    for (String regex : regexes) {
      String label = "comm_" + matchMap.size();
      CommunityMatchExpr comm = new CommunityMatchRegex(ColonSeparatedRendering.instance(), regex);
      matchMap.put(label, comm);
      setMap.put(label, new HasCommunity(comm));
    }
    config.setCommunityMatchExprs(matchMap);
    config.setCommunitySetMatchExprs(setMap);
  }

  public static BgpActivePeerConfig getBgpActivePeerConfig(
      String groupName, String importPolicy, String exportPolicy) {
    BgpActivePeerConfig.Builder builder = BgpActivePeerConfig.builder().setGroup(groupName);
    if (importPolicy != null && exportPolicy != null) {
      return builder
          .setIpv4UnicastAddressFamily(
              Ipv4UnicastAddressFamily.builder()
                  .setImportPolicy(importPolicy)
                  .setExportPolicy(exportPolicy)
                  .build())
          .build();
    } else if (importPolicy != null) {
      return builder
          .setIpv4UnicastAddressFamily(
              Ipv4UnicastAddressFamily.builder().setImportPolicy(importPolicy).build())
          .build();
    } else if (exportPolicy != null) {
      return builder
          .setIpv4UnicastAddressFamily(
              Ipv4UnicastAddressFamily.builder().setExportPolicy(exportPolicy).build())
          .build();
    } else {
      return builder.build();
    }
  }
}
