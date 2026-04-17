package org.batfish.minesweeper.question.verificationutilities;

import com.google.common.annotations.VisibleForTesting;
import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.NetworkSnapshot;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Bgpv4Route;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.ModelGeneration;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.bdd.TransferReturn;
import org.batfish.minesweeper.question.liveness.InterferenceCheck;
import org.batfish.minesweeper.question.liveness.Path;
import org.batfish.minesweeper.question.liveness.PathAnalyzer;
import org.batfish.minesweeper.question.liveness.PathExploration;
import org.batfish.minesweeper.question.liveness.UpdatedPathAnalyzer;
import org.batfish.minesweeper.question.safety.Infer;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;
import org.batfish.question.edges.EdgesQuestion;
import org.batfish.specifier.SpecifierContext;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.MoreObjects.firstNonNull;
import static java.util.Objects.isNull;
import static java.util.Objects.nonNull;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_locations;

public class NetworkInfo {
  private static final Logger LOGGER = LogManager.getLogger(NetworkInfo.class);

  public final TransferBDD tbdd;
  public final Invariant defaultIncoming;

  public record NamedIp(Ip ip, String node) {
    @Override
    public boolean equals(Object object) {
      if (object == null || getClass() != object.getClass()) {
        return false;
      }
      NamedIp key = (NamedIp) object;
      return Objects.equals(ip, key.ip) && Objects.equals(node, key.node);
    }

    @Override
    public int hashCode() {
      return Objects.hash(ip, node);
    }
  }

  /// Node n Ip -> (Neighbor Ip -> node object for node n)
  private final Map<String, Node> nodeByName = new HashMap<>();
  private final Map<NamedIp, Map<NamedIp, Edge>> edges = new HashMap<>();
  private final Map<Edge, RoutingPolicy> imports = new HashMap<>();
  private final Map<Edge, RoutingPolicy> exports = new HashMap<>();

  /// Assumptions on edges where we do not have the config for the source of the edge
  private final Map<Location, Invariant> checkedAssumptions = new HashMap<>();
  /// Assumptions on nodes in network or edges originating within network
  private final Map<Location, Invariant> enforcedAssumptions = new HashMap<>();

  // information to deal with internal/external ASN
  private final Set<Location> externalOutgoing = new HashSet<>();

  @VisibleForTesting
  private void processOnlyConfigs(@Nonnull Map<String, Configuration> configs) {
    Map<Configuration, Collection<RoutingPolicy>> policies = new HashMap<>();
    configs
        .keySet()
        .forEach(nodeName -> nodeByName.put(nodeName.toLowerCase(), new Node(nodeName)));

    Map<Ip, Node> ipIndexed = new HashMap<>();
    configs.forEach(
        (name, config) -> {
          Ip ip = config.getDefaultVrf().getBgpProcess().getRouterId();
          Node v = ipIndexed.put(ip, nodeByName.get(name.toLowerCase()));
          if (v != null) {
            throw new BatfishException("Processing by configs cannot handle reuse of Ip.");
          }
          config
              .getDefaultVrf()
              .getBgpProcess()
              .getActiveNeighbors()
              .values()
              .forEach(
                  peer -> {
                    if (peer.getLocalIp() != null) {
                      Node vv =
                          ipIndexed.put(peer.getLocalIp(), nodeByName.get(name.toLowerCase()));
                      if (vv != null) {
                        throw new BatfishException(
                            "Processing by configs cannot handle reuse of Ip.");
                      }
                    }
                  });
        });

    for (String nodeName : configs.keySet()) {
      Configuration config = configs.get(nodeName);
      if (isNull(config) || isNull(config.getVrfs())) {
        continue;
      }

      policies.put(config, new HashSet<>());
      config
          .getDefaultVrf()
          .getBgpProcess()
          .getActiveNeighbors()
          .forEach(
              (neighborIp, peer) -> {
                Ip nodeIp =
                    firstNonNull(
                        peer.getLocalIp(), config.getDefaultVrf().getBgpProcess().getRouterId());

                boolean eBGP =
                    !(peer.getLocalAs() == null
                        || peer.getRemoteAsns().contains(peer.getLocalAs()));

                NamedIp thisKey = new NamedIp(nodeIp, nodeName.toLowerCase());
                NamedIp neighborKey =
                    new NamedIp(
                        neighborIp,
                        ipIndexed.containsKey(neighborIp)
                            ? ipIndexed.get(neighborIp).getName().toLowerCase()
                            : null);

                Edge incoming =
                    edges.containsKey(neighborKey) && edges.get(neighborKey).containsKey(thisKey)
                        ? edges.get(neighborKey).get(thisKey)
                        : (edges.containsKey(thisKey) && edges.get(thisKey).containsKey(neighborKey)
                            ? edges.get(neighborKey).get(thisKey).flipEdge()
                            : new Edge(neighborIp, nodeIp, eBGP));

                if (!incoming.hasSrcNode() && ipIndexed.containsKey(neighborIp)) {
                  incoming.setSrcNode(ipIndexed.get(neighborIp));
                }
                Node thisNode = nodeByName.get(nodeName.toLowerCase());
                if (!incoming.hasDstNode()) {
                  incoming.setDstNode(thisNode);
                }
                Edge outgoing = incoming.flipEdge();

                nodeByName.get(nodeName.toLowerCase()).addIncomingNeighbor(incoming);

                edges.computeIfAbsent(neighborKey, k -> new HashMap<>()).put(thisKey, incoming);
                edges.computeIfAbsent(thisKey, k -> new HashMap<>()).put(neighborKey, outgoing);

                if (eBGP) {
                  // to keep traffic of all outgoing edges
                  this.externalOutgoing.add(outgoing);
                }
                Ipv4UnicastAddressFamily unicast = peer.getIpv4UnicastAddressFamily();
                // only add policies which exist, otherwise a default is used for weakest
                // precondition
                if (!isNull(unicast) && !isNull(config.getRoutingPolicies())) {
                  if (!isNull(unicast.getImportPolicy())
                      && !isNull(config.getRoutingPolicies().get(unicast.getImportPolicy()))) {
                    imports.put(
                        incoming, config.getRoutingPolicies().get(unicast.getImportPolicy()));
                    policies.get(config).add(imports.get(incoming));
                  }
                  if (!isNull(unicast.getExportPolicy())
                      && !isNull(config.getRoutingPolicies().get(unicast.getExportPolicy()))) {
                    exports.put(
                        outgoing, config.getRoutingPolicies().get(unicast.getExportPolicy()));
                    policies.get(config).add(exports.get(outgoing));
                  }
                }
              });
    }

    assert this.externalOutgoing.stream().allMatch(l -> l instanceof Edge);
  }

  private NetworkInfo(@Nonnull TransferBDD tbdd, @Nonnull Map<String, Configuration> configs) {
    this(tbdd, configs, new Invariant(tbdd));
  }

  private NetworkInfo(
      @Nonnull TransferBDD tbdd,
      @Nonnull Map<String, Configuration> configs,
      @Nonnull Invariant defaultIncoming) {
    this.tbdd = tbdd;
    this.defaultIncoming = defaultIncoming;
    processOnlyConfigs(configs);
    // default assumption of True for incoming edges
    for (Map<NamedIp, Edge> edgesBank : edges.values()) {
      edgesBank
          .values()
          .forEach(
              edge -> {
                if (!edge.hasSrcNode()) {
                  checkedAssumptions.put(edge, this.defaultIncoming);
                }
              });
    }
  }

  @VisibleForTesting
  public static NetworkInfo ofConfigs(
      @Nonnull TransferBDD tbdd,
      @Nonnull Map<String, Configuration> configs,
      @Nonnull Invariant defaultIncoming) {
    return new NetworkInfo(tbdd, configs, defaultIncoming);
  }

  @VisibleForTesting
  public static NetworkInfo ofConfigs(
      @Nonnull TransferBDD tbdd, @Nonnull Map<String, Configuration> configs) {
    return new NetworkInfo(tbdd, configs);
  }

  private boolean validLocation(Location location) {
    if (location instanceof Node node) {
      return nodeByName.containsKey(node.getName()) && nodeByName.get(node.getName()).equals(node);
    } else if (location instanceof Edge edge) {
      // checks if it is an incoming or an outgoing edge
      NamedIp src =
          new NamedIp(
              edge.getSrc(), edge.getSrcNode() != null ? edge.getSrcNode().getName() : null);
      NamedIp dst =
          new NamedIp(
              edge.getDst(), edge.getDstNode() != null ? edge.getDstNode().getName() : null);
      boolean isIncomingEdgeOrInternal =
          edges.containsKey(src)
              && edges.get(src).containsKey(dst)
              && edges.get(src).get(dst).equals(edge);
      return isIncomingEdgeOrInternal
          || (edges.containsKey(dst)
              && edges.get(dst).containsKey(src)
              && edges.get(dst).get(src).equals(edge.flipEdge()));
    } else {
      return false;
    }
  }

  private Map<Configuration, Collection<RoutingPolicy>> processConfigs(
      @Nonnull Map<String, Configuration> configs) {
    LOGGER.info("Processing each config provided...");
    Map<Configuration, Collection<RoutingPolicy>> policies = new HashMap<>();

    for (String nodeName : configs.keySet()) {
      Configuration config = configs.get(nodeName);
      // no need to evaluate any configs which are null or don't yield anything
      if (isNull(config) || isNull(config.getVrfs())) {
        continue;
      }

      Node node = nodeByName.get(nodeName.toLowerCase());
      if (node == null) {
        throw new BatfishException("Node from BGP sessions found not found in topology");
      }
      policies.put(config, new HashSet<>());

      // filter out any null VRFs and only keep default
      Stream<Vrf> forwarding =
          config.getVrfs().values().stream()
              .filter(vrf -> nonNull(vrf) && vrf.getName().equals("default"));

      // gets the bgp processes and filters out any null processes
      List<BgpProcess> bgpProcesses =
          forwarding.map(Vrf::getBgpProcess).filter(Objects::nonNull).toList();

      // gather the policies
      bgpProcesses.forEach(
          proc -> {
            proc.getActiveNeighbors().entrySet().stream()
                .filter(
                    entry ->
                        nonNull(entry)
                            // make sure entry doesn't have nulls
                            && nonNull(entry.getKey())
                            && nonNull(entry.getValue())
                            // if the local IP address is 0.0.0.0, we remove
                            && (entry.getValue().getLocalIp() == null
                                || !entry.getValue().getLocalIp().equals(Ip.ZERO)))
                .forEach(
                    entry -> {
                      Ip nodeIp = firstNonNull(entry.getValue().getLocalIp(), proc.getRouterId());
                      Ip neighborIp = entry.getKey();
                      assert !nodeIp.equals(Ip.ZERO);

                      boolean eBGP =
                          !(entry.getValue().getLocalAs() == null
                              || entry
                                  .getValue()
                                  .getRemoteAsns()
                                  .contains(entry.getValue().getLocalAs()));

                      Optional<Edge> incomingOpt = node.getIncoming(neighborIp, nodeIp);
                      Edge incoming;
                      if (incomingOpt.isPresent()) {
                        incoming = incomingOpt.get();
                        assert eBGP == incoming.isEBGP();
                      } else {
                        NamedIp key = new NamedIp(nodeIp, nodeName.toLowerCase());
                        NamedIp neighborKey = new NamedIp(neighborIp, null);
                        incoming = new Edge(neighborIp, nodeIp, eBGP);
                        Edge prev =
                            edges
                                .computeIfAbsent(neighborKey, k -> new HashMap<>())
                                .put(key, incoming);
                        incoming.setDstNode(node);
                        boolean prevPresent = node.addIncomingNeighbor(incoming);
                        assert prev == null && !prevPresent;
                      }
                      Edge outgoing = incoming.flipEdge();

                      if (outgoing.isEBGP()) {
                        this.externalOutgoing.add(outgoing);
                      }

                      Ipv4UnicastAddressFamily unicast =
                          entry.getValue().getIpv4UnicastAddressFamily();

                      if (!isNull(unicast) && !isNull(config.getRoutingPolicies())) {
                        if (!isNull(unicast.getImportPolicy())
                            && !isNull(
                                config.getRoutingPolicies().get(unicast.getImportPolicy()))) {
                          imports.put(
                              incoming, config.getRoutingPolicies().get(unicast.getImportPolicy()));
                          policies.get(config).add(imports.get(incoming));
                        }
                        if (!isNull(unicast.getExportPolicy())
                            && !isNull(
                                config.getRoutingPolicies().get(unicast.getExportPolicy()))) {
                          exports.put(
                              outgoing, config.getRoutingPolicies().get(unicast.getExportPolicy()));
                          policies.get(config).add(exports.get(outgoing));
                        }
                      }
                    });
          });
    }
    return policies;
  }

  /// String representation of the provided location within context of the network (ie using node
  /// names  when possible in place of ip addresses)
  public String locationStr(Location loc) {
    return loc.toUniqueString();
  }

  /// Returns the assumptions that should be checked of the network
  public Map<Location, Invariant> getCheckedAssumptions() {
    return checkedAssumptions;
  }

  /// Returns the assumptions of the network that are enforced in inference
  public Map<Location, Invariant> getEnforcedAssumptions() {
    return enforcedAssumptions;
  }

  public Set<Location> getEdgesByDstIp(Ip dst) {
    Set<Location> destinationEdges = new HashSet<>();
    for (Map<NamedIp, Edge> edgeMap : edges.values()) {
      edgeMap
          .values()
          .forEach(
              edge -> {
                if (edge.getDst().equals(dst)) {
                  destinationEdges.add(edge);
                }
              });
    }
    return destinationEdges;
  }

  public Set<Location> getEdgesBySrcIp(Ip src) {
    Set<Location> sourceEdges = new HashSet<>();
    for (NamedIp srcKey : edges.keySet()) {
      if (srcKey.ip.equals(src)) {
        sourceEdges.addAll(edges.get(srcKey).values());
      }
    }
    return sourceEdges;
  }

  /// Returns set of all ips associated with a provided node (via node's name)
  public Optional<Node> getNodeByName(String name) {
    if (this.nodeByName.containsKey(name)) {
      return Optional.of(this.nodeByName.get(name));
    } else {
      return Optional.empty();
    }
  }

  public Set<Location> getNodesLinkedToIp(Ip ip) {
    return nodeByName.values().stream().filter(n -> n.tiedToIp(ip)).collect(Collectors.toSet());
  }

  /// Returns the policy (getImport flag indicates import or export) for the provided edge
  public RoutingPolicy getPolicy(Edge location, boolean getImport) {
    if (getImport) {
      return imports.getOrDefault(location, null);
    } else {
      return exports.getOrDefault(location, null);
    }
  }

  ///  Builds the provided invariant in the context of this network
  public Invariant buildInvariant(Location location, Invariant.Builder inv, boolean wpQuery) {
    RoutingPolicy policy = null;
    assert location instanceof Edge || location instanceof Node;
    boolean getImportPolicy = (location instanceof Edge) != wpQuery;
    if (location instanceof Node node) {
      for (Edge incoming : node.getAllIncomingEdges()) {
        policy = this.getPolicy(incoming, getImportPolicy);
        if (policy != null) {
          break;
        }
      }
    } else {
      policy = this.getPolicy((Edge) location, getImportPolicy);
    }
    return inv.build(this.tbdd, policy);
  }

  /// Used to add an assumption which indicates any traffic is possible at provided location
  public NetworkInfo anyRouteAllowedAt(Location anchor) {
    //    return this.addAssumption(anchor, new Invariant(this.tbdd));
    this.checkedAssumptions.put(anchor, new Invariant(this.tbdd));
    return this;
  }

  /// Checks according to ASN if applicable, otherwise checks if we have a config for the
  /// destination (ONLY USED FOR VERIFYING PROPERTY GOING OUT ON ALL EXTERNAL EDGES)
  public Set<Location> allEdgesLeavingNetwork() {
    Set<Location> outgoing = new HashSet<>();
    if (!this.externalOutgoing.isEmpty()) {
      outgoing.addAll(this.externalOutgoing);
      assert outgoing.stream().allMatch(l -> l instanceof Edge e && e.isEBGP());
    } else {
      for (Location location : this.checkedAssumptions.keySet()) {
        if (location instanceof Edge incoming && isIncomingEdge(incoming)) {
          outgoing.add(incoming.flipEdge());
        }
      }
    }
    assert outgoing.stream().allMatch(l -> l instanceof Edge e && e.hasSrcNode());
    return outgoing;
  }

  public Optional<Edge> getOutgoingEdgeIfNeighborExists(Node node, Ip neighbor) {
    if (nodeByName.containsKey(node.getName())) {
      assert nodeByName.get(node.getName()).equals(node);
      return node.getIncomingFrom(neighbor).map(Edge::flipEdge);
    }
    return Optional.empty();
  }

  public Optional<Edge> checkForEdgeViaIps(Ip src, Ip dst) {
    Optional<Edge> option = Optional.empty();
    for (NamedIp srcKey : edges.keySet()) {
      if (srcKey.ip.equals(src)) {
        for (NamedIp dstKey : edges.get(srcKey).keySet()) {
          if (dstKey.ip.equals(dst)) {
            if (option.isPresent()) {
              // if there are multiple edges via just Ip then return empty
              return Optional.empty();
            } else {
              option = Optional.of(edges.get(srcKey).get(dstKey));
            }
          }
        }
      }
    }
    return option;
  }

  /// Checks according to ASN if applicable, otherwise checks if we have a config for the
  /// destination
  private boolean isOutgoingEdge(Location location) {
    if (location instanceof Edge edge) {
      if (externalOutgoing.isEmpty()) {
        // outgoing external edge if it does not have destination node
        return !edge.hasDstNode();
      } else {
        return externalOutgoing.contains(edge);
      }
    } else {
      return false;
    }
  }

  /// Checks according to ASN if applicable, otherwise checks if we have a config for the source
  public boolean isIncomingEdge(Location location) {
    return location instanceof Edge edge && this.isOutgoingEdge(edge.flipEdge());
  }

  /// Used to add an assumption pertaining to traffic at provided location, we assume incoming edges
  /// are checked and internal locations/outgoing edges are enforced
  public void addAssumption(@Nonnull Location location, @Nonnull Invariant assumption) {
    // we only want to add assumptions within network or connecting to external neighbor
    if (this.validLocation(location)) {
      if (location instanceof Edge e && !e.hasSrcNode()) {
        // check if edge is coming from a source where we do not have a config
        checkedAssumptions.put(location, assumption);
      } else {
        // a location that is not an incoming edge, should be enforced during inference
        enforcedAssumptions.put(location, assumption);
      }
    } else {
      throw new BatfishException(
          "Attempting to place assumption at "
              + location
              + ", but this location is not within nor connected to the analyzed network.");
    }
  }

  /// Used to add an assumption pertaining to traffic at provided location, need to build location
  /// and invariant in the context of this network
  public Set<Location> addAssumption(
      @Nonnull Location.Builder locationBuilder, @Nonnull Invariant.Builder assumption) {
    Set<Location> locations = locationBuilder.instantiate(this);
    assert !locations.isEmpty();
    locations.forEach(
        location -> this.addAssumption(location, this.buildInvariant(location, assumption, true)));
    return locations;
  }

  /// Creates instance of Lightyear objection, which can be used as a sanity check
  public Lightyear checker() {
    return new Lightyear(this.imports, this.exports);
  }

  /// Returns an Infer object reflective of the network which can be used for safety property
  /// verification
  public Infer toInfer() {
    Path.Context context =
        new Path.Context(
            this.tbdd,
            this.checkedAssumptions,
            this.enforcedAssumptions,
            this.imports,
            this.exports,
            this.defaultIncoming);
    return new Infer(
        context,
        this.nodeByName,
        this.edges.values().stream().flatMap(m -> m.values().stream()).collect(Collectors.toSet()));
  }

  /// Returns a PathAnalyzer objective reflective of the network which can be used for verification
  /// of the provided liveness property (pertaining to the provided prefix space)
  public PathAnalyzer toPathAnalyzer(
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Map<RoutingPolicy, List<TransferReturn>> computedPathsCache) {
    Path.Context context =
        new Path.Context(
            this.tbdd,
            this.checkedAssumptions,
            this.enforcedAssumptions,
            this.imports,
            this.exports,
            this.defaultIncoming);
    return new UpdatedPathAnalyzer(context, prefix, location, target, computedPathsCache);
  }

  public PathExploration toPathExploration(
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Set<Edge> ingress,
      Map<RoutingPolicy, List<TransferReturn>> computedPathsCache) {
    Path.Context context =
        new Path.Context(
            this.tbdd,
            this.checkedAssumptions,
            this.enforcedAssumptions,
            this.imports,
            this.exports,
            this.defaultIncoming);
    return new PathExploration(context, prefix, location, target, ingress, computedPathsCache);
  }

  public Inference toInference() {
    return new Inference(tbdd, imports, exports, checkedAssumptions, enforcedAssumptions);
  }

  /// Returns a PathAnalyzer objective reflective of the network which can be used for interference
  /// of the provided liveness property (pertaining to the provided prefix space)
  public InterferenceCheck toInterferenceCheck(
      PrefixSpace prefix,
      Location location,
      Invariant target,
      Map<RoutingPolicy, List<TransferReturn>> computedPathsCache) {
    Path.Context context =
        new Path.Context(
            this.tbdd,
            this.checkedAssumptions,
            this.enforcedAssumptions,
            this.imports,
            this.exports,
            this.defaultIncoming);
    return new InterferenceCheck(context, prefix, location, target, computedPathsCache);
  }

  /// Returns TableAnswerElement which lists all locations within the network (used when no target
  /// property is provided)
  public TableAnswerElement getAnswerElement() {
    TableAnswerElement tae = new TableAnswerElement(metadata_locations());
    Map<String, List<Map<Ip, Set<String>>>> nodeNameToEdges = new HashMap<>();
    nodeByName.forEach(
        (name, node) -> {
          List<Map<Ip, Set<String>>> connections =
              nodeNameToEdges.computeIfAbsent(name, k -> List.of(new HashMap<>(), new HashMap<>()));
          node.getAllIncomingEdges()
              .forEach(
                  incoming -> {
                    int typ = (incoming.isEBGP() ? 1 : 0);
                    connections
                        .get(typ)
                        .computeIfAbsent(incoming.getDst(), k -> new HashSet<>())
                        .add(
                            incoming.getSrcNode() == null
                                ? incoming.getSrc().toString()
                                : incoming.getSrcNode().getName() + " (" + incoming.getSrc() + ")");
                  });
        });

    nodeNameToEdges.keySet().stream()
        .sorted()
        .forEach(
            node -> {
              for (int i = 0; i <= 1; i++) {
                Map<Ip, Set<String>> neighbors = nodeNameToEdges.get(node).get(i);
                String connectionType = i == 0 ? "internal" : "external";
                neighbors.forEach(
                    (dst_ip, n) -> {
                      tae.addRow(
                          Row.builder()
                              .put(Setup.NODES_COL, node)
                              .put(Setup.CONNECTION_TYPE_COL, connectionType)
                              .put(Setup.DESTINATION_COL, dst_ip)
                              .put(Setup.NEIGHBORS_COL, n)
                              .build());
                    });
              }
            });

    return tae;
  }

  ///  Provides an example route for the constraint provided, we assume the constraint is
  /// satisfiable and well-formed
  public static Bgpv4Route getRouteExample(TransferBDD tbdd, BDD constraint) {
    assert !constraint.isZero();
    BDD model = ModelGeneration.constraintsToModel(constraint, tbdd.getConfigAtomicPredicates());
    if (!model.isAssignment() && model.isZero()) {
      return null;
    } else if (!model.isAssignment()) {
      assert false; // throws error during testing
      return null; // avoided otherwise
    } else {
      return ModelGeneration.satAssignmentToBgpInputRoute(model, tbdd.getConfigAtomicPredicates());
    }
  }

  public NetworkInfo(
      @Nonnull IBatfish batfish,
      @Nonnull NetworkSnapshot snapshot,
      @Nonnull Set<RegexConstraint> communityRegexes,
      @Nonnull Set<RegexConstraint> asPathRegexes,
      @Nullable Invariant.Builder defaultIncoming) {
    SpecifierContext context = batfish.specifierContext(snapshot);
    if (context == null) {
      throw new BatfishException("Cannot get the SpecifierContext from snapshot");
    }
    Map<String, Configuration> configs = context.getConfigs();

    batfish.computeDataPlane(snapshot);
    EdgesQuestion question = new EdgesQuestion(".*", ".*", EdgesQuestion.EdgeType.BGP, false);
    Answerer answerer = batfish.createAnswerer(question);
    if (answerer == null) {
      throw new BatfishException("Null answerer created");
    }
    List<Row> sessions = ((TableAnswerElement) answerer.answer(snapshot)).getRowsList();

    // ============================== EdgeAnswerer.answer() ============================== //
    //    EdgesQuestion question = new EdgesQuestion(".*", ".*", EdgesQuestion.EdgeType.BGP, false);
    //    Map<String, Configuration> configurations = batfish.loadConfigurations(snapshot);
    //    Set<String> includeNodes =
    //        question.getNodeSpecifier().resolve(batfish.specifierContext(snapshot));
    //    Set<String> includeRemoteNodes =
    //        question.getRemoteNodeSpecifier().resolve(batfish.specifierContext(snapshot));
    //
    //    TopologyProvider topologyProvider = batfish.getTopologyProvider();
    //    Topology topology =
    //        question.getInitial()
    //            ? topologyProvider.getInitialLayer3Topology(snapshot)
    //            : topologyProvider.getLayer3Topology(snapshot);
    //    Collection<Row> sessions =
    //        generateRows(
    //            configurations,
    //            snapshot,
    //            topology,
    //            batfish.getTopologyProvider(),
    //            includeNodes,
    //            includeRemoteNodes,
    //            question.getEdgeType(),
    //            question.getInitial());
    // =================================================================================== //

    String COL_NODE = "Node";
    String COL_REMOTE_NODE = "Remote_Node";
    String COL_AS_NUMBER = "AS_Number";
    String COL_REMOTE_AS_NUMBER = "Remote_AS_Number";
    String COL_IP = "IP";
    String COL_REMOTE_IP = "Remote_IP";

    for (Row row : sessions) {
      Ip srcIp = row.getIp(COL_IP);
      Ip dstIp = row.getIp(COL_REMOTE_IP);

      String srcNodeName =
          row.get(COL_NODE).get("name") != null
              ? row.get(COL_NODE).get("name").textValue().toLowerCase()
              : null;

      if (srcIp == null && srcNodeName != null && configs.containsKey(srcNodeName)) {
        srcIp = configs.get(srcNodeName).getDefaultVrf().getBgpProcess().getRouterId();
      }

      String dstNodeName =
          row.get(COL_REMOTE_NODE).get("name") != null
              ? row.get(COL_REMOTE_NODE).get("name").textValue().toLowerCase()
              : null;

      if (dstIp == null && dstNodeName != null && configs.containsKey(dstNodeName)) {
        dstIp = configs.get(dstNodeName).getDefaultVrf().getBgpProcess().getRouterId();
      }

      if (srcIp == null || dstIp == null) {
        continue;
      }

      Node srcNode =
          srcNodeName == null
              ? null
              : nodeByName.computeIfAbsent(srcNodeName, k -> new Node(srcNodeName));

      Node dstNode =
          dstNodeName == null
              ? null
              : nodeByName.computeIfAbsent(dstNodeName, k -> new Node(dstNodeName));

      NamedIp srcKey = new NamedIp(srcIp, srcNodeName);
      NamedIp dstKey = new NamedIp(dstIp, dstNodeName);

      boolean eBGP =
          !Objects.equals(row.getString(COL_AS_NUMBER), row.getString(COL_REMOTE_AS_NUMBER));

      if (edges.containsKey(srcKey) && edges.get(srcKey).containsKey(dstKey)) {
        throw new BatfishException("Expected to have a unique connection");
      } else {
        edges
            .computeIfAbsent(srcKey, k -> new HashMap<>())
            .put(dstKey, new Edge(srcIp, dstIp, eBGP));
        edges.get(srcKey).get(dstKey).setSrcNode(srcNode);
        edges.get(srcKey).get(dstKey).setDstNode(dstNode);
        if (dstNode != null) {
          dstNode.addIncomingNeighbor(edges.get(srcKey).get(dstKey));
        }
      }
    }

    Map<Configuration, Collection<RoutingPolicy>> relevantPolicies = new HashMap<>();

    for (String upperCaseNodeName : configs.keySet()) {
      String nodeName = upperCaseNodeName.toLowerCase();

      if (!nodeByName.containsKey(nodeName)) {
        nodeByName.put(nodeName, new Node(nodeName));
      }

      Configuration config = configs.get(upperCaseNodeName);
      relevantPolicies.put(config, new HashSet<>());
      if (config.getDefaultVrf() == null || config.getDefaultVrf().getBgpProcess() == null) {
        continue;
      }
      BgpProcess bgp = config.getDefaultVrf().getBgpProcess();
      bgp.getActiveNeighbors()
          .forEach(
              (neighborIp, session) -> {
                Ipv4UnicastAddressFamily unicast = session.getIpv4UnicastAddressFamily();
                if (!isNull(unicast) && !isNull(config.getRoutingPolicies())) {
                  boolean eBGP =
                      !(session.getLocalAs() == null
                          || session.getRemoteAsns().contains(session.getLocalAs()));
                  Ip nodeIp = firstNonNull(session.getLocalIp(), bgp.getRouterId());

                  Optional<Edge> incomingOption =
                      nodeByName.get(nodeName).getIncoming(neighborIp, nodeIp);
                  Edge incoming = incomingOption.orElse(new Edge(neighborIp, nodeIp, eBGP));
                  if (incomingOption.isEmpty()) { // this means new edge was created
                    incoming.setDstNode(nodeByName.get(nodeName));
                    nodeByName.get(nodeName).addIncomingNeighbor(incoming);
                    NamedIp srcKey = new NamedIp(neighborIp, null);
                    NamedIp dstKey = new NamedIp(nodeIp, nodeName);
                    Edge check =
                        edges.computeIfAbsent(srcKey, k -> new HashMap<>()).put(dstKey, incoming);
                    if (check != null) {
                      throw new BatfishException("Edge (with node + ip combo) is not distinct");
                    }
                  }
                  Edge outgoing = incoming.flipEdge();

                  if (outgoing.isEBGP() && !outgoing.hasDstNode()) {
                    externalOutgoing.add(outgoing);
                  }

                  if (!isNull(unicast.getImportPolicy())
                      && !isNull(config.getRoutingPolicies().get(unicast.getImportPolicy()))) {
                    imports.put(
                        incoming, config.getRoutingPolicies().get(unicast.getImportPolicy()));
                    relevantPolicies.get(config).add(imports.get(incoming));
                  }
                  if (!isNull(unicast.getExportPolicy())
                      && !isNull(config.getRoutingPolicies().get(unicast.getExportPolicy()))) {
                    exports.put(
                        outgoing, config.getRoutingPolicies().get(unicast.getExportPolicy()));
                    relevantPolicies.get(config).add(exports.get(outgoing));
                  }
                }
              });
    }

    ConfigAtomicPredicates configAtomicPredicates =
        getConfigAtomicPredicates(communityRegexes, asPathRegexes, relevantPolicies);

    this.tbdd = new TransferBDD(configAtomicPredicates);
    this.defaultIncoming =
        defaultIncoming == null ? new Invariant(this.tbdd) : defaultIncoming.build(this.tbdd, null);

    // default assumption for incoming edges in the checkedAssumptions
    for (Node node : nodeByName.values()) {
      node.getAllIncomingEdges()
          .forEach(
              edge -> {
                if (!edge.hasSrcNode()) {
                  this.checkedAssumptions.put(edge, this.defaultIncoming);
                }
              });
    }

    int edgesCount =
        nodeByName.values().stream().mapToInt(n -> n.getAllIncomingEdges().size()).sum();
    LOGGER.info("Nodes in Network: {}, Edges in Network: {}", nodeByName.size(), edgesCount);
  }
}
