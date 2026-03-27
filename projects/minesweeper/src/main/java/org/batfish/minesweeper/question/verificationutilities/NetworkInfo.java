package org.batfish.minesweeper.question.verificationutilities;

import net.sf.javabdd.BDD;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.batfish.common.BatfishException;
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
import org.batfish.minesweeper.question.liveness.InterferenceCheck;
import org.batfish.minesweeper.question.liveness.Path;
import org.batfish.minesweeper.question.liveness.PathAnalyzer;
import org.batfish.minesweeper.question.safety.Infer;
import org.batfish.minesweeper.question.searchroutepolicies.RegexConstraint;

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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.Objects.isNull;
import static java.util.Objects.nonNull;
import static org.batfish.minesweeper.question.verificationutilities.Setup.getConfigAtomicPredicates;
import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_locations;

public class NetworkInfo {
  private static final Logger LOGGER = LogManager.getLogger(NetworkInfo.class);

  public final TransferBDD tbdd;
  public final Invariant defaultIncoming;

  private final Map<Ip, Node> nodes = new HashMap<>();
  private final Set<Location> locations = new HashSet<>();
  private final Map<Edge, RoutingPolicy> imports = new HashMap<>();
  private final Map<Edge, RoutingPolicy> exports = new HashMap<>();

  /// Assumptions on edges where we do not have the config for the source of the edge
  private final Map<Location, Invariant> checkedAssumptions = new HashMap<>();
  /// Assumptions on nodes in network or edges originating within network
  private final Map<Location, Invariant> enforcedAssumptions = new HashMap<>();

  // information to deal with internal/external ASN
  private final Set<Location> externalOutgoing = new HashSet<>();

  /// Processes the provided config files to determine the network's topology and relevant
  /// information, returns a map including the relevant RoutingPolicies
  private Map<Configuration, Collection<RoutingPolicy>> processConfigs(
      @Nonnull Map<String, Configuration> configs) {
    LOGGER.info("Processing each config provided...");
    Map<Configuration, Collection<RoutingPolicy>> policies = new HashMap<>();

    for (String nodeName : configs.keySet()) {
      Configuration config = configs.get(nodeName);
      policies.put(config, new HashSet<>());
      // no need to evaluate any configs which are null or don't yield anything
      if (isNull(config) || isNull(config.getVrfs())) {
        continue;
      }
      // filter out any null VRFs and only keep default
      Stream<Vrf> forwarding =
          config.getVrfs().values().stream()
              .filter(vrf -> nonNull(vrf) && vrf.getName().equals("default"));
      // gets the bgp processes and filters out any null processes
      List<BgpProcess> bgpProcesses =
          forwarding.map(Vrf::getBgpProcess).filter(Objects::nonNull).toList();
      // note, getRouterId's return value is Nonnull
      Set<Ip> nodeIps =
          bgpProcesses.stream()
              .map(BgpProcess::getRouterId)
              .filter(ip -> !ip.equals(Ip.ZERO))
              .collect(Collectors.toSet());
      // gather the policies
      bgpProcesses.stream()
          .flatMap(proc -> proc.getActiveNeighbors().entrySet().stream())
          // make sure any null neighbors are filtered out, and filter out any node without an ip
          // address
          .filter(
              entry ->
                  nonNull(entry)
                      // make sure entry doesn't have nulls
                      && nonNull(entry.getKey())
                      && nonNull(entry.getValue())
                      // if the local IP address is 0.0.0.0, we remove
                      && (entry.getValue().getLocalIp() == null
                          || !entry.getValue().getLocalIp().equals(Ip.ZERO))
                      // make sure there is a relevant IP
                      && (nodeIps.stream().findFirst().isPresent()
                          || nonNull(entry.getValue().getLocalIp())))
          .forEach(
              entry -> {
                assert nodeIps.stream().findFirst().isPresent()
                    || nonNull(entry.getValue().getLocalIp());
                Ip nodeIp =
                    nonNull(entry.getValue().getLocalIp())
                        ? entry.getValue().getLocalIp()
                        : nodeIps.stream().findFirst().get();
                nodeIps.add(nodeIp);
                assert !nodeIp.equals(Ip.ZERO);

                // TODO this may need to be updated
                // currently we determine that a session is EBGP if the local ASN is not in the list
                // of remote ASNs
                boolean eBGP =
                    !(entry.getValue().getLocalAs() == null
                        || entry
                            .getValue()
                            .getRemoteAsns()
                            .contains(entry.getValue().getLocalAs()));
                Edge incoming = new Edge(entry.getKey(), nodeIp, eBGP);
                Edge outgoing = new Edge(nodeIp, entry.getKey(), eBGP);
                if (eBGP) {
                  // to keep traffic of all outgoing edges
                  this.externalOutgoing.add(outgoing);
                }
                Ipv4UnicastAddressFamily unicast = entry.getValue().getIpv4UnicastAddressFamily();
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
                // add anywhere edge is going into this node (i.e. the incoming edge above)
                locations.add(new Edge(entry.getKey(), nodeIp, eBGP));
              });
      Node node = new Node(nodeIps, nodeName);
      locations.add(node); // add node
      nodeIps.forEach(nodeIp -> nodes.put(nodeIp, node));
    }

    assert this.externalOutgoing.stream().allMatch(l -> l instanceof Edge);
    return policies;
  }

  public NetworkInfo(
      @Nonnull Map<String, Configuration> configs,
      @Nonnull Set<RegexConstraint> communityRegexes,
      @Nonnull Set<RegexConstraint> asPathRegexes) {
    this(configs, communityRegexes, asPathRegexes, null);
  }

  public NetworkInfo(
      @Nonnull Map<String, Configuration> configs,
      @Nonnull Set<RegexConstraint> communityRegexes,
      @Nonnull Set<RegexConstraint> asPathRegexes,
      @Nullable Invariant.Builder defaultIncoming) {
    Map<Configuration, Collection<RoutingPolicy>> relevantPolicies = processConfigs(configs);
    LOGGER.info("Creating ConfigAtomicPredicates for TransferBDD...");
    ConfigAtomicPredicates configAtomicPredicates =
        getConfigAtomicPredicates(communityRegexes, asPathRegexes, relevantPolicies);
    LOGGER.info("COMPLETED ConfigAtomicPredicates");
    this.tbdd = new TransferBDD(configAtomicPredicates);
    this.defaultIncoming =
        defaultIncoming == null ? new Invariant(this.tbdd) : defaultIncoming.build(this.tbdd, null);
    // default assumption for incoming edges in the checkedAssumptions
    for (Location location : locations) {
      if (location instanceof Edge edge
          && (isIncomingEdge(edge) || !this.nodes.containsKey(edge.getSrc()))) {
        checkedAssumptions.put(edge, this.defaultIncoming);
      }
    }
    LOGGER.info("COMPLETED NetworkInfo");
  }

  public NetworkInfo(@Nonnull TransferBDD tbdd, @Nonnull Map<String, Configuration> configs) {
    this(tbdd, configs, new Invariant(tbdd));
  }

  public NetworkInfo(
      @Nonnull TransferBDD tbdd,
      @Nonnull Map<String, Configuration> configs,
      @Nonnull Invariant defaultIncoming) {
    this.tbdd = tbdd;
    this.defaultIncoming = defaultIncoming;
    processConfigs(configs);
    // default assumption of True for incoming edges
    for (Location location : locations) {
      if (location instanceof Edge edge) {
        // if the edge's source is not in the set of nodes (i.e. out of network)
        if (!nodes.containsKey(edge.getSrc())) {
          checkedAssumptions.put(edge, defaultIncoming);
        }
      }
    }
  }

  /// String representation of the provided location within context of the network (ie using node
  // names
  /// when possible in place of ip addresses)
  public String locationStr(Location loc) {
    return loc.contextString(this.nodes);
  }

  /// Returns the assumptions that should be checked of the network
  public Map<Location, Invariant> getCheckedAssumptions() {
    return checkedAssumptions;
  }

  /// Returns the assumptions of the network that are enforced in inference
  public Map<Location, Invariant> getEnforcedAssumptions() {
    return enforcedAssumptions;
  }

  /// Returns set of all ips associated with a provided node (via node's name)
  public Optional<Collection<Ip>> ipsFromNodeName(String name) {
    for (Location location : locations) {
      if (location instanceof Node node && node.getName().equals(name)) {
        return Optional.of(node.getIps());
      }
    }
    return Optional.empty();
  }

  /// Returns boolean indicating if network contains this edge
  public boolean containsEdge(Edge edge) {
    return imports.containsKey(edge) || exports.containsKey(edge) || locations.contains(edge);
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
    RoutingPolicy policy;
    assert location instanceof Edge || location instanceof Node;
    boolean getImportPolicy = (location instanceof Edge) != wpQuery;
    if (location instanceof Node node) {
      policy = this.getPolicy(this.getAnyIncomingEdge(node), getImportPolicy);
    } else {
      policy = this.getPolicy((Edge) location, getImportPolicy);
    }
    return inv.build(this.tbdd, policy);
  }

  /// Included for pybatfish question development
  public Edge getAnyIncomingEdge(Node node) {
    for (Location location : locations) {
      if (location instanceof Edge edge) {
        if (edge.isDst(node)) {
          return edge.copy();
        }
      }
    }
    return null;
  }

  public Set<Location> getAllIncomingEdges(Node node) {
    Set<Location> incoming = new HashSet<>();
    for (Location location : locations) {
      if (location instanceof Edge edge) {
        if (edge.isDst(node)) {
          incoming.add(edge.copy());
        }
      }
    }
    return incoming;
  }

  public Set<Location> getAllIncomingEdges(Ip ip) {
    if (nodes.containsKey(ip)) {
      return this.getAllIncomingEdges(nodes.get(ip));
    } else {
      Set<Location> incoming = new HashSet<>();
      for (Location location : locations) {
        if (location instanceof Edge edge) {
          if (edge.getDst().equals(ip)) {
            incoming.add(edge.copy());
          } else if (edge.getSrc().equals(ip)) {
            incoming.add(edge.flipEdge());
          }
        }
      }
      return incoming;
    }
  }

  public Set<Location> getAllOutgoingEdges(Node node) {
    Set<Location> outgoing = new HashSet<>();
    for (Location location : locations) {
      if (location instanceof Edge edge) {
        if (edge.isDst(node)) {
          outgoing.add(edge.flipEdge());
        }
      }
    }
    return outgoing;
  }

  public Set<Location> getAllOutgoingEdges(Ip ip) {
    if (nodes.containsKey(ip)) {
      return this.getAllOutgoingEdges(nodes.get(ip));
    } else {
      Set<Location> outgoing = new HashSet<>();
      for (Location location : locations) {
        if (location instanceof Edge edge) {
          if (edge.getDst().equals(ip)) {
            outgoing.add(edge.flipEdge());
          } else if (edge.getSrc().equals(ip)) {
            outgoing.add(edge.copy());
          }
        }
      }
      return outgoing;
    }
  }

  /// Used to add an assumption which indicates any traffic is possible at provided location
  public NetworkInfo anyRouteAllowedAt(Location anchor) {
    //    return this.addAssumption(anchor, new Invariant(this.tbdd));
    this.checkedAssumptions.put(anchor, new Invariant(this.tbdd));
    return this;
  }

  /// Checks according to ASN if applicable, otherwise checks if we have a config for the
  /// destination (ONLY USED FOR VERIFYING PROPERTY GOING OUT ON ALL EXTERNAL EDGES)
  public Set<Location> allOutgoingEdges() {
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
    return outgoing;
  }

  /// Checks according to ASN if applicable, otherwise checks if we have a config for the
  /// destination
  private boolean isOutgoingEdge(Location location) {
    if (location instanceof Edge edge) {
      if (externalOutgoing.isEmpty()) {
        return !nodes.containsKey(edge.getDst());
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
    if (locations.contains(location)
        || (location instanceof Edge e && nodes.containsKey(e.getSrc()))) {
      boolean noConfigAtSource = location instanceof Edge e && !nodes.containsKey(e.getSrc());
      // check if edge is coming from external node or if we do not have a config for source
      // TODO would there ever be an external node we don't have config for?
      if (isIncomingEdge(location) || noConfigAtSource) {
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
    return new Lightyear(this.nodes, this.imports, this.exports);
  }

  private Map<Node, Set<Edge>> getEdgesByDestination() {
    Map<Node, Set<Edge>> edgesByDestination = new HashMap<>();
    for (Location loc : this.locations) {
      if (loc instanceof Edge edge && this.nodes.containsKey(edge.getDst())) {
        Node dst = this.nodes.get(edge.getDst());
        if (!edgesByDestination.containsKey(dst)) {
          edgesByDestination.put(dst, new HashSet<>());
        }
        edgesByDestination.get(dst).add(edge);
      }
    }
    return edgesByDestination;
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
    return new Infer(context, this.nodes, this.getEdgesByDestination());
  }

  /// Returns a PathAnalyzer objective reflective of the network which can be used for verification
  /// of the provided liveness property (pertaining to the provided prefix space)
  public PathAnalyzer toPathAnalyzer(PrefixSpace prefix, Location location, Invariant target) {
    Path.Context context =
        new Path.Context(
            this.tbdd,
            this.checkedAssumptions,
            this.enforcedAssumptions,
            this.imports,
            this.exports,
            this.defaultIncoming);
    return new PathAnalyzer(
        context, prefix, location, target, this.nodes, this.getEdgesByDestination());
  }

  /// Returns a PathAnalyzer objective reflective of the network which can be used for interference
  /// of the provided liveness property (pertaining to the provided prefix space)
  public InterferenceCheck toInterferenceCheck(
      PrefixSpace prefix, Location location, Invariant target) {
    Path.Context context =
        new Path.Context(
            this.tbdd,
            this.checkedAssumptions,
            this.enforcedAssumptions,
            this.imports,
            this.exports,
            this.defaultIncoming);
    return new InterferenceCheck(
        context, prefix, location, target, this.nodes, this.getEdgesByDestination());
  }

  /// Returns TableAnswerElement which lists all locations within the network (used when no target
  /// property is provided)
  public TableAnswerElement getAnswerElement() {
    TableAnswerElement tae = new TableAnswerElement(metadata_locations());
    Map<String, Set<String>> nodeNameToEdges = new HashMap<>();
    nodes.values().forEach(node -> nodeNameToEdges.put(node.contextString(nodes), new HashSet<>()));

    locations.forEach(
        loc -> {
          if (loc instanceof Edge edge) {
            String src =
                nodes.containsKey(edge.getSrc())
                    ? nodes.get(edge.getSrc()).contextString(nodes)
                    : edge.getSrc().toString();
            String dst =
                nodes.containsKey(edge.getDst())
                    ? nodes.get(edge.getDst()).contextString(nodes)
                    : edge.getDst().toString();
            if (nodeNameToEdges.containsKey(src)) {
              nodeNameToEdges.get(src).add(dst);
            }
            if (nodeNameToEdges.containsKey(dst)) {
              nodeNameToEdges.get(dst).add(src);
            }
          }
        });

    nodeNameToEdges.keySet().stream()
        .sorted()
        .forEach(
            node ->
                tae.addRow(
                    Row.builder()
                        .put(Setup.NODES_COL, node)
                        .put(Setup.NEIGHBORS_COL, nodeNameToEdges.get(node))
                        .build()));

    Set<String> externals = new HashSet<>();
    AtomicInteger externalEdgeCount = new AtomicInteger();
    this.allOutgoingEdges()
        .forEach(
            loc -> {
              if (loc instanceof Edge e) {
                externals.add(e.getDst().toString());
                externalEdgeCount.addAndGet(1);
              }
            });

    tae.addRow(
        Row.builder()
            .put(
                Setup.NODES_COL,
                "EXTERNAL NEIGHBORS ("
                    + externals.size()
                    + " distinct neighbors, "
                    + externalEdgeCount
                    + " distinct edges)")
            .put(Setup.NEIGHBORS_COL, externals.stream().sorted().collect(Collectors.toList()))
            .build());

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
}
