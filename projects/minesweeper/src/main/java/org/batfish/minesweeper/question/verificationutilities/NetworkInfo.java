package org.batfish.minesweeper.question.verificationutilities;

import org.batfish.datamodel.BgpProcess;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.datamodel.Vrf;
import org.batfish.datamodel.bgp.Ipv4UnicastAddressFamily;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.table.Row;
import org.batfish.datamodel.table.TableAnswerElement;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.batfish.minesweeper.question.liveness.InterferenceCheck;
import org.batfish.minesweeper.question.liveness.Path;
import org.batfish.minesweeper.question.liveness.PathAnalyzer;
import org.batfish.minesweeper.question.safety.Infer;

import javax.annotation.Nonnull;
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

import static java.util.Objects.isNull;
import static java.util.Objects.nonNull;
import static org.batfish.minesweeper.question.verificationutilities.Setup.metadata_locations;

public class NetworkInfo {
    public final TransferBDD tbdd;

    private final Map<Ip, Node> nodes = new HashMap<>();
    private final Set<Location> locations = new HashSet<>();
    private final Map<Edge, RoutingPolicy> imports = new HashMap<>();
    private final Map<Edge, RoutingPolicy> exports = new HashMap<>();
    private final Map<Location, Invariant> assumptions = new HashMap<>();

    /// Processes the provided config files to determine the network's topology and relevant information
    private void processConfigs(@Nonnull Map<String, Configuration> configs) {
        for (String nodeName : configs.keySet()) {
            Configuration config = configs.get(nodeName);
            // no need to evaluate any configs which are null or don't yield anything
            if (isNull(config) || isNull(config.getVrfs())) continue;
            // filter out any null VRFs
            Stream<Vrf> forwarding = config.getVrfs().values().stream().filter(Objects::nonNull);
            // gets the bgp processes and filters out any null processes
            List<BgpProcess> bgpProcesses = forwarding.map(Vrf::getBgpProcess).filter(Objects::nonNull).toList();
            // note, getRouterId's return value is Nonnull
            Set<Ip> nodeIps = bgpProcesses.stream().map(BgpProcess::getRouterId).collect(Collectors.toSet());
            // gather the policies
            bgpProcesses.stream().flatMap(proc -> proc.getActiveNeighbors().entrySet().stream())
                    // make sure any null neighbors are filtered out, and filter out any node without an ip address
                    .filter(entry -> nonNull(entry) && nonNull(entry.getKey()) && nonNull(entry.getValue()) &&
                            (nodeIps.stream().findFirst().isPresent() || nonNull(entry.getValue().getLocalIp())))
                    .forEach(entry -> {
                        // at least one of these will be non-null based on filter, null pointer exception should never be thrown
                        Ip nodeIp = nonNull(entry.getValue().getLocalIp()) ?
                                entry.getValue().getLocalIp() : nodeIps.stream().findFirst().get();
                        nodeIps.add(nodeIp);
                        Edge incoming = new Edge(entry.getKey(),nodeIp);
                        Edge outgoing = new Edge(nodeIp,entry.getKey());
                        Ipv4UnicastAddressFamily unicast = entry.getValue().getIpv4UnicastAddressFamily();
                        imports.put(incoming,isNull(unicast) || isNull(unicast.getImportPolicy())
                                || isNull(config.getRoutingPolicies()) || isNull(config.getRoutingPolicies().get(unicast.getImportPolicy()))
                                ? new RoutingPolicy("from null",config)
                                : config.getRoutingPolicies().get(unicast.getImportPolicy()));
                        exports.put(outgoing,isNull(unicast) || isNull(unicast.getExportPolicy())
                                || isNull(config.getRoutingPolicies()) || isNull(config.getRoutingPolicies().get(unicast.getExportPolicy()))
                                ? new RoutingPolicy("from null",config)
                                : config.getRoutingPolicies().get(unicast.getExportPolicy()));
                        // add anywhere edge is going into this node (i.e. the incoming edge above)
                        locations.add(new Edge(entry.getKey(),nodeIp));
                    });
            Node node = new Node(nodeIps,nodeName);
            locations.add(node); // add node
            nodeIps.forEach(nodeIp -> nodes.put(nodeIp,node));
        }
    }

    public NetworkInfo(@Nonnull TransferBDD tbdd, @Nonnull Map<String, Configuration> configs) {
        this.tbdd = tbdd;
        processConfigs(configs);
        // default assumption of True for incoming edges
        for (Location location : locations) {
            if (location instanceof Edge edge) {
                // if the edge's source is not in the set of nodes (i.e. out of network)
                if (!nodes.containsKey(edge.getSrc())) {
                    assumptions.put(edge,new Invariant(tbdd));
                }
            }
        }
    }

    /// String representation of the provided location within context of the network (ie using node names
    /// when possible in place of ip addresses)
    public String locationStr(Location loc) { return loc.contextString(this.nodes); }

    /// Returns the assumptions of the network
    public Map<Location, Invariant> getAssumptions() { return assumptions; }

    /// Returns set of all ips associated with a provided node (via node's name)
    public Optional<Collection<Ip>> ipsFromNodeName(String name) {
        for (Location location : locations) {
            if (location instanceof Node node && node.getName().equals(name))
                return Optional.of(node.getIps());
        }
        return Optional.empty();
    }

    /// Returns boolean indicating if the provided edge has an policy associated with it
    public boolean containsPolicy(Edge edge) {
        return imports.containsKey(edge) || exports.containsKey(edge);
    }

    /// Returns the policy (getImport flag indicates import or export) associated with the provided edge
    public RoutingPolicy getPolicy(Edge location, boolean getImport) {
        if (getImport) {
            return imports.getOrDefault(location,null);
        } else {
            return exports.getOrDefault(location,null);
        }
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

    /// Used to add an assumption which indicates any traffic is possible at provided location
    public NetworkInfo anyRouteAllowedAt(Location anchor) {
        return this.addAssumption(anchor,new Invariant(this.tbdd));
    }

    /// Used to add an assumption pertaining to traffic at provided location
    public NetworkInfo addAssumption(@Nonnull Location location, @Nonnull Invariant assumption) {
        assumptions.put(location,assumption);
        return this;
    }

    /// Used to add an assumption pertaining to traffic at provided location
    public void addAssumption(@Nonnull Location.Builder locationBuilder, @Nonnull Invariant.Builder assumption) {
        Location location = locationBuilder.instantiate(this);
        RoutingPolicy policy;
        if (location instanceof Node node) {
            Optional<Edge> incoming = imports.keySet().stream().filter(e -> e.isDst(node)).findFirst();
            if (incoming.isPresent()) {
                policy = imports.get(incoming.get());
            } else {
                Optional<Edge> outgoing = exports.keySet().stream().filter(e -> e.isSrc(node)).findFirst();
                policy = outgoing.map(imports::get).orElse(null);
            }
        } else {
            assert location instanceof Edge;
            policy = exports.getOrDefault(location,imports.getOrDefault(location,null));
        }
        this.addAssumption(location,assumption.build(tbdd,policy));
    }

    /// Creates instance of Lightyear objection, which can be used as a sanity check
    public Lightyear checker() {
        return new Lightyear(this.tbdd,this.nodes,this.imports,this.exports);
    }

    /// Returns an Infer object reflective of the network which can be used for safety property verification
    public Infer toInfer() {
        Path.Context context = new Path.Context(this.tbdd,this.assumptions,this.imports,this.exports);
        return new Infer(context,this.nodes,this.locations);
    }

    /// Returns a PathAnalyzer objective reflective of the network which can be used for verification of the provided
    /// liveness property (pertaining to the provided prefix space)
    public PathAnalyzer toPathAnalyzer(PrefixSpace prefix, Location location, Invariant target) {
        Path.Context context = new Path.Context(this.tbdd,this.assumptions,this.imports,this.exports);
        Map<Node,Set<Edge>> edgesByDestination = new HashMap<>();
        for (Location loc : this.locations) {
            if (loc instanceof Edge edge && this.nodes.containsKey(edge.getDst())) {
                Node dst = this.nodes.get(edge.getDst());
                if (!edgesByDestination.containsKey(dst)) edgesByDestination.put(dst,new HashSet<>());
                edgesByDestination.get(dst).add(edge);
            }
        }
        return new PathAnalyzer(context,prefix,location,target, this.nodes, edgesByDestination);
    }

    /// Returns a PathAnalyzer objective reflective of the network which can be used for interference of the provided
    /// liveness property (pertaining to the provided prefix space)
    public InterferenceCheck toInterferenceCheck(PrefixSpace prefix, Location location, Invariant target) {
        Path.Context context = new Path.Context(this.tbdd,this.assumptions,this.imports,this.exports);
        Map<Node,Set<Edge>> edgesByDestination = new HashMap<>();
        for (Location loc : this.locations) {
            if (loc instanceof Edge edge && this.nodes.containsKey(edge.getDst())) {
                Node dst = this.nodes.get(edge.getDst());
                if (!edgesByDestination.containsKey(dst)) edgesByDestination.put(dst,new HashSet<>());
                edgesByDestination.get(dst).add(edge);
            }
        }
        return new InterferenceCheck(context,prefix,location,target, this.nodes, edgesByDestination);
    }

    /// Returns TableAnswerElement which lists all locations within the network (used when no target property is provided)
    public TableAnswerElement getAnswerElement() {
        TableAnswerElement tae = new TableAnswerElement(metadata_locations());
        locations.forEach(loc -> tae.addRow(Row.builder().put(Setup.LOCATION_COL, this.locationStr(loc)).build()));
        return tae;
    }

    // CODE BELOW FOR DEBUGGING PURPOSES
    public String displayNodes() {
        StringBuilder builder = new StringBuilder();
        Set<Node> done = new HashSet<>();
        for (Node n : nodes.values().stream().sorted().toList()) {
            if (!done.contains(n)) {
                done.add(n);
                builder.append("\n + ").append(n);
                for (Location l : locations) {
                    if (l instanceof Edge e && e.isSrc(n)) {
                        builder.append("\n    - ").append(e.getDst());
                    }
                }
            }
        }
        return builder.toString();
    }
}
