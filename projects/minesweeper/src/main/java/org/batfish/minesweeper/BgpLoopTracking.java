package org.batfish.minesweeper;

import com.google.common.collect.ImmutableList;
import java.util.List;
import javax.annotation.Nonnull;
import org.batfish.datamodel.Ip;

/**
 * The parts of BGP's loop-prevention state that a symbolic route tracks (see {@link
 * org.batfish.minesweeper.bdd.BDDRoute}), for clients that model BGP's own behavior between
 * routers:
 *
 * <ul>
 *   <li>{@code ases}: the AS numbers for which the route tracks whether its AS path contains them
 *   <li>{@code confedAses}: the confederation member AS numbers for which the route tracks whether
 *       its AS path contains them in a confederation segment
 *   <li>{@code clusterIds}: the route-reflection cluster IDs for which the route tracks whether its
 *       cluster list contains them
 *   <li>{@code routerIds}: the router IDs that the route's originator ID is told apart from; any
 *       other originator ID is represented by a single "other" value
 * </ul>
 */
public record BgpLoopTracking(
    @Nonnull List<Long> ases,
    @Nonnull List<Long> confedAses,
    @Nonnull List<Long> clusterIds,
    @Nonnull List<Ip> routerIds) {
  public static final BgpLoopTracking NONE =
      new BgpLoopTracking(
          ImmutableList.of(), ImmutableList.of(), ImmutableList.of(), ImmutableList.of());

  public BgpLoopTracking {
    ases = ImmutableList.copyOf(ases);
    confedAses = ImmutableList.copyOf(confedAses);
    clusterIds = ImmutableList.copyOf(clusterIds);
    routerIds = ImmutableList.copyOf(routerIds);
  }
}
