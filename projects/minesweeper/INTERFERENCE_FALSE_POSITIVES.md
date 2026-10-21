# Where the reachability interference check is too strong

This note covers pure reachability queries (target `true` at a location, plus a prefix) on which
`ReachabilityAnswerer.run` reports interference although, in real BGP, the target always ends up
with a route for the prefix. The examples are tests in
`src/test/java/org/batfish/minesweeper/question/reachability/`:

- `InterferenceFalsePositiveTest`: small hand-built networks, one test per case. Where the check
  is wrong today, the interference assertion is commented out with a TODO.
- `InterferenceRepoExampleTest`: the existing `weakerPathConstraints` network.
- `InterferenceDiagnosticsTest`: prints the path constraints and the inferred invariants for
  each network, which shows where each report comes from.

## What the check requires

1. `PathExploration` picks one good path: the first shortest path from an ingress along which
   every route the ingress assumption allows reaches the target.
2. For each node on that path, its *path constraint* is the set of routes at that node that the
   rest of the good path's policies deliver to the target. These are computed with denied routes
   excluded, so a route that some later hop on the good path would drop violates the constraint.
3. `Infer` then requires that every route that can ever be at each of those nodes satisfies the
   node's path constraint. It reports interference if an ingress assumption allows a route that
   would violate a requirement. `Infer` runs with pushFalse set, so a requirement of false at
   some location does not stop it; the false is pushed back to the ingresses like any other
   requirement. (The "Dead End" report in `ReachabilityAnswerer.run` therefore never fires.)
4. Route preference: the requirement at a node on the good path is relaxed to also allow any
   route that is less preferred (by weight, local-pref, then AS-path length) than every good
   route that reaches that node, since such a route is never selected there.

This is sound. Whatever route each node on the good path selects is carried one more hop, so the
target gets a route. But it protects one particular path at every hop, which is stronger than
reachability needs. The false positives below are all cases where the prefix reaches the target
for some other reason.

The base network for the examples:

```
E1 --import: clear communities--> A --T's import: deny 2:2--> T
E2 --import: accept unchanged-----> A --> B --> T     (B and T accept everything)
```

The query is target `true` at T, prefix 2.4.8.0/24. E2's routes may carry 2:2. The good path is
E1 -> A -> T.

## 1. Another path delivers the competing route

Tests: `base`, `baseIngressE1`, `parallelSessionSwapped`, `parallelSessionSwappedIngressE1`,
`cE2AtBIngressE1`, and variations 1 and 2 of `InterferenceRepoExampleTest`.

A route from E2 that carries 2:2 can be at A, and T's import from A drops it. So it violates A's
path constraint, and interference is reported from E2. In reality T always has the prefix. If A
selects E1's route, T gets it directly. If A selects E2's route, T drops it on the direct session,
but B delivers it.

- `parallelSessionSwapped` is the two-router form: A and T are joined by two sessions, and only
  the one the good path happens to use filters 2:2. With the filter on the other session
  (`parallelSession`), the check passes. So the verdict depends on which path `PathExploration`
  picks first.
- `cE2AtBIngressE1`: the competing route enters at B rather than A. It fails only when `ingress`
  forces the good path to start at E1. With no ingress given (`cE2AtB`), the good path starts at
  E2 and the check passes.

Controls: `aNoSecondPath` and `a2SecondPathAlsoFilters` remove the second path, or make it filter
2:2 too. There, if A prefers E2's route, T really does lose the prefix, and the check is right to
report interference.

## 2. The competing route is never selected (fixed)

Test: `bLowerLocalPref`. A sets local-pref 200 on E1's routes and 50 on E2's, so A never selects
E2's route while E1's is present, and E2's route never replaces the good route. This was a false
positive before the route-preference reasoning (step 4 above) was added, and it now passes.
Preference only excuses routes that are strictly less preferred than every good route, so a
competing route that ties with the good route is still reported.

## 3. Loops

Test: `eLoopBackTag`. There is one ingress and one path. T's export back to A tags routes 2:2, and
T's import from A drops 2:2. The copy of the good route that T sends back to A violates A's path
constraint, so the requirement at T, and then everywhere upstream, becomes false. That false is
pushed back to E1, and interference is reported at the good path's own ingress, with an arbitrary
(harmless) route as the witness, since no route satisfies false. That witness pattern is the clue
to recognize this case in real output.

In real BGP the copy never comes back. Over eBGP, A rejects it because A's own AS is already in
the path; over iBGP, T does not advertise a route learned over iBGP to another iBGP peer. The
model has neither form of loop prevention. The loop tests in `ReachabilityAnswererTest`
(`ibgpLoopBackNoInterferenceTest`, `ebgpLoopBackNoInterferenceTest`) show the same thing.

Note: for these networks the verdicts are the same if the internal sessions are iBGP instead of
eBGP (`dSessionTypeMatrix`).

## Possible fixes

### Route preference (class 2, partly class 3)

Implemented (step 4 above). It also excuses a competing route that arrives over more eBGP hops
than the good route, but only when the AS-path length of incoming routes is pinned by an
assumption; otherwise every length is possible and nothing is excused on length. With the lengths
pinned at 0, `cE2AtBIngressE1PinnedAsPathLength` (E2's route reaches A one hop later, via B) and
`eLoopBackTagPinnedAsPathLength` (the looped copy has gone two hops further) both pass. It cannot
excuse iBGP loops, or competing routes that arrive over as many hops as the good route (`base`,
the parallel-session cases): those tie with the good route on every attribute compared.

### Try other good paths (some of class 1)

Each good path gives a sound check on its own. So we can try several candidate paths and accept
as soon as one passes, reporting interference only if none does. In `base`, the path
E1 -> A -> B -> T passes: every route A can hold is carried to T through B. The cost is one
`Infer` run per candidate, and the candidates would have to be enumerated, e.g. the k shortest
paths from each ingress.

This is not enough when different routes need different paths. Suppose T's import from A drops
routes tagged 2:2, and B's import from A drops routes tagged 3:3. E2's import tags its routes 2:2
only, and E3's import tags its routes 3:3 only.

- Whatever A selects, T gets the prefix: a 2:2 route goes via B, and a 3:3 route goes direct.
- But no single path passes. Checking E1 -> A -> T fails, because a 2:2 route can be at A and that
  path drops it. Checking E1 -> A -> B -> T fails, because a 3:3 route can be at A and that path
  drops it.

So "one path with no interference" never succeeds here, even though there is no interference.
(This example is not yet a test.)

### Combine paths: a ranked set of routers (class 1)

Replace "the good path" with a set S of routers that contains the target, and give each a rank,
with the target at 0. Compute requirements from the target backwards:

- The target's requirement is the target property.
- The requirement of any other router n in S is the set of routes that at least one router m in S
  with lower rank accepts from n as a route meeting m's requirement. That is, the union over such
  m of the weakest precondition of n -> m (export then import, denied routes excluded) of m's
  requirement.

Then check with `Infer`, as now, that every route that can be at a router in S meets its
requirement, and that the ingress assumption meets the first router's.

Why this is sound: suppose the target has no route. Of the routers in S that do have a route, take
one with the lowest rank. The good ingress guarantees there is at least one such router. Its
selected route meets its requirement, so some lower-ranked router in S accepts that route and
therefore also has a route. That contradicts the choice of the lowest rank.

The current check is the special case where S is the good path and the rank is the distance along
it. With T = 0, B = 1, A = 2, this handles both `base` and the 2:2/3:3 example.

The open question is how to choose S and the ranks. Hop distance to the target does not work
here: A and B are both one hop from T, so the A -> B edge does not go down in rank. One option is
to rank by position in the union of several candidate good paths. The ranks only need to be
strictly decreasing along the edges used, and the union must not form a cycle.

### Model loop prevention (class 3)

- iBGP split horizon and route reflection: carry one more bit in the route, "learned over iBGP",
  set on iBGP edges, and do not let such a route be exported to an iBGP peer unless the sender is
  a route reflector and the peer is a client.
- AS-path loop detection is harder. The eBGP prepend currently changes only the modeled AS-path
  length, not the AS-path regex atomic predicates, so the modeled path never actually contains the
  router's own AS. We would need a predicate per internal AS ("the path contains AS x"), set on
  export from a router in AS x and checked on import into AS x.
