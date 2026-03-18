package org.batfish.minesweeper.bdd;

import static junit.framework.TestCase.assertEquals;
import static junit.framework.TestCase.assertFalse;
import static junit.framework.TestCase.assertTrue;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import java.util.List;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import org.batfish.common.bdd.MutableBDDInteger;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.junit.Before;
import org.junit.Test;

public class TransferBDDUtilsTest {

  private TransferBDD _tbdd;
  private BDDRoute _freshRoute;

  @Before
  public void setup() {
    ConfigAtomicPredicates configAPs =
        new ConfigAtomicPredicates(
            ImmutableList.of(),
            ImmutableSet.of(CommunityVar.from("30:30"), CommunityVar.from("40:40")),
            ImmutableSet.of());
    _tbdd = new TransferBDD(configAPs);
    _freshRoute = new BDDRoute(_tbdd.getFactory(), configAPs);
  }

  @Test
  public void testWeakestPrecondition() {

    BDDFactory factory = _tbdd.getFactory();

    // no paths
    List<TransferReturn> paths = ImmutableList.of();
    assertEquals(
        TransferBDDUtils.weakestPrecondition(paths, 0, _tbdd, (post, path) -> factory.one()),
        factory.zero());

    // the WP is the identity function
    paths = ImmutableList.of(new TransferReturn(_freshRoute, factory.one(), true));
    assertEquals(
        TransferBDDUtils.weakestPrecondition(
            paths, 0, _tbdd, (post, path) -> path.getOutputRoute().getLocalPref().value(300)),
        _freshRoute.getLocalPref().value(300));

    // ignore denying paths
    paths = ImmutableList.of(new TransferReturn(_freshRoute, factory.one(), false));
    assertEquals(
        TransferBDDUtils.weakestPrecondition(
            paths, 0, _tbdd, (post, path) -> path.getOutputRoute().getLocalPref().value(300)),
        factory.zero());

    // disjoin the conditions on multiple paths
    paths =
        ImmutableList.of(
            new TransferReturn(_freshRoute, _freshRoute.getCommunityAtomicPredicates()[1], true),
            new TransferReturn(_freshRoute, _freshRoute.getCommunityAtomicPredicates()[2], true));
    assertEquals(
        TransferBDDUtils.weakestPrecondition(
            paths, 0, _tbdd, (post, path) -> path.getOutputRoute().getLocalPref().value(300)),
        _freshRoute
            .getLocalPref()
            .value(300)
            .and(
                _freshRoute.getCommunityAtomicPredicates()[1].or(
                    _freshRoute.getCommunityAtomicPredicates()[2])));

    // with state updates
    BDDRoute o1 = new BDDRoute(_freshRoute);
    o1.getLocalPref().setValue(300);
    BDDRoute o2 = new BDDRoute(_freshRoute);
    o2.getLocalPref().setValue(500);
    paths =
        ImmutableList.of(
            // this path sets the local pref to 300, so that condition should not be part of the WP
            new TransferReturn(o1, _freshRoute.getCommunityAtomicPredicates()[1], true),
            // this path sets the local pref to 500 so it is not a feasible path for the given
            // postcondition
            new TransferReturn(o2, _freshRoute.getCommunityAtomicPredicates()[2], true));
    assertEquals(
        TransferBDDUtils.weakestPrecondition(
            paths, 0, _tbdd, (post, path) -> path.getOutputRoute().getLocalPref().value(300)),
        _freshRoute.getCommunityAtomicPredicates()[1]);
  }

  @Test
  public void testDeniedRoutes() {
    BDDFactory factory = _tbdd.getFactory();

    // no paths
    List<TransferReturn> paths = ImmutableList.of();
    assertEquals(TransferBDDUtils.deniedRoutes(paths, _tbdd), factory.zero());

    // no denying paths
    paths = ImmutableList.of(new TransferReturn(_freshRoute, factory.one(), true));
    assertEquals(TransferBDDUtils.deniedRoutes(paths, _tbdd), factory.zero());

    // single denying path
    paths = ImmutableList.of(new TransferReturn(_freshRoute, factory.one(), false));
    assertEquals(TransferBDDUtils.deniedRoutes(paths, _tbdd), factory.one());

    // multiple denying paths
    paths =
        ImmutableList.of(
            new TransferReturn(_freshRoute, _freshRoute.getCommunityAtomicPredicates()[1], false),
            new TransferReturn(_freshRoute, _freshRoute.getCommunityAtomicPredicates()[2], false));
    assertEquals(
        TransferBDDUtils.deniedRoutes(paths, _tbdd),
        _freshRoute.getCommunityAtomicPredicates()[1].or(
            _freshRoute.getCommunityAtomicPredicates()[2]));

    // mixed accepting and denying paths - only denying paths should be included
    paths =
        ImmutableList.of(
            new TransferReturn(_freshRoute, _freshRoute.getCommunityAtomicPredicates()[1], true),
            new TransferReturn(_freshRoute, _freshRoute.getCommunityAtomicPredicates()[2], false));
    assertEquals(
        TransferBDDUtils.deniedRoutes(paths, _tbdd), _freshRoute.getCommunityAtomicPredicates()[2]);
  }

  @Test
  public void testMakeRoutePairing() {
    // Test 1: The pairing is the identity function
    BDDRoute route1 = new BDDRoute(_freshRoute);
    BDDPairing pairing1 = TransferBDDUtils.makeRoutePairing(route1, _tbdd);
    BDD bdd1 = route1.getCommunityAtomicPredicates()[0];
    assertEquals(bdd1.veccompose(pairing1), bdd1);

    // Test 2: The pairing is unrelated to the BDD
    BDDRoute route2 = new BDDRoute(_freshRoute);
    BDD[] commAPs = route2.getCommunityAtomicPredicates();
    commAPs[1] = commAPs[0].or(commAPs[1]);
    BDDPairing pairing2 = TransferBDDUtils.makeRoutePairing(route2, _tbdd);
    BDD bdd2 = route2.getLocalPref().support();
    assertEquals(bdd2.veccompose(pairing2), bdd2);

    // Test 3: The pairing affects the BDD
    BDD bdd3 = commAPs[0].and(commAPs[1]);
    assertEquals(bdd3.veccompose(pairing2), commAPs[0]);
  }

  @Test
  public void testWeakestPreconditionForPathPostCondUpdate() {
    BDDFactory factory = _tbdd.getFactory();

    // make sure the postcondition is not consumed by the function
    TransferReturn path = new TransferReturn(_freshRoute, factory.nithVar(0), true);
    BDD postCond = factory.ithVar(0).and(factory.nithVar(1));
    TransferBDDUtils.weakestPreconditionForPath(path, postCond, (post, p) -> post);
    // the postcondition is updated by the WP call
    assertEquals(postCond, factory.zero());
    // the input constraints are unchanged
    assertEquals(path.getInputConstraints(), factory.nithVar(0));
  }

  @Test
  public void testGetMinValue() {
    TransferBDDUtils utils = new TransferBDDUtils();
    MutableBDDInteger localPref = _freshRoute.getLocalPref();

    // When the BDD is unconstrained (one), the minimum value is 0
    BDD unconstrained = _tbdd.getFactory().one();
    assertEquals(0L, utils.getMinValue(unconstrained, localPref));

    // When the BDD constrains the integer to exactly one value, min equals that value
    BDD exactly100 = localPref.value(100);
    assertEquals(100L, utils.getMinValue(exactly100, localPref));

    // When the BDD constrains the integer to a range (>= 200), the minimum is 200
    BDD atLeast200 = localPref.geq(200);
    assertEquals(200L, utils.getMinValue(atLeast200, localPref));

    // When the BDD is the disjunction of two specific values, min is the smaller one
    BDD val50or300 = localPref.value(50).or(localPref.value(300));
    assertEquals(50L, utils.getMinValue(val50or300, localPref));
  }

  @Test
  public void testGetMaxValue() {
    TransferBDDUtils utils = new TransferBDDUtils();
    MutableBDDInteger localPref = _freshRoute.getLocalPref();
    // local pref is a 32-bit integer, so the max possible value is 2^32 - 1
    long maxUint32 = 0xFFFFFFFFL;

    // When the BDD is unconstrained (one), the maximum value is the largest representable value
    BDD unconstrained = _tbdd.getFactory().one();
    assertEquals(maxUint32, utils.getMaxValue(unconstrained, localPref));

    // When the BDD constrains the integer to exactly one value, max equals that value
    BDD exactly100 = localPref.value(100);
    assertEquals(100L, utils.getMaxValue(exactly100, localPref));

    // When the BDD constrains the integer to a range (<= 500), the maximum is 500
    BDD atMost500 = localPref.leq(500);
    assertEquals(500L, utils.getMaxValue(atMost500, localPref));

    // When the BDD is the disjunction of two specific values, max is the larger one
    BDD val50or300 = localPref.value(50).or(localPref.value(300));
    assertEquals(300L, utils.getMaxValue(val50or300, localPref));
  }

  @Test
  public void testIsMorePreferredBGP_higherWeightWins() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p has weight 200 (min = 200), q has weight 100 (max = 100); p is more preferred
    BDD p = orig.getWeight().value(200);
    BDD q = orig.getWeight().value(100);
    assertTrue(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testIsMorePreferredBGP_lowerWeightLoses() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p has weight 50 (min = 50), q has weight 100 (max = 100); p is not more preferred
    BDD p = orig.getWeight().value(50);
    BDD q = orig.getWeight().value(100);
    assertFalse(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testIsMorePreferredBGP_sameWeightHigherLocalPrefWins() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p and q have the same weight (100), but p has higher local pref (300 vs 200)
    BDD p = orig.getWeight().value(100).and(orig.getLocalPref().value(300));
    BDD q = orig.getWeight().value(100).and(orig.getLocalPref().value(200));
    assertTrue(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testIsMorePreferredBGP_sameWeightLowerLocalPrefLoses() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p and q have the same weight (100), but p has lower local pref (100 vs 200)
    BDD p = orig.getWeight().value(100).and(orig.getLocalPref().value(100));
    BDD q = orig.getWeight().value(100).and(orig.getLocalPref().value(200));
    assertFalse(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testIsMorePreferredBGP_sameWeightSameLocalPref() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p and q have the same weight (100) and the same local pref (200); tie, returns false
    BDD p = orig.getWeight().value(100).and(orig.getLocalPref().value(200));
    BDD q = orig.getWeight().value(100).and(orig.getLocalPref().value(200));
    assertFalse(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testIsMorePreferredBGP_overlappingWeightRanges() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p's weight is in [100..200] (min=100), q's weight is in [150..300] (max=300)
    // min(p) = 100 < max(q) = 300 so we cannot say p is more preferred by weight alone
    BDD p = orig.getWeight().geq(100).and(orig.getWeight().leq(200));
    BDD q = orig.getWeight().geq(150).and(orig.getWeight().leq(300));
    assertFalse(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testIsMorePreferredBGP_pWeightRangeAlwaysHigherThanQ() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p's weight is in [400..500] (min=400), q's weight is in [100..300] (max=300)
    // min(p) = 400 > max(q) = 300 so p is more preferred
    BDD p = orig.getWeight().geq(400).and(orig.getWeight().leq(500));
    BDD q = orig.getWeight().geq(100).and(orig.getWeight().leq(300));
    assertTrue(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testIsMorePreferredBGP_disjunction() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    // p's minimum weight is 0 due to the disjunction
    BDD p = orig.getWeight().value(200).or(orig.getMed().value(500));
    BDD q = orig.getWeight().value(100);
    assertFalse(utils.isMorePreferredBgp(p, q, _tbdd));
  }

  @Test
  public void testLessPreferredThanBgp_lowerWeightAlwaysIncluded() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    BDD p = orig.getWeight().value(200).and(orig.getLocalPref().value(300));
    BDD lessPreferred = utils.lessPreferredThanBgp(p, _tbdd);

    assertTrue(lessPreferred.andSat(orig.getWeight().value(199)));
    assertFalse(lessPreferred.andSat(orig.getWeight().value(201)));
  }

  @Test
  public void testLessPreferredThanBgp_sameWeightLowerLocalPrefIncluded() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    BDD p = orig.getWeight().value(200).and(orig.getLocalPref().value(300));
    BDD lessPreferred = utils.lessPreferredThanBgp(p, _tbdd);

    assertTrue(
        lessPreferred.andSat(orig.getWeight().value(200).and(orig.getLocalPref().value(299))));
    assertFalse(
        lessPreferred.andSat(orig.getWeight().value(200).and(orig.getLocalPref().value(300))));
  }

  @Test
  public void testLessPreferredThanBgp_disjunctionUsesConservativeMinimums() {
    TransferBDDUtils utils = new TransferBDDUtils();
    BDDRoute orig = _tbdd.getOriginalRoute();

    BDD p =
        orig.getWeight()
            .value(150)
            .and(orig.getLocalPref().value(500))
            .or(orig.getWeight().value(200).and(orig.getLocalPref().value(300)));
    BDD lessPreferred = utils.lessPreferredThanBgp(p, _tbdd);

    assertTrue(lessPreferred.andSat(orig.getWeight().value(149)));
    assertTrue(
        lessPreferred.andSat(orig.getWeight().value(150).and(orig.getLocalPref().value(299))));
    assertFalse(
        lessPreferred.andSat(orig.getWeight().value(150).and(orig.getLocalPref().value(300))));
    assertFalse(lessPreferred.andSat(orig.getWeight().value(199)));
  }
}
