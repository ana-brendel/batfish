package org.batfish.minesweeper.question.verificationutilities;

import com.google.common.collect.ImmutableSet;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;
import org.batfish.datamodel.PrefixRange;
import org.batfish.datamodel.PrefixSpace;
import org.batfish.minesweeper.CommunityVar;
import org.batfish.minesweeper.ConfigAtomicPredicates;
import org.batfish.minesweeper.bdd.BDDRoute;
import org.batfish.minesweeper.bdd.TransferBDD;
import org.junit.Before;
import org.junit.Test;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.batfish.minesweeper.bdd.TransferBDD.isRelevantForDestination;
import static org.junit.Assert.assertEquals;

public class BDDStringTest {
  private TransferBDD tbdd;
  private BDDRoute base;

  @Before
  public void setup() {
    tbdd =
        new TransferBDD(
            new ConfigAtomicPredicates(
                List.of(),
                Set.of(
                    CommunityVar.from("10:10"),
                    CommunityVar.from("20:20"),
                    CommunityVar.from("30:30"),
                    CommunityVar.from("40:40"),
                    CommunityVar.from("50:50")),
                new HashSet<>()));
    base = tbdd.getOriginalRoute();
  }

  private BDD commBDDString(String regex) {
    BDDRoute route = new BDDRoute(tbdd.getFactory(), tbdd.getConfigAtomicPredicates());
    return tbdd.getFactory()
        .orAll(
            tbdd
                .getConfigAtomicPredicates()
                .getStandardCommunityAtomicPredicates()
                .getRegexAtomicPredicates()
                .get(CommunityVar.from(regex))
                .stream()
                .map(i -> route.getCommunityAtomicPredicates()[i])
                .collect(ImmutableSet.toImmutableSet()));
  }

  private BDD prefixStringToBDD(String str, boolean positive) {
    PrefixSpace space = new PrefixSpace(PrefixRange.fromString(str));
    BDDFactory factory = base.getPrefix().getFactory();
    if (space.isEmpty()) {
      return factory.one();
    } else {
      BDD result = factory.zero();
      for (PrefixRange range : space.getPrefixRanges()) {
        BDD rangeBDD = isRelevantForDestination(base, range);
        result = result.or(rangeBDD);
      }
      if (!positive) {
        result = result.not();
      }
      return result;
    }
  }

  @Test
  public void onlyCommunities() {
    // singles
    assertEquals("comm(40:40)", BDDString.get(tbdd, commBDDString("40:40")));
    assertEquals("!comm(10:10)", BDDString.get(tbdd, commBDDString("10:10").not()));
    assertEquals(
        "comm(50:50)", BDDString.get(tbdd, commBDDString("50:50").and(commBDDString("50:50"))));

    // conjunctions
    assertEquals(
        "comm(20:20),comm(30:30)",
        BDDString.get(tbdd, commBDDString("20:20").and(commBDDString("30:30"))));
    String s = BDDString.get(tbdd, commBDDString("20:20").and(commBDDString("30:30").not()));
    assertEquals("!comm(30:30),comm(20:20)", s);
    String t = BDDString.get(tbdd, commBDDString("20:20").not().and(commBDDString("30:30").not()));
    assertEquals("!comm(20:20),!comm(30:30)", t);
    assertEquals(
        "False", BDDString.get(tbdd, commBDDString("40:40").and(commBDDString("40:40").not())));

    // disjunctions
    String u = BDDString.get(tbdd, commBDDString("20:20").or(commBDDString("30:30")));
    assertEquals("comm(20:20) OR comm(30:30)", u);
    assertEquals(
        "True", BDDString.get(tbdd, commBDDString("40:40").or(commBDDString("40:40").not())));
    String v =
        BDDString.get(
            tbdd,
            commBDDString("20:20").or(commBDDString("30:30")).or(commBDDString("50:50").not()));
    assertEquals("!comm(50:50) OR comm(20:20) OR comm(30:30)", v);

    // implications
    String w =
        BDDString.get(
            tbdd, (commBDDString("40:40").and(commBDDString("50:50"))).imp(commBDDString("10:10")));
    assertEquals("!comm(40:40) OR !comm(50:50) OR comm(10:10)", w);
    String y = BDDString.get(tbdd, commBDDString("40:40").imp(commBDDString("10:10")));
    assertEquals("!comm(40:40) OR comm(10:10)", y);

    // negations
    String z = BDDString.get(tbdd, (commBDDString("20:20").and(commBDDString("10:10"))).not());
    assertEquals("!comm(10:10) OR !comm(20:20)", z);
    String q = BDDString.get(tbdd, (commBDDString("20:20").or(commBDDString("10:10"))).not());
    assertEquals("!comm(10:10),!comm(20:20)", q);
  }

  @Test
  public void onlyPrefixes() {
    // singles
    String a = BDDString.get(tbdd, prefixStringToBDD("25.13.0.0/16", true));
    assertEquals("prefix(25.13.0.0/16)", a);
    String b = BDDString.get(tbdd, prefixStringToBDD("25.13.0.0/16", false));
    assertEquals("!prefix(25.13.0.0/16)", b);

    // disjunction
    String c =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.0.0/16", true).or(prefixStringToBDD("12.0.0.0/8", true)));
    assertEquals("prefix(12.0.0.0/8) OR prefix(25.13.0.0/16)", c);
    String d =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.0.0/16", true).or(prefixStringToBDD("12.0.0.0/8", false)));
    assertEquals("!prefix(12.0.0.0/8)", d);
    String e =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.7.0/24", false).or(prefixStringToBDD("120.0.0.0/8", false)));
    assertEquals("True", e);

    // conjunction
    String f =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.0.0/16", true).and(prefixStringToBDD("12.0.0.0/8", true)));
    assertEquals("False", f);

    // prefix range
    String g = BDDString.get(tbdd, prefixStringToBDD("25.13.0.0/16:16-32", true));
    assertEquals("prefix(25.13.0.0/16:16-32)", g);

    // disjunction of disjoint prefix ranges
    String h =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.0.0/16:16-32", true)
                .or(prefixStringToBDD("12.0.0.0/8:8-12", true)));
    assertEquals("prefix(12.0.0.0/8:8-12) OR prefix(25.13.0.0/16:16-32)", h);

    // disjunction of two prefixes that can be combined into a single prefix with wildcards
    String i =
        BDDString.get(
            tbdd,
            prefixStringToBDD("192.0.0.0/8", true).or(prefixStringToBDD("200.0.0.0/8", true)));
    assertEquals("prefix(1100*000/8)", i);

    // as above but now prefix ranges with the same range of prefix lengths
    String j =
        BDDString.get(
            tbdd,
            prefixStringToBDD("192.0.0.0/8:8-16", true)
                .or(prefixStringToBDD("200.0.0.0/8:8-16", true)));
    assertEquals("prefix(1100*000/8:8-16)", j);

    // as above but now the prefix lengths overlap but are not equivalent
    String k =
        BDDString.get(
            tbdd,
            prefixStringToBDD("192.0.0.0/8:8-16", true)
                .or(prefixStringToBDD("200.0.0.0/8:8-12", true)));
    assertEquals("prefix(1100*000/8:8-12) OR prefix(192.0.0.0/8:13-16)", k);

    // TODO - Examples that return bitstrings, but we'd like to do better than that
    // and recover the original prefix ranges
    /*
    String unknown1 =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.0.0/16:16-32", true)
                .or(prefixStringToBDD("12.0.0.0/8:8-24", true)));
    String unknown2 = BDDString.get(tbdd, prefixStringToBDD("25.13.0.0/16:16-32", false));
    String unknown3 =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.0.0/16", false).and(prefixStringToBDD("12.0.0.0/8", false)));
    String unknown4 =
        BDDString.get(
            tbdd,
            prefixStringToBDD("25.13.7.0/24", false)
                .and(prefixStringToBDD("25.13.0.0/16:16-32", true)));
     */
  }

  @Test
  public void includesCommunitiesAndPrefixes() {
    // TODO - run more tests

    // conjunctions
    BDD a = commBDDString("40:40").and(prefixStringToBDD("25.13.0.0/16", true));
    String a_str = BDDString.get(tbdd, a);
    assertEquals("comm(40:40),prefix(25.13.0.0/16)", a_str);
    BDD aa = commBDDString("40:40").and(prefixStringToBDD("25.13.0.0/16:16-32", true));
    String aa_str = BDDString.get(tbdd, aa);
    assertEquals("comm(40:40),prefix(25.13.0.0/16:16-32)", aa_str);
    BDD d = commBDDString("30:30").and(prefixStringToBDD("25.13.0.0/16", false));
    String d_str = BDDString.get(tbdd, d);
    assertEquals("!prefix(25.13.0.0/16),comm(30:30)", d_str);
    BDD e =
        (commBDDString("20:20").and(commBDDString("30:30")))
            .and(prefixStringToBDD("25.13.0.0/16", false));
    String e_str = BDDString.get(tbdd, e);
    assertEquals("!prefix(25.13.0.0/16),comm(20:20),comm(30:30)", e_str);

    // disjunctions
    BDD b = commBDDString("40:40").or(prefixStringToBDD("25.13.0.0/16", true));
    String b_str = BDDString.get(tbdd, b);
    assertEquals("comm(40:40) OR prefix(25.13.0.0/16)", b_str);
    BDD c = commBDDString("50:50").or(prefixStringToBDD("25.13.0.0/16", false));
    String c_str = BDDString.get(tbdd, c);
    assertEquals("!prefix(25.13.0.0/16) OR comm(50:50)", c_str);

    // combinations
    BDD f = d.or(a);
    String f_str = BDDString.get(tbdd, f);
    // this is accurate but can be reduced
    assertEquals(
        "!comm(30:30),comm(40:40),prefix(25.13.0.0/16) OR !comm(40:40),"
            + "!prefix(25.13.0.0/16),comm(30:30) OR comm(30:30),comm(40:40)",
        f_str);
  }
}
