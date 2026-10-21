# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for a6_r3h.py (job m29). Pure Python; the expected values are computed by hand in
m29/predictions.md and notes/a16.md."""
import random
import unittest

import a6_r3 as r3
import a6_r3h as h
import sat_aniso as sa


def lemma63_ii():
    """Lemma 63 (ii) with a = h_0, b = h_1, e = e_0, f = e_1: sigma(a) = sigma(b) = e,
    sigma(a + b) = f, A_a = A_b = the projection onto span(f) along span(e) (entry (1, 1))."""
    p = sa.entries(2, [(1, 1)])
    return [p, p], [1, 1], {(0, 1): 1 ^ 1 ^ 2}


class TestFacts(unittest.TestCase):
    def test_uplus(self):
        self.assertEqual(h.uplus(7, "A", 5), [0, 1, 2])
        self.assertEqual(h.uplus(7, "B", 4), [0, 1, 2])
        self.assertEqual(h.uplus(7, "B", 5), [0, 1])
        self.assertTrue(h.lemma64_applies(6, 7, "A", 5, 3))
        self.assertTrue(h.lemma64_applies(6, 7, "B", 4, 3))
        self.assertFalse(h.lemma64_applies(6, 7, "B", 5, 3))
        self.assertTrue(h.lemma64_applies(2, 2, "A", 1, 0))
        self.assertFalse(h.lemma64_applies(2, 2, "A", 1, 1))
        self.assertTrue(h.lemma64_applies(4, 5, "B", 3, 2))
        self.assertFalse(h.lemma64_applies(4, 5, "A", 3, 2))

    def test_fact_counts_t6(self):
        x1, r = r3.rref([1, 2, 4]), r3.rref([1, 8, 32])
        self.assertEqual(h.fact_counts(6, 7, "A", 5, 3, x1, r), [18, 60, 3])
        self.assertEqual(h.fact_counts(6, 7, "B", 4, 3, x1, r), [16, 54, 3])
        self.assertEqual(h.fact_counts(6, 7, "B", 5, 3, x1, r), [6, 21, 0])

    def test_fact_counts_small(self):
        self.assertEqual(h.fact_counts(2, 2, "A", 1, 1, (1,), (2,)), [2, 3, 0])
        self.assertEqual(h.fact_counts(2, 2, "B", 1, 1, (1,), (2,)), [0, 0, 0])
        self.assertEqual(h.fact_counts(2, 2, "A", 1, 0, (2, 1), ()), [4, 4, 1])
        x1, r = r3.rref([1, 2]), r3.rref([4, 8])
        self.assertEqual(h.fact_counts(4, 5, "A", 3, 2, x1, r), [8, 20, 0])
        self.assertEqual(h.fact_counts(4, 5, "B", 3, 2, x1, r), [6, 14, 1])
        self.assertEqual(h.fact_counts(4, 5, "B", 2, 2, x1, r), [6, 16, 0])

    def test_alternatives(self):
        plain, alts = h.facts(6, 7, "B", 4, 3, r3.rref([1, 2, 4]), r3.rref([1, 8, 32]))
        self.assertEqual([alt[0][0] for alt in alts], [(1,), (2,), (1, 2)])
        self.assertTrue(all(len(alt) == 3 and all(c[3] == (1,) for c in alt) for alt in alts))

    def test_holds(self):
        As = lemma63_ii()[0]
        self.assertTrue(h.holds(((0,), 1, 0, ()), As, 2))       # A_a e = 0
        self.assertFalse(h.holds(((0,), 2, 0, ()), As, 2))      # A_a f = f != 0
        self.assertTrue(h.holds(((0,), 2, 1, ()), As, 2))       # (I + A_a) f = 0
        self.assertTrue(h.holds(((0, 1), 2, 0, ()), As, 2))     # A_(a + b) = 0
        self.assertTrue(h.holds(((0,), 2, 0, (2,)), As, 2))     # A_a f in span(f)

    def test_encoding_agrees(self):
        st = h.encoding_check(random.Random(1), 80)
        self.assertEqual(st["disagree"], 0)
        self.assertTrue(0 < st["true"] < st["trials"])

    def test_lemma63_system(self):
        As, ss, B = lemma63_ii()
        at, sv = sa.tables(As, ss, B, 2)
        self.assertTrue(sa.is_system(at, sv, 2, 2) and sa.anisotropic(sv))
        st = h.new_counts()
        h.lemma_check(at, sv, 2, 2, st)
        # u = a + b: U+ = V (4 tests of (a)); u = a, b: U+ = {0, u} (2 each). Only u = a + b has
        # k = 2 with dim U+ = 2.
        self.assertEqual(st["a_tested"], 8)
        self.assertEqual(st["b_tested"], 6)
        self.assertEqual(st["c_tested"], 2)
        self.assertEqual(st["d_tested"], 1)
        self.assertEqual(st["e_tested"], 1)
        self.assertTrue(all(st[f"{k}_failed"] == 0 for k in h.FACT_KEYS))

    def test_lemma_check_catches_a_wrong_map(self):
        As, ss, B = lemma63_ii()
        at, sv = sa.tables(As, ss, B, 2)
        at = list(at)
        at[3] = sa.entries(2, [(1, 1)])      # A_(a + b) = p is not the map of a system
        st = h.new_counts()
        h.lemma_check(at, sv, 2, 2, st)
        self.assertGreater(st["a_failed"], 0)

    def test_names(self):
        self.assertEqual(h.instance_name(6, 3, "A", 5, 7), "r3h_t6_r3_A5_o007")


if __name__ == "__main__":
    unittest.main()
