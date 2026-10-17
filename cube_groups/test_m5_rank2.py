# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import m5_rank2 as mr


def lemma28_space():
    # {A in M_4 : A P <= span(e_3)} with P = {x : x_3 = 0}: row 3 in columns 0..2, and column 3.
    return [mr.entries(4, [(3, 0)]), mr.entries(4, [(3, 1)]), mr.entries(4, [(3, 2)]),
            mr.entries(4, [(0, 3)]), mr.entries(4, [(1, 3)]), mr.entries(4, [(2, 3)]),
            mr.entries(4, [(3, 3)])]


class TestHelpers(unittest.TestCase):
    def test_matrices(self):
        self.assertEqual(mr.outer(1, 1, 2), 1)                   # E_00
        self.assertEqual(mr.outer(3, 1, 2), 5)                   # E_00 + E_10
        self.assertEqual(mr.columns_of(mr.entries(2, [(1, 0)]), 2), [2, 0])
        self.assertEqual(mr.padded([mr.entries(3, [(2, 2)])], 4), [mr.entries(4, [(2, 2)])])
        self.assertEqual(len(mr.elements([1, 2, 4])), 8)
        self.assertEqual([len(mr.proper_subspaces(t)) for t in (2, 3, 4, 5)], [3, 14, 65, 372])

    def test_alternating(self):
        # A_3: every non-zero element has rank 2 and a kernel line; for every hyperplane P some
        # element has its kernel outside P, so no compression; no invariant line or plane.
        B = mr.primitive3("A3")
        self.assertEqual(sorted({mr.mat_rank(A, 3) for A in mr.elements(B) if A}), [2])
        c = mr.classify(B, 3, mr.proper_subspaces(3))
        self.assertEqual((c["kernel"], c["image"], c["compressions"]), (0, 3, 0))
        self.assertFalse(c["covered"])
        self.assertTrue(c["irreducible"])
        self.assertFalse(c["lemma28"])

    def test_lemma28_space(self):
        B = lemma28_space()
        self.assertEqual(max(mr.mat_rank(A, 4) for A in mr.elements(B)), 2)
        c = mr.classify(B, 4, mr.proper_subspaces(4))
        self.assertEqual((c["kernel"], c["image"]), (0, 4))
        self.assertTrue(c["covered"] and c["irreducible"] and c["lemma28"])
        self.assertIn((8, 8), mr.compressions(B, 4))

    def test_padded(self):
        subs = mr.proper_subspaces(4)
        c = mr.classify(mr.padded(mr.primitive3("A3"), 4), 4, subs)
        self.assertEqual(c["kernel"], 1)
        self.assertTrue(c["covered"])
        self.assertFalse(c["irreducible"])
        # images inside span(e_0, e_1): covered, and span(e_0, e_1) is invariant
        B = [mr.entries(4, [(0, 0), (1, 3)]), mr.entries(4, [(0, 2), (1, 1)])]
        c = mr.classify(B, 4, subs)
        self.assertEqual(c["image"], 2)
        self.assertTrue(c["covered"])
        self.assertFalse(c["irreducible"])


class TestLemma29(unittest.TestCase):
    def test_random_rank2(self):
        rng = random.Random(5)
        subs = mr.proper_subspaces(4)
        for i in range(12):
            seed = mr.padded(mr.primitive3("U3"), 4) if i % 3 == 2 else []
            B = mr.grow(rng, 4, seed, 120)
            self.assertLessEqual(max(mr.mat_rank(A, 4) for A in mr.elements(B)), 2)
            for k in range(1, len(B) + 1):
                c = mr.classify(B[:k], 4, subs)
                self.assertTrue(c["covered"])
                if c["irreducible"]:
                    self.assertTrue(c["lemma28"])


class TestCases(unittest.TestCase):
    def test_bounds(self):
        A, E = mr.bounds(10)
        self.assertEqual(A, [0, 1, 2, 3, 5, 7, 9, 12, 15, 18, 20])
        self.assertEqual(E, [0, 0, 0, 0, 1, 2, 3, 5, 7, 9, 10])

    def test_settled(self):
        out = mr.cases()
        self.assertTrue(all(out["graded"].values()))
        self.assertEqual({b: out["first_open"][str(b)] for b in range(2, 9)},
                         {2: 9, 3: 9, 4: 9, 5: 10, 6: 10, 7: 11, 8: 11})
        for a, b in ((8, 2), (8, 5), (9, 5), (9, 6), (10, 7), (10, 8)):
            self.assertTrue(mr.settled(a, b))
        for a, b in ((9, 2), (9, 4), (10, 5), (11, 7), (11, 8)):
            self.assertFalse(mr.settled(a, b))


if __name__ == "__main__":
    unittest.main()
