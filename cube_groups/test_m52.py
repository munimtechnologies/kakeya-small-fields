# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m52.py (job m52). The orbit counts themselves are the job's graded output, not
tested here."""
import random
import unittest

import m52 as m


class TestM52(unittest.TestCase):
    def test_linear_algebra(self):
        self.assertEqual(m.rank([1, 2, 3]), 2)
        self.assertEqual(m.rank([5, 6, 3, 0]), 2)
        self.assertEqual(m.rank(list(m.IDENT)), 7)
        g = (2, 1, 4, 8, 16, 32, 64 | 1)
        self.assertEqual(m.compose(g, m.inverse(g)), m.IDENT)
        self.assertEqual(m.compose(m.inverse(g), g), m.IDENT)
        # x0 + x1 = 1, x1 + x2 = 0 over three unknowns: one free variable
        part, basis = m.solve_affine([(3, 1), (6, 0)], 3)
        self.assertEqual(len(basis), 1)
        for v in (part, part ^ basis[0]):
            self.assertEqual(bin(v & 3).count("1") % 2, 1)
            self.assertEqual(bin(v & 6).count("1") % 2, 0)
        self.assertIsNone(m.solve_affine([(1, 1), (1, 0)], 1))

    def test_structure(self):
        for kind in m.KINDS:
            s = m.structure(kind)
            self.assertEqual(s["rank_au"], 3, kind)
            self.assertTrue(s["ker_is_x1"] and s["r_in_x1"] and s["kind_ok"], kind)

    def test_maps(self):
        rng = random.Random(1)
        for kind in m.KINDS:
            mp = m.Maps(kind)
            self.assertEqual(mp.cols(mp.au_idx), m.au_of(kind))
            self.assertFalse(mp.valid(0) or mp.valid(mp.au_idx))
            for _ in range(200):
                i = rng.randrange(1 << 18)
                self.assertEqual(mp.index(mp.cols(i)), i)
                self.assertEqual(mp.rank_x1(i), mp.rank_x1(i ^ mp.au_idx))

    def test_small_groups(self):
        # graph and L have solution spaces of dimension 15 and 16: quick enough for a test.
        rng = random.Random(2)
        for kind in ("graph", "L"):
            grp, dim = m.group(kind)
            self.assertEqual(len(grp), m.HAND_ORDER[kind], kind)
            self.assertTrue(m.check_group(kind, grp))
            mp = m.Maps(kind)
            for _ in range(100):
                g = rng.choice(grp)
                gi = m.inverse(g)
                i = rng.randrange(1 << 18)
                j = mp.conj(g, gi, i)
                self.assertEqual(mp.rank_x1(i), mp.rank_x1(j))
                self.assertEqual(mp.conj(gi, g, j), i)
                self.assertEqual(mp.conj(g, gi, mp.au_idx), mp.au_idx)


if __name__ == "__main__":
    unittest.main()
