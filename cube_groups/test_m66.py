# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m66.py. Hand counts are not tested here; the grade part grades them."""
import random
import unittest

import m66


class TestM66(unittest.TestCase):
    def test_cols_of_mask(self):
        # o004_c000 in a52.md: e_4 -> e_4, e_5 -> e_2, e_6 -> e_1.
        au = m66.cols_of_mask(m66.classes()["r3b_t7_B6_o004_c000"])
        self.assertEqual(au, (0, 0, 0, 0, 16, 4, 2))

    def test_inverse_and_compose(self):
        rng = random.Random(1)
        for _ in range(20):
            while True:
                g = tuple(rng.randrange(1, 128) for _ in range(m66.T))
                if m66.rank(g) == m66.T:
                    break
            self.assertEqual(m66.compose(g, m66.inverse(g)), m66.IDENT)

    def test_solve_affine(self):
        # x0 + x1 = 1, x1 + x2 = 0 over three unknowns: one free variable.
        part, basis = m66.solve_affine([(0b011, 1), (0b110, 0)], 3)
        self.assertEqual(len(basis), 1)
        sols = {part, part ^ basis[0]}
        for s in sols:
            self.assertEqual(((s & 1) ^ (s >> 1 & 1)), 1)
            self.assertEqual(((s >> 1 & 1) ^ (s >> 2 & 1)), 0)

    def test_index_round_trip(self):
        mp = m66.Maps((16, 4, 2))
        for idx in (0, 1, 511, 12345, (1 << 18) - 1):
            self.assertEqual(mp.index(mp.cols(idx)), idx)

    def test_group_small_class(self):
        name = "r3b_t7_B6_o012_c001"
        au = m66.cols_of_mask(m66.classes()[name])
        grp, dim = m66.group(au)
        self.assertGreater(len(grp), 0)
        self.assertTrue(m66.check_group(au, grp))
        gens = m66.generators(grp, random.Random(0))
        self.assertEqual(m66.closure_size(gens), len(grp))

    def test_tables_match_direct(self):
        name = "r3b_t7_B6_o012_c001"
        au = m66.cols_of_mask(m66.classes()[name])
        grp, _ = m66.group(au)
        mp = m66.Maps(m66.m58.B6_PAIR_R[m66.pair_of(name)])
        rng = random.Random(2)
        for g in rng.sample(grp, 3):
            tabs = mp.conj_tables(g)
            gi = m66.inverse(g)
            for i in rng.sample(range(1 << 18), 50):
                fast = tabs[0][i & 63] ^ tabs[1][(i >> 6) & 63] ^ tabs[2][i >> 12]
                self.assertEqual(fast, mp.conj_direct(g, gi, i))

    def test_structure(self):
        cl = m66.classes()
        for name in ("r3b_t7_B6_o003_c000", "r3b_t7_B6_o009_c004", "r3b_t7_B6_o012_c011"):
            s = m66.structure(name, cl[name])
            self.assertEqual(s["rank_au"], 3)
            self.assertTrue(s["ker_is_x1"] and s["image_is_r"])

    def test_grade_empty(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            out = m66.grade(d, ["r3b_t7_B6_o012_c001"])
            self.assertFalse(out["all_held"])
            self.assertIn("r3b_t7_B6_o012_c001", out["ungraded"])


if __name__ == "__main__":
    unittest.main()
