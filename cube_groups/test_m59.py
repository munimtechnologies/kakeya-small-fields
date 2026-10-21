# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m59.py (job m59). The counts (|G|, |Adm|, classes and ranks of the splits) are
graded in --part check, so a wrong count is a graded failure, not a crashed job."""
import unittest

import m55
import m57
import m59 as m


def fake_rep(a1, rank_x1=0):
    return {"index": 1, "cols": list(m55.cols_of(a1)), "a1": a1, "rank_x1": rank_x1, "size": 1}


class TestM59(unittest.TestCase):
    def test_mask_round_trip(self):
        for mask in (m.L_AU, m.GRAPH_AU, 33556496, 34086912, (1 << 49) - 1):
            self.assertEqual(m.mask_of(m55.cols_of(mask)), mask)
            self.assertEqual(m55.cols_of(mask), tuple(m57.column(mask, c) for c in range(7)))

    def test_l_au(self):
        self.assertEqual(m55.cols_of(m.L_AU), (0, 0, 0, 0, 4, 2, 1))
        mp = m.LMaps(m.L_R)
        au = m55.cols_of(m.L_AU)
        self.assertEqual(mp.cols(mp.index(au)), au)
        self.assertEqual(mp.rank_x1(mp.index(au)), 0)
        self.assertFalse(m.admissible_l(m.L_AU))
        self.assertTrue(m.admissible_l(1 << (7 * 2 + 4)))      # e_4 -> e_2
        self.assertFalse(m.admissible_l(1 << (7 * 3 + 4)))     # e_4 -> e_3, outside R
        self.assertFalse(m.admissible_l(1))                    # e_0 -> e_0: does not kill x0
        self.assertTrue(m.admissible_l(1 << 1))                # e_1 -> e_0: rank 1 on X_1
        self.assertTrue(m.admissible_l((1 << 1) | (1 << 9)))   # and e_2 -> e_1: rank 2
        self.assertFalse(m.admissible_l((1 << 1) | (1 << 9) | (1 << 17)))  # and e_3 -> e_2: 3

    def test_identity_in_group_conditions(self):
        au = m55.cols_of(m.L_AU)
        x = sum(1 << (6 * (j - 1) + (j - 1)) for j in range(1, 7))
        self.assertEqual(m.b6_g_of(x), m55.IDENT)
        for mask, c in m.b6_group_conditions(au):
            self.assertEqual(bin(mask & x).count("1") % 2, c)

    def test_graph_open(self):
        for k, idx, rk, a1 in m.GRAPH_OPEN:
            self.assertTrue(m.admissible_graph(a1))
            self.assertEqual(m57.rank_on_x1(a1), rk)
        self.assertEqual(m57.column(33556496, 4), 8 + 2 + 1)    # a117: e_4 -> e_0 + e_1 + e_3
        self.assertEqual(m57.column(34078720, 5), 4)            # a153: e_5 -> e_2

    def test_b5(self):
        for name in m.B5_XOR:
            self.assertIn(name, m57.BATCH_C)
        for name in m.SPLIT:
            au, x1, rb = m55.CLASSES[name]
            self.assertEqual(x1, m55.ALPHA)
            self.assertFalse(m.admissible_b5(au, au, rb))
            self.assertFalse(m.admissible_b5(0, au, rb))
        self.assertEqual(m55.CLASSES["r3b_t7_B5_o001_c000"][0],
                         m57.BATCH_C["r3b_t7_B5_o001_c000"])

    def test_plan(self):
        reps = {"L": [fake_rep(1 << 18), fake_rep(1 << 11)]}
        for name in m.SPLIT:
            reps[name] = [fake_rep(1 << 11), fake_rep(1 << 18), fake_rep(1 << 19)]
        a, b = m.plan("a", reps), m.plan("b", reps)
        self.assertEqual(len(a), 4 + 2)
        self.assertEqual([(s["name"], arm, cond) for s, arm, _, cond, _ in a[:4]],
                         [("r3g_t7_B6_o002_a117", "cadical", None),
                          ("r3g_t7_B6_o002_a117", "xor", "open"),
                          ("r3g_t7_B6_o002_a153", "cadical", None),
                          ("r3g_t7_B6_o002_a153", "xor", "open")])
        self.assertTrue(all(named and cap == 900.0 for _, _, cap, _, named in a[:4]))
        self.assertEqual(a[4][0]["name"], "r3l_t7_B6_o000_a000")
        self.assertTrue(all(arm == "cadical" and cap == 25.0 and not named
                            for _, arm, cap, _, named in a[4:]))
        self.assertEqual(len(b), 2 + 6)
        self.assertTrue(all(arm == "xor" and named for _, arm, _, _, named in b[:2]))
        self.assertEqual(b[2][0]["name"], "r3s_t7_B5_o002_c000_a000")
        self.assertEqual(b[-1][0]["name"], "r3s_t7_B5_o001_c000_a002")

    def test_specs(self):
        sp = m.l_spec(0, fake_rep(1 << 18))
        t, d, au, s0, phis, kd, pvecs = m57.params(sp)
        self.assertEqual((t, d, au, s0, kd), (7, 9, m.L_AU, 1, 3))
        sp = m.split_spec("r3b_t7_B5_o002_c000", 3, fake_rep(1 << 11))
        t, d, au, s0, phis, kd, pvecs = m57.params(sp)
        self.assertEqual((au, kd), (34086976, 4))
        self.assertEqual(sp["name"], "r3s_t7_B5_o002_c000_a003")
        self.assertEqual(sp["parent"], "r3b_t7_B5_o002_c000")


if __name__ == "__main__":
    unittest.main()
