# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m48.py (job m48). The comparison with m42.py's full classification of (B5) is in
--part check, which the job runs as its own step."""
import unittest

import m42
import m46
import m48 as m
import sat_aniso as sa


class TestM48(unittest.TestCase):
    def test_tables(self):
        self.assertEqual(len(m.OPEN), 51)
        self.assertEqual(sorted(sum(m.BATCHES.values(), [])), sorted(m.OPEN))
        for b in m.BATCHES.values():
            self.assertEqual(len(b), 17)
        self.assertFalse(set(m.OPEN) & set(m46.OPEN))
        # 30 open classes with X_1 inside H0 (pair orbits 0 to 19), 21 outside.
        self.assertEqual(sum(1 for n in m.OPEN if m46.x_orbit(m46.pair_cls(n)[0]) == 0), 30)

    def test_names(self):
        for name in m.OPEN:
            pi, ci = m46.pair_cls(name)
            self.assertEqual(m42.instance_name(7, 5, pi, ci), name)
            self.assertLess(ci, m46.M42C_PER_PAIR[pi])

    def test_reps(self):
        for name, au in m.OPEN.items():
            pi, _ = m46.pair_cls(name)
            self.assertEqual(m42.kernel(au, 7), m46.x1_of(pi))
            self.assertEqual(m42.column_space(au, 7), m46.PAIR_R[pi])
            self.assertEqual(sa.rank_f2(m42.cols_of(au, 7)), 3)

    def test_d3(self):
        # The five classes with d = dim(X_1 n R) = 3 (A_u^2 = 0) that m42d tried (notes/a34.md).
        d3 = sorted(n for n in m.OPEN
                    if m42.dim_meet(m46.x1_of(m46.pair_cls(n)[0]),
                                    m46.PAIR_R[m46.pair_cls(n)[0]]) == 3)
        self.assertEqual(d3, ["r3b_t7_B5_o000_c001", "r3b_t7_B5_o000_c002",
                              "r3b_t7_B5_o001_c000", "r3b_t7_B5_o031_c000",
                              "r3b_t7_B5_o033_c000"])
        for n in d3:
            au = m.OPEN[n]
            self.assertEqual(sa.mat_mul(au, au, 7), 0)

    def test_spec(self):
        sp = m.spec_of("r3b_t7_B5_o048_c003")
        self.assertEqual((sp["t"], sp["d"], sp["p"], sp["kind"]), (7, 9, 5, "main"))
        self.assertEqual(sp["x1"], [64, 4, 2, 1])
        self.assertEqual(sp["r"], [72, 32, 17])
        t, d, au, s0, phis, kd, pvecs = m42.params(sp)
        self.assertEqual((au, s0, kd), (36288195461136, 1, 4))


if __name__ == "__main__":
    unittest.main()
