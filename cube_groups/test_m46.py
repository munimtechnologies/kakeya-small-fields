# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m46.py (job m46). The comparison with m42.py's full classification of (B5) is in
--part check, which the job runs as its own step."""
import unittest

import m42
import m46 as m
import sat_aniso as sa


class TestM46(unittest.TestCase):
    def test_tables(self):
        self.assertEqual(len(m.OPEN), 42)
        self.assertEqual(len(m.M42C_PER_PAIR), 49)
        self.assertEqual(sum(m.M42C_PER_PAIR), 420)
        self.assertEqual(sum(m.M42C_PER_PAIR[:m.FIRST_BETA_PAIR]), 206)
        self.assertEqual(len(m.PAIR_R), 49)
        self.assertEqual(len(m.BATCHES["a"]), 20)
        self.assertEqual(len(m.BATCHES["b"]), 22)
        self.assertEqual(sorted(m.BATCHES["a"] + m.BATCHES["b"]), sorted(m.OPEN))
        # Lemma 83: 20 pair orbits with X_1 inside H0, 29 outside.
        self.assertEqual(sum(1 for pi in m.PAIR_R if m.x_orbit(pi) == 0), 20)
        self.assertEqual(sum(1 for pi in m.PAIR_R if m.x_orbit(pi) == 1), 29)

    def test_pair_data(self):
        for pi, r in m.PAIR_R.items():
            self.assertEqual(sa.rank_f2(list(r)), 3)
            self.assertEqual(sa.rank_f2(list(m.x1_of(pi))), 4)
            self.assertEqual(m42.rref(list(r)), tuple(r))
            self.assertEqual(m42.rref(list(m.x1_of(pi))), m.x1_of(pi))

    def test_names(self):
        self.assertEqual(m.pair_cls("r3b_t7_B5_o039_c022"), (39, 22))
        for name in m.OPEN:
            pi, ci = m.pair_cls(name)
            self.assertEqual(m42.instance_name(7, 5, pi, ci), name)
            self.assertLess(ci, m.M42C_PER_PAIR[pi])

    def test_reps(self):
        for name, au in m.OPEN.items():
            pi, _ = m.pair_cls(name)
            self.assertEqual(m42.kernel(au, 7), m.x1_of(pi))
            self.assertEqual(m42.column_space(au, 7), m.PAIR_R[pi])
            self.assertEqual(sa.rank_f2(m42.cols_of(au, 7)), 3)

    def test_spec(self):
        sp = m.spec_of("r3b_t7_B5_o000_c000")
        self.assertEqual((sp["t"], sp["d"], sp["p"], sp["kind"]), (7, 9, 5, "main"))
        t, d, au, s0, phis, kd, pvecs = m42.params(sp)
        self.assertEqual((au, s0, kd), (266304, 1, 4))
        sp = m.spec_of("r3b_t7_B5_o042_c002")
        self.assertEqual(sp["x1"], [64, 4, 2, 1])
        self.assertEqual(sp["r"], [72, 4, 3])


if __name__ == "__main__":
    unittest.main()
