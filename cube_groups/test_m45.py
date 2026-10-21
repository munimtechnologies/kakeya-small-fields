# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m45.py (job m45). The comparison with m42.py's full classification of (B6) is in
--part check, which the job runs as its own step."""
import unittest

import m42
import m45 as m
import sat_aniso as sa


class TestM45(unittest.TestCase):
    def test_tables(self):
        self.assertEqual(len(m.OPEN), 30)
        self.assertEqual(sum(m.M42A_PER_PAIR), 68)
        self.assertEqual(len(m.PAIR_R), 13)
        self.assertEqual(len(m.BATCHES["a"]), 15)
        self.assertEqual(len(m.BATCHES["b"]), 15)
        self.assertEqual(sorted(m.BATCHES["a"] + m.BATCHES["b"]), sorted(m.OPEN))

    def test_names(self):
        self.assertEqual(m.pair_cls("r3b_t7_B6_o012_c008"), (12, 8))
        for name in m.OPEN:
            pi, ci = m.pair_cls(name)
            self.assertEqual(m42.instance_name(7, 6, pi, ci), name)
            self.assertLess(ci, m.M42A_PER_PAIR[pi])

    def test_reps(self):
        for name, au in m.OPEN.items():
            pi, _ = m.pair_cls(name)
            self.assertEqual(m42.kernel(au, 7), m.X1)
            self.assertEqual(m42.column_space(au, 7), m.PAIR_R[pi])
            self.assertEqual(sa.rank_f2(m42.cols_of(au, 7)), 3)

    def test_spec(self):
        sp = m.spec_of("r3b_t7_B6_o009_c004")
        self.assertEqual((sp["t"], sp["d"], sp["p"], sp["kind"]), (7, 9, 6, "main"))
        t, d, au, s0, phis, kd, pvecs = m42.params(sp)
        self.assertEqual((au, s0, kd), (562640726096, 1, 3))
        self.assertEqual(phis, (None, 0, 0, 2, 4, 8, 16, 32, 64))


if __name__ == "__main__":
    unittest.main()
