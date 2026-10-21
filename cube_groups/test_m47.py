# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m47.py (job m47). The comparison with m42.py's full classification of (B6) is in
--part check, which the job runs as its own step."""
import unittest

import m42
import m47 as m
import sat_aniso as sa


class TestM47(unittest.TestCase):
    def test_tables(self):
        self.assertEqual(len(m.OPEN), 29)
        self.assertEqual(len(m.M42B_UNSAT), 5)
        self.assertEqual(sum(m.M42_PER_PAIR), 68)
        self.assertEqual(sum(m.M42A_TRIED_PER_PAIR), 34)
        self.assertEqual(sum(m.M42B_TRIED_PER_PAIR), 34)
        self.assertEqual(tuple(a + b for a, b in zip(m.M42A_TRIED_PER_PAIR, m.M42B_TRIED_PER_PAIR)),
                         m.M42_PER_PAIR)
        self.assertEqual(len(m.PAIR_R), 13)
        self.assertEqual(sorted(m.BATCHES), ["a", "b", "c"])
        self.assertEqual([len(m.BATCHES[b]) for b in "abc"], [9, 11, 9])
        self.assertEqual(sorted(sum(m.BATCHES.values(), [])), sorted(m.OPEN))
        self.assertFalse(set(m.OPEN) & set(m.M42B_UNSAT))

    def test_m42b_half(self):
        both = dict(m.OPEN)
        both.update(m.M42B_UNSAT)
        self.assertEqual(len(both), 34)
        self.assertEqual(m.per_pair(both), m.M42B_TRIED_PER_PAIR)
        self.assertEqual(m.per_pair(m.M42B_UNSAT), (0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0))
        self.assertEqual(m.per_pair(m.OPEN), (0, 1, 0, 5, 0, 2, 0, 6, 1, 5, 4, 2, 3))

    def test_names(self):
        self.assertEqual(m.pair_cls("r3b_t7_B6_o012_c011"), (12, 11))
        for name in list(m.OPEN) + list(m.M42B_UNSAT):
            pi, ci = m.pair_cls(name)
            self.assertEqual(m42.instance_name(7, 6, pi, ci), name)
            self.assertLess(ci, m.M42_PER_PAIR[pi])

    def test_reps(self):
        both = dict(m.OPEN)
        both.update(m.M42B_UNSAT)
        for name, au in both.items():
            pi, _ = m.pair_cls(name)
            self.assertEqual(m42.kernel(au, 7), m.X1)
            self.assertEqual(m42.column_space(au, 7), m.PAIR_R[pi])
            self.assertEqual(sa.rank_f2(m42.cols_of(au, 7)), 3)
        self.assertEqual(len(set(both.values())), 34)

    def test_spec(self):
        sp = m.spec_of("r3b_t7_B6_o009_c000")
        self.assertEqual((sp["t"], sp["d"], sp["p"], sp["kind"]), (7, 9, 6, "main"))
        t, d, au, s0, phis, kd, pvecs = m42.params(sp)
        self.assertEqual((au, s0, kd), (558345756736, 1, 3))
        self.assertEqual(phis, (None, 0, 0, 2, 4, 8, 16, 32, 64))
        sp = m.spec_of("r3b_t7_B6_o003_c004")
        self.assertEqual(sp["r"], [16, 2, 1])


if __name__ == "__main__":
    unittest.main()
