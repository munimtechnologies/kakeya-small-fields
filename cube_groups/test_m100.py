# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m100.py (job m100, notes/a92.md). Needs m42.py and sat_aniso.py next to it."""
import itertools
import unittest

import m42
import m100
import sat_aniso as sa


class TestM100(unittest.TestCase):
    def test_pairs(self):
        self.assertEqual(len(m100.PAIRS), 13)
        self.assertEqual(sum(len(p[2]) for p in m100.PAIRS), 68)
        self.assertEqual(tuple(len(p[2]) for p in m100.PAIRS), m100.M99_CLASSES)
        for x1, r, cls in m100.PAIRS:
            self.assertEqual(sum(s for _, s in cls), 168)

    def test_reps(self):
        for x1, r, cls in m100.PAIRS:
            for rep, _ in cls:
                self.assertEqual(sa.rank_f2(sa.rows_of(rep, 8)), 3)
                self.assertEqual(m100.span(m100.kernel_basis(rep)), m100.span(x1))
                self.assertEqual(m100.image(rep), m100.span(r))

    def test_d(self):
        self.assertEqual(tuple(m100.meet_dim(x1, r) for x1, r, _ in m100.PAIRS), m100.M99_D)
        self.assertEqual(m100.meet_dim((4, 2, 1), (2, 1)), 2)

    def test_kernel_basis(self):
        au = sa.entries(4, [(2, 2), (3, 3)])
        self.assertEqual(m100.kernel_basis(au, 4), [1, 2])

    def test_encode_as_m42(self):
        au = sa.entries(4, [(0, 2), (1, 3)])
        phis = (None, 0, 0, 2, 4)
        a, _ = m100.encode_fixed(4, 5, au, 1, phis)
        b, _ = m42.encode_fixed(4, 5, au, 1, phis)
        self.assertEqual(a.clauses, b.clauses)
        c, _ = m100.encode_fixed(4, 5, au, 1, phis, aniso=False)
        self.assertEqual(m100.aniso_clauses(a, 4), 31)
        self.assertEqual(m100.aniso_clauses(c, 4), 0)

    def test_sweep_small(self):
        t, d, kd = 4, 5, 3
        au = sa.entries(t, [(2, 2), (3, 3)])

        def accepts(a1, b12):
            cnf, names = sa.encode(t, d, star=False, aniso=False, echelon=False)
            n = m100.add_sweep(cnf, names, t, kd, au)
            self.assertEqual(n, 2 * 2 * t + t)
            As = [au, a1, 0, 1, 2]
            ss = [1, 2, 4, 8, 3]
            B = {key: 0 for key in itertools.combinations(range(d), 2)}
            B[(1, 2)] = b12
            return sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, t, d))

        self.assertTrue(accepts(sa.entries(t, [(0, 2), (3, 3)]), 0))
        self.assertFalse(accepts(sa.entries(t, [(0, 1)]), 0))
        self.assertFalse(accepts(0, 1))

    def test_constants(self):
        self.assertEqual(m100.SWEEP_CONDITIONS, 144)
        self.assertEqual(m100.KD, 4)
        self.assertEqual(sorted(m100.SHARDS["a"] + m100.SHARDS["b"]), list(range(13)))
        for shard, ctl in m100.CONTROLS.items():
            for pi, ci in ctl:
                self.assertIn(pi, m100.SHARDS[shard])
                self.assertLess(ci, len(m100.PAIRS[pi][2]))
        self.assertEqual(len(m100.shard_specs("a")) + len(m100.shard_specs("b")), 68)

    def test_spec(self):
        sp = m100.spec_of(11, 5)
        self.assertEqual(sp["name"], "r3b_t8_B7_o011_c005")
        self.assertEqual(sp["dmeet"], 0)
        t, d, au, s0, phis, kd, pvecs = m42.params(sp)
        self.assertEqual((t, d, kd, s0), (8, 11, 4, 1))


if __name__ == "__main__":
    unittest.main()
