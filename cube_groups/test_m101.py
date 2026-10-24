# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m101.py (job m101, notes/a93.md). Needs m42.py, sat_aniso.py, m100.py and
python-sat next to it."""
import itertools
import random
import unittest

import m100
import m101
import sat_aniso as sa


def solve(clauses):
    from pysat.solvers import Solver
    for name in sa.SOLVERS:
        try:
            s = Solver(name=name, bootstrap_with=clauses)
        except Exception:
            continue
        ok = s.solve()
        s.delete()
        return ok
    raise RuntimeError("no SAT solver available")


class TestM101(unittest.TestCase):
    def test_zero_map_small(self):
        t, d = 4, 3

        def accepts(a1):
            cnf, names = sa.encode(t, d, star=False, aniso=False, echelon=False)
            self.assertEqual(m101.add_zero_map(cnf, names, t), 16)
            B = {key: 0 for key in itertools.combinations(range(d), 2)}
            return sa.satisfies(cnf, sa.assignment(cnf, names, [1, a1, 2], [1, 2, 4], B, t, d))

        self.assertTrue(accepts(0))
        self.assertFalse(accepts(sa.entries(t, [(0, 0)])))

    def test_in_x1_small(self):
        t, d = 4, 3

        def accepts(b01, b12):
            cnf, names = sa.encode(t, d, star=False, aniso=False, echelon=False)
            self.assertEqual(m101.add_in_x1(cnf, names, t, d, nx1=2), 4)
            B = {(0, 1): b01, (0, 2): 8, (1, 2): b12}
            return sa.satisfies(cnf, sa.assignment(cnf, names, [0, 0, 0], [1, 2, 4], B, t, d))

        self.assertTrue(accepts(1, 2))
        self.assertTrue(accepts(3, 0))
        self.assertFalse(accepts(1, 4))
        self.assertFalse(accepts(8, 1))

    def test_aniso_on_small(self):
        As, ss, B = sa.norm_pair()

        def accepts(ss, idx):
            cnf, names = sa.encode(2, 4, star=False, aniso=False, echelon=False)
            n = m101.add_aniso_on(cnf, names, 2, idx)
            self.assertEqual(n, (1 << len(idx)) - 1)
            return sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, 2, 4))

        self.assertTrue(accepts(ss, range(4)))
        self.assertFalse(accepts([0, 1, 2, 2], range(4)))
        self.assertTrue(accepts([1, 1, 0, 2], [0, 1]))
        self.assertFalse(accepts([1, 1, 0, 2], [1, 2]))
        # sigma(e_0 + e_1) = 1 + 1 + beta(e_0, e_1): zero once beta(e_0, e_1) = 0
        B2 = dict(B)
        B2[(0, 1)] = 0
        cnf, names = sa.encode(2, 4, star=False, aniso=False, echelon=False)
        m101.add_aniso_on(cnf, names, 2, [0, 1])
        self.assertFalse(sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B2, 2, 4)))

    def test_case_two(self):
        t, d = 8, 3
        rng = random.Random(101)
        cases = [(2, 4, 8), (3, 2, 0), (1, 0, 0), (0, 0, 0), (3, 5, 6), (3, 5, 7), (17, 2, 0)]
        cases += [tuple(rng.randrange(32) for _ in range(3)) for _ in range(30)]
        for vecs in cases:
            cnf = sa.CNF()
            S = [[cnf.new() for _ in range(t)] for _ in range(d)]
            B = {key: [cnf.new() for _ in range(t)] for key in itertools.combinations(range(d), 2)}
            f, n = m101.add_case_two(cnf, (None, S, B), t, d)
            self.assertEqual((len(f), n), (5, 3))
            for vec, v in zip((S[1], B[(0, 1)], B[(1, 2)]), vecs):
                cnf.clauses += [[vec[r]] if (v >> r) & 1 else [-vec[r]] for r in range(t)]
            self.assertEqual(solve(cnf.clauses), 1 not in m100.span(vecs), vecs)

    def test_idempotent(self):
        self.assertTrue(m101.is_idempotent(sa.entries(4, [(2, 2), (3, 3)]), 4))
        self.assertFalse(m101.is_idempotent(sa.entries(4, [(0, 2), (1, 3)]), 4))
        self.assertEqual(m100.PAIRS[11][2][5][0], sa.entries(8, [(5, 5), (6, 6), (7, 7)]))
        self.assertEqual(m100.PAIRS[12][2][10][0],
                         sa.entries(8, [(5, 5), (6, 6), (7, 7), (0, 5)]))
        self.assertFalse(m101.case_two_required(m100.spec_of(11, 5)))
        self.assertTrue(m101.case_two_required(m100.spec_of(0, 0)))

    def test_constants(self):
        self.assertEqual((m101.ZERO_UNITS, m101.IN_X1_UNITS, m101.CASE_TWO_VECTORS), (64, 30, 11))
        self.assertEqual((m101.X0, m101.X1_MASK, m101.KD), (1, 31, 4))
        sp = m100.spec_of(0, 0)
        self.assertEqual(m101.needed(sp, "sweep"),
                         ["system", "normal_form", "sweep", "zero_map", "in_x1", "case_two",
                          "anisotropic"])
        self.assertEqual(m101.needed(m100.spec_of(11, 5), "relax_n"),
                         ["system", "normal_form", "sweep", "zero_map", "in_x1", "aniso_n"])


if __name__ == "__main__":
    unittest.main()
