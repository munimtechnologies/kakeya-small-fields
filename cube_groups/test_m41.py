# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m41.py (job m41). The orbit closure, the t = 5 CNFs and the t = 7 CNF are in
--part selfcheck, which the job runs as its own step."""
import unittest

import case_a as ca
import m41 as m
import sat_aniso as sa


class TestM41(unittest.TestCase):
    def test_rep(self):
        A = m.rep()
        self.assertTrue(m.is_candidate(A))
        self.assertEqual([sa.mat_apply(A, 1 << j, 7) for j in range(7)], [0, 0, 0, 0, 2, 4, 8])
        self.assertEqual(sa.mat_mul(A, A, 7), 0)

    def test_candidates(self):
        cand = m.candidates()
        self.assertEqual(len(cand), m.CANDIDATES)
        self.assertIn(m.rep(), cand)
        self.assertFalse(m.is_candidate(0))
        # A_u e_6 = e_0 leaves R.
        self.assertFalse(m.is_candidate(sa.from_cols([0, 0, 0, 0, 2, 4, 1], 7)))

    def test_generators(self):
        gens = m.generators()
        self.assertEqual(len(gens), 22)
        for g in gens:
            self.assertEqual(sa.mat_mul(g, g, 7), ca.identity(7))
            self.assertEqual(sa.mat_apply(g, 1, 7), 1)
            for j in (1, 2, 3):
                self.assertEqual(sa.mat_apply(g, 1 << j, 7) & ~m.R_MASK, 0)
            for j in (4, 5):
                self.assertEqual(sa.mat_apply(g, 1 << j, 7) & ~m.P_MASK, 0)
            self.assertTrue(m.is_candidate(ca.conj(g, m.rep(), 7)))

    def test_counts(self):
        self.assertEqual(m.MAIN_UNITS, 112)
        self.assertEqual(m.HINT_UNITS, 110)
        self.assertEqual(list(m.PHI[1:]), [0, 0, 1, 2, 4, 8, 16, 32])

    def test_t5_same_cnf_as_case_a(self):
        Au = ca.candidates(5)[0]
        mine = m.encode_fixed(5, 6, Au, 1, m.T5_PHI, {1: 2})[0]
        theirs = ca.encode_case_a(5, Au)[0]
        self.assertEqual(mine.nv, theirs.nv)
        self.assertEqual(m.clause_set(mine), m.clause_set(theirs))

    def test_planted(self):
        As, ss, B = m.planted()
        at, sv = sa.tables(As, ss, B, 6)
        self.assertTrue(sa.is_system(at, sv, 6, 6))
        self.assertTrue(sa.anisotropic(sv))
        cnf, names = m.build(m.planted_spec())
        self.assertTrue(sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, 6, 6)))


if __name__ == "__main__":
    unittest.main()
