# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of a7_casea.py (job m39). The orbit closure and the t = 7 CNF are in --part
selfcheck, which the job runs as its own step."""
import unittest

import a7_casea as m
import case_a as ca
import sat_aniso as sa


class TestA7CaseA(unittest.TestCase):
    def test_reps(self):
        for cls in m.CLASSES:
            A = m.rep(cls)
            self.assertTrue(m.is_candidate(A), cls)
            self.assertEqual(m.pclass(A), cls)
        self.assertEqual(len({m.rep(c) for c in m.CLASSES}), 6)

    def test_hand_counts(self):
        self.assertEqual(sum(m.HAND_SIZES.values()), m.CANDIDATES)
        self.assertEqual(m.group_order(), 3538944)
        for n in m.HAND_SIZES.values():
            self.assertEqual(m.group_order() % n, 0)
        self.assertEqual(m.MAIN_UNITS, 112)
        self.assertEqual(m.HINT_UNITS, 65)

    def test_not_candidates(self):
        self.assertFalse(m.is_candidate(0))
        self.assertFalse(m.is_candidate(ca.identity(m.T)))
        # A_u e_6 = e_0 leaves R.
        self.assertFalse(m.is_candidate(sa.from_cols([0, 0, 0, 2, 4, 8, 1], m.T)))

    def test_generators(self):
        gens = m.generators()
        self.assertEqual(len(gens), 20)
        for g in gens:
            self.assertEqual(sa.rank_f2(sa.rows_of(g, m.T)), m.T)
            self.assertEqual(sa.mat_mul(g, g, m.T), ca.identity(m.T))
            self.assertEqual(sa.mat_apply(g, 1, m.T), 1)
            for j in (1, 2):
                self.assertEqual(sa.mat_apply(g, 1 << j, m.T) & ~m.D_MASK, 0)
            for j in (3, 4):
                self.assertEqual(sa.mat_apply(g, 1 << j, m.T) & ~m.R_MASK, 0)
            for cls in m.CLASSES:
                B = ca.conj(g, m.rep(cls), m.T)
                self.assertTrue(m.is_candidate(B))
                self.assertEqual(m.pclass(B), cls)

    def test_t5_same_cnf_as_case_a(self):
        for Au in (ca.candidates(5)[0], ca.candidates(5)[-1]):
            mine = m.encode_fixed(5, 6, Au, 1, m.T5_PHI, {1: 2})[0]
            theirs = ca.encode_case_a(5, Au)[0]
            self.assertEqual(mine.nv, theirs.nv)
            self.assertEqual(len(mine.clauses), len(theirs.clauses))
            self.assertEqual(m.clause_set(mine), m.clause_set(theirs))

    def test_planted(self):
        As, ss, B = m.planted()
        at, sv = sa.tables(As, ss, B, 6)
        self.assertTrue(sa.is_system(at, sv, 6, 6))
        self.assertTrue(sa.anisotropic(sv))
        self.assertEqual([B[(0, 1)], B[(0, 2)]], [0, 0])
        cnf, names = m.build(m.planted_spec())
        self.assertTrue(sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, 6, 6)))
        As2 = list(As)
        As2[0] ^= 1
        self.assertFalse(sa.satisfies(cnf, sa.assignment(cnf, names, As2, ss, B, 6, 6)))

    def test_params(self):
        t, d, au, s0, phis, fixed = m.params(m.main_spec("main", 5))
        self.assertEqual((t, d, au, s0, fixed), (7, 9, m.rep("nil"), 1, {}))
        self.assertEqual(list(phis[1:]), [0, 1, 2, 4, 8, 16, 32, 64])
        self.assertEqual(m.main_spec("hint", 0)["name"], "a7ca_hint_0_zero")


if __name__ == "__main__":
    unittest.main()
