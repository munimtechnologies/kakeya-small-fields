# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Tests for sat_aniso.py. Pure Python: they check the CNF encoding against brute force and do not
need a SAT solver."""
import random
import unittest

import sat_aniso as sa


class TestEquations(unittest.TestCase):
    def test_example1(self):
        # Example 1 is a system and anisotropic (checked by hand on (L) in run 56).
        As, ss, B = sa.example1()
        at, sv = sa.tables(As, ss, B, 2)
        self.assertTrue(sa.is_system(at, sv, 2, 3))
        self.assertTrue(sa.anisotropic(sv))
        self.assertTrue(sa.coeff_ok(As, ss, B, 3, 2))
        self.assertEqual(sv, [0, 6, 7, 3])

    def test_random_agree(self):
        rng = random.Random(5)
        for t, d, As, ss, B in sa.random_examples(rng, 60):
            at, sv = sa.tables(As, ss, B, d)
            self.assertEqual(sa.coeff_ok(As, ss, B, t, d), sa.is_system(at, sv, d, t))


class TestCNF(unittest.TestCase):
    def test_example1_accepted(self):
        As, ss, B = sa.example1()
        self.assertTrue(sa.cnf_accepts(As, ss, B, 3, 2, echelon=False))
        # sigma(e_1) = e_2 + e_3 is not in echelon form (the first value must be 0 or e_1)
        self.assertFalse(sa.in_echelon(ss, 3))
        self.assertFalse(sa.cnf_accepts(As, ss, B, 3, 2))
        nAs, nss, nB = sa.normalize(As, ss, B, 3)
        self.assertTrue(sa.in_echelon(nss, 3))
        self.assertTrue(sa.cnf_accepts(nAs, nss, nB, 3, 2))

    def test_example1_broken(self):
        # A_1 = 0 instead of E_11: (L) for (i, j) = (2, 1) fails, A_1 s_2 = 0 != e_1
        As, ss, B = sa.example1()
        self.assertFalse(sa.coeff_ok([0, As[1]], ss, B, 3, 2))
        self.assertFalse(sa.cnf_accepts([0, As[1]], ss, B, 3, 2, echelon=False))

    def test_linear(self):
        # alpha = 0 and sigma linear and one-to-one: an anisotropic system in echelon form
        self.assertTrue(sa.cnf_accepts([0, 0, 0], [1, 2, 4], {(0, 1): 0, (0, 2): 0, (1, 2): 0},
                                       3, 3))
        # sigma(e_3) = sigma(e_1) + sigma(e_2): sigma(e_1 + e_2 + e_3) = 0
        self.assertFalse(sa.cnf_accepts([0, 0, 0], [1, 2, 3], {(0, 1): 0, (0, 2): 0, (1, 2): 0},
                                        3, 3))

    def test_norm_pair(self):
        As, ss, B = sa.norm_pair()
        at, sv = sa.tables(As, ss, B, 4)
        self.assertTrue(sa.anisotropic(sv))
        self.assertFalse(sa.is_system(at, sv, 4, 2))
        self.assertTrue(sa.cnf_accepts(As, ss, B, 2, 4, star=False))
        self.assertFalse(sa.cnf_accepts(As, ss, B, 2, 4))

    def test_random_agree(self):
        rng = random.Random(7)
        for t, d, As, ss, B in sa.random_examples(rng, 40):
            at, sv = sa.tables(As, ss, B, d)
            good = sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
            self.assertEqual(sa.cnf_accepts(As, ss, B, t, d, echelon=False), good)
            nAs, nss, nB = sa.normalize(As, ss, B, t)
            self.assertTrue(sa.in_echelon(nss, t))
            self.assertEqual(sa.cnf_accepts(nAs, nss, nB, t, d), good)

    def test_decode_roundtrip(self):
        As, ss, B = sa.example1()
        nAs, nss, nB = sa.normalize(As, ss, B, 3)
        cnf, names = sa.encode(3, 2)
        val = sa.assignment(cnf, names, nAs, nss, nB, 3, 2)
        model = [v if val[v] else -v for v in range(1, cnf.nv + 1)]
        self.assertEqual(sa.decode(model, names, 3, 2), (nAs, nss, nB))


class TestMatrices(unittest.TestCase):
    def test_inverse(self):
        rng = random.Random(3)
        for _ in range(50):
            A = rng.getrandbits(16)
            if sa.rank_f2(sa.rows_of(A, 4)) == 4:
                self.assertEqual(sa.mat_mul(A, sa.mat_inv(A, 4), 4), sa.entries(4, [(i, i) for i in range(4)]))


if __name__ == "__main__":
    unittest.main()
