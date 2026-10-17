# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import m4_irred as mi


def diagonal_system():
    # Lemma 23(d) with t = 2: V = F_2^4 with (u_1, u_2, v_1, v_2) in bits 0..3, A_h = diag(u_1, u_2),
    # sigma_i = (1 + u_i) v_i.
    at, sv = [], []
    for h in range(16):
        u1, u2, v1, v2 = h & 1, (h >> 1) & 1, (h >> 2) & 1, (h >> 3) & 1
        at.append(u1 | (u2 << 3))
        sv.append(((1 ^ u1) & v1) | (((1 ^ u2) & v2) << 1))
    return at, sv


class TestMasks(unittest.TestCase):
    def test_masks(self):
        self.assertEqual(mi.block_mask(2, 1), 11)          # every entry but (1, 0)
        self.assertEqual(mi.compression_mask(2, 1, 1), 7)  # every entry but (1, 1)
        self.assertEqual(mi.block(mi.identity(3), 3, 1, 3), mi.identity(2))
        self.assertEqual(mi.block(mi.entries(3, [(2, 1), (0, 2)]), 3, 1, 3), mi.entries(2, [(1, 0)]))

    def test_irreducible(self):
        subs = mi.proper_subspaces(2)
        self.assertEqual(len(subs), 3)
        self.assertTrue(mi.is_irreducible([2, 4], 2, subs))    # E_01, E_10: no invariant line
        self.assertFalse(mi.is_irreducible([2], 2, subs))      # E_01 kills e_0
        self.assertFalse(mi.is_irreducible([11], 2, subs))     # upper triangular keeps e_0
        self.assertEqual(len(mi.proper_subspaces(4)), 65)


class TestLemma27(unittest.TestCase):
    def test_diagonal(self):
        at, sv = diagonal_system()
        self.assertTrue(mi.is_system(at, sv, 4, 2))
        xms = {m: mi.xor_masks(m) for m in range(0, 5)}
        r = mi.lemma27_check(at, sv, 4, 2, 1, xms)
        self.assertTrue(r["quotient"] and r["inside"] and r["restricted"] and r["exact"])
        self.assertEqual((r["lc"], r["codim_q"], r["lc_u"]), (2, 1, 1))
        self.assertFalse(r["aniso"])

    def test_random_reducible(self):
        rng = random.Random(3)
        xms = {m: mi.xor_masks(m) for m in range(0, 6)}
        for t, count in ((2, 8), (3, 10)):
            for _ in range(count):
                d = rng.randint(1, t - 1)
                B = mi.independent([rng.randrange(1, 1 << (t * t)) & mi.block_mask(t, d)
                                    for _ in range(rng.randint(1, 3))])
                m, at = mi.system(B, rng.randint(0, min(t, 5 - len(B))))
                if m == 0:
                    continue
                tabs = mi.mon_tables(m)
                sol = mi.solve_sigma(at, m, t)
                for _ in range(2 if sol else 0):
                    v = mi.combine(sol, rng.getrandbits(len(sol)))
                    sv = mi.table(mi.sigma_from_coeffs(v, tabs, t), m)
                    r = mi.lemma27_check(at, sv, m, t, d, xms)
                    self.assertTrue(r["exact"])
                    self.assertTrue(r["quotient"] and r["inside"] and r["restricted"])
                    self.assertLessEqual(r["lc"], r["codim_q"] + r["lc_u"])
                    self.assertLessEqual(r["lc"], t)
                    if r["aniso"]:
                        self.assertLessEqual(m, t)


class TestLemma28(unittest.TestCase):
    def test_compression(self):
        rng = random.Random(4)
        xms = {m: mi.xor_masks(m) for m in range(0, 7)}
        for t, y in ((2, 0), (2, 1), (3, 0), (3, 1)):
            B = [1 << b for b in range(t * t) if (mi.compression_mask(t, 1, 1) >> b) & 1]
            if t == 3:
                B = B[:4]
            m, at = mi.system(B, y)
            tabs = mi.mon_tables(m)
            sol = mi.solve_sigma(at, m, t)
            picks = range(1 << len(sol)) if len(sol) <= 8 else \
                [rng.getrandbits(len(sol)) for _ in range(120)]
            for p in picks:
                sv = mi.table(mi.sigma_from_coeffs(mi.combine(sol, p), tabs, t), m)
                r = mi.lemma28_check(at, sv, m, t, xms)
                self.assertTrue(r["tau_pi"])
                self.assertTrue(r["exact"])
                self.assertLessEqual(r["lc"], t)
                if r["aniso"]:
                    self.assertLessEqual(m, t)
                if not r["pi_zero"]:
                    self.assertTrue(r["hyperplane"])
                    self.assertTrue(r["beta_zero"])


class TestControl(unittest.TestCase):
    def test_anisotropic_form(self):
        # x^2 + xy + y^2 on F_2^2 is anisotropic, and it is no solution of (*) with alpha = 0.
        tabs = mi.mon_tables(2)
        sv = mi.table(mi.sigma_from_coeffs(7, tabs, 1), 2)
        self.assertEqual(sv, [0, 1, 1, 1])
        self.assertEqual(mi.zero_set(sv), 0)
        sol = mi.solve_sigma([0, 0, 0, 0], 2, 1)
        self.assertEqual(len(sol), 2)
        self.assertEqual(mi.rank_f2(sol + [7]), 3)


if __name__ == "__main__":
    unittest.main()
