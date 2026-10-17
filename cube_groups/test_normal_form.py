# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import normal_form as nf


class TestNormalForm(unittest.TestCase):
    def test_coeffs_roundtrip(self):
        rng = random.Random(1)
        m, t = 4, 2
        tabs = nf.mon_tables(m)
        N = len(tabs)
        for _ in range(20):
            c = rng.getrandbits(t * N)
            S = nf.sigma_from_coeffs(c, tabs, t)
            self.assertEqual(nf.coeffs_of(lambda h: nf.sig(S, h), m, t), c)

    def test_nf_generators_pointwise(self):
        rng = random.Random(2)
        t = 2
        B = nf.random_subspace(nf.structured(t)["End"], 2, rng)
        m, at = nf.system(B, 1)
        tabs = nf.mon_tables(m)
        gens = nf.nf_basis(at, m, t)
        k = 0
        for j in range(m):
            for r in range(t):
                S = nf.sigma_from_coeffs(gens[k], tabs, t)
                for h in range(1 << m):
                    e = 1 << r
                    want = (e ^ nf.mat_apply(at[h], e, t)) if (h >> j) & 1 else 0
                    self.assertEqual(nf.sig(S, h), want)
                k += 1

    def test_rank_le_1_in_nf(self):
        # Lemma 23(c): rank alpha <= 1 gives the normal form, for every t.
        rng = random.Random(3)
        tabs = {}
        for c in (0, 1):
            for B in nf.subspaces(4, c):
                for y in range(3):
                    self.assertTrue(nf.nf_check(B, y, 2, tabs, rng)["in_nf"])
        t = 3
        w = nf.entries(t, [(1, 0), (2, 1), (0, 2), (1, 2)])
        for A in (nf.entries(t, [(0, 0)]), nf.identity(t), nf.entries(t, [(0, 1), (1, 2)]), w,
                  nf.entries(t, [(0, 0), (1, 1), (0, 2)])):
            for y in range(3):
                self.assertTrue(nf.nf_check([A], y, t, tabs, rng)["in_nf"])

    def test_diag_example(self):
        # Lemma 23(d): the diagonal example is a system in normal form needing codimension t.
        for t in (1, 2):
            d = nf.check_diag(t)
            self.assertTrue(d["identity"])
            self.assertTrue(d["in_sol"])
            self.assertTrue(d["in_nf"])
            self.assertTrue(d["exact"])
            self.assertEqual(d["least_codim"], t)

    def test_full_action_zero(self):
        # Lemma 21(c): alpha onto End(X), t >= 2, forces sigma = 0.
        rec = nf.nf_check(nf.structured(2)["End"], 0, 2, {}, random.Random(4))
        self.assertEqual(rec["sol_dim"], 0)

    def test_image_and_nf_on_random_t2(self):
        # Lemma 23(a) holds for every solution; the normal-form solutions lie in Sol n NF.
        rng = random.Random(5)
        tabs = {}
        End = nf.structured(2)["End"]
        for d in (2, 3):
            for _ in range(4):
                B = nf.random_subspace(End, d, rng)
                for y in range(3):
                    rec = nf.nf_check(B, y, 2, tabs, rng)
                    self.assertEqual(rec["image_violations"], 0)
                    self.assertLessEqual(rec["inter_dim"], rec["sol_dim"])

    def test_constraint_of_lemma_23b(self):
        # Diagonal alpha (commuting idempotents): every lam gives a solution.
        rng = random.Random(6)
        t = 2
        B = nf.structured(t)["diag"]
        m, at = nf.system(B, 1)
        tabs = nf.mon_tables(m)
        gens = nf.nf_basis(at, m, t)
        for _ in range(5):
            S = nf.sigma_from_coeffs(nf.combine(gens, rng.getrandbits(len(gens))), tabs, t)
            self.assertTrue(nf.identity_holds(at, S, m, t))
        # Nilpotent alpha = h_1 N with lam(e_1) = e_2 and N e_2 = e_1: the constraint fails, and so
        # does the identity.
        N = nf.entries(t, [(0, 1)])
        m, at = nf.system([N], 1)
        tabs = nf.mon_tables(m)
        e2 = 1 << 1
        S = nf.sigma_from_coeffs(
            nf.coeffs_of(lambda h: (e2 ^ nf.mat_apply(at[h], e2, t)) if h & 1 else 0, m, t),
            tabs, t)
        self.assertFalse(nf.identity_holds(at, S, m, t))


if __name__ == "__main__":
    unittest.main()
