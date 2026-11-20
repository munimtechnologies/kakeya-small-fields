# Tests for sticky_kexact.py (stdlib only; the CP-SAT models are not built here).
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.

import random
import unittest

import sticky_s7 as s7
import sticky_kexact as kx


def random_maps(h, rng):
    return {a: tuple(rng.randrange(3) for _ in range(3)) for a in kx.prefixes(h)}


class TestTables(unittest.TestCase):
    def test_roundtrip(self):
        for P, h in ((s7.tree_A, 3), (s7.tree_B, 3), (s7.tree_H, 4), (s7.tree_G, 5),
                     (s7.classical, 2)):
            mp = kx.maps_of(P, h)
            Q = kx.fn_of(mp)
            for d in s7.domain(h):
                self.assertEqual(Q(d), tuple(x % 3 for x in P(d)))

    def test_classical_kappa(self):
        for h, want in ((1, 4), (2, 8), (3, 16)):
            self.assertEqual(kx.kappa0(kx.maps_of(s7.classical, h), h), want)

    def test_H_and_G(self):
        mH = kx.maps_of(s7.tree_H, 4)
        self.assertEqual(kx.kappa0(mH, 4), 31)
        self.assertEqual(s7.kappa(s7.tree_H, 4)[0], 31)
        self.assertEqual(kx.kappa0(kx.maps_of(s7.tree_G, 5), 5), 62)
        self.assertEqual([len(s) for s in s7.slices(kx.triangle(s7.tree_H), 5)], [31, 31, 31])

    def test_translation_invariance(self):
        rng = random.Random(7)
        for h in (2, 3):
            for _ in range(5):
                mp = random_maps(h, rng)
                c = [rng.randrange(3) for _ in range(h)]
                self.assertEqual(kx.kappa0(mp, h), kx.kappa0(kx.shift_maps(mp, c), h))
                mq = random_maps(h, rng)
                self.assertEqual(kx.lam0(mp, mq, h),
                                 kx.lam0(kx.shift_maps(mp, c), kx.shift_maps(mq, c), h))

    def test_lemma_166(self):
        """|S_i| + |S_{i+1} u (S_{i+2} + w)| equals kappa0 of R(d) = rho_i P(d + e) + e, e = -w."""
        rng = random.Random(11)
        for h in (1, 2, 3):
            for _ in range(4):
                mp = random_maps(h, rng)
                P = kx.fn_of(mp)
                S = s7.slices(P, h)
                for i in range(3):
                    Q = s7.rho(P, i)
                    for w in s7.domain(h):
                        v1 = len(S[i]) + len(S[(i + 1) % 3] | s7.translate(S[(i + 2) % 3], w))
                        e = tuple((-x) % 3 for x in w)

                        def R(d, Q=Q, e=e):
                            dd = tuple((a + b) % 3 for a, b in zip(d, e))
                            return tuple((q + x) % 3 for q, x in zip(Q(dd), e))
                        self.assertTrue(s7.is_sticky(R, h))
                        self.assertEqual(kx.kappa0(kx.maps_of(R, h), h), v1)
                # hence s7.kappa (min over i, w) equals the min of kappa0 over these trees
                self.assertLessEqual(s7.kappa(P, h)[0], kx.kappa0(mp, h))


class TestPairs(unittest.TestCase):
    def setUp(self):
        self.mA = kx.maps_of(s7.tree_A, 3)
        self.mB = kx.maps_of(s7.tree_B, 3)
        self.mH = kx.maps_of(s7.tree_H, 4)

    def test_a196_pair(self):
        self.assertEqual(kx.lam0(self.mA, self.mB, 3), 31)
        self.assertEqual(kx.lam_best(self.mA, self.mB, 3)[0], 31)
        N = kx.pair_tree(kx.fn_of(self.mA), kx.fn_of(self.mB))
        for d in s7.domain(4):
            self.assertEqual(N(d), s7.tree_H(d))
        self.assertEqual([len(s) for s in s7.slices(kx.triangle(N), 5)], [31, 31, 31])

    def test_pair_identity_random(self):
        """|N_0| + |N_1 u N_2| = lambda(A, B) for N = root x^2 over (A, B, B(-e))."""
        rng = random.Random(5)
        for h in (1, 2, 3):
            for _ in range(4):
                mA, mB = random_maps(h, rng), random_maps(h, rng)
                N = kx.pair_tree(kx.fn_of(mA), kx.fn_of(mB))
                self.assertTrue(s7.is_sticky(N, h + 1))
                self.assertEqual(kx.kappa0(kx.maps_of(N, h + 1), h + 1), kx.lam0(mA, mB, h))
                T = kx.triangle(N)
                v = kx.lam0(mA, mB, h)
                self.assertEqual([len(s) for s in s7.slices(T, h + 2)], [v, v, v])

    def test_HH(self):
        self.assertEqual(kx.lam_best(self.mH, self.mH, 4)[0], 62)

    def test_hints_are_normalised(self):
        hA, hB = kx.pair_hint(self.mA, self.mB, 3)
        self.assertEqual(kx.lam0(hA, hB, 3), 31)
        for j in range(3):
            self.assertEqual(hB[(1,) * j][1], 0)
        hH, hH2 = kx.pair_hint(self.mH, self.mH, 4)
        self.assertEqual(kx.lam0(hH, hH2, 4), 62)
        md = kx.normalised(self.mH, 4, range(4))
        self.assertEqual(kx.kappa0(md, 4), 31)
        for j in range(4):
            self.assertEqual(md[(1,) * j][1], 0)
        mr = kx.normalised(self.mH, 4, range(1, 4))
        self.assertEqual(mr[()], (0, 1, 1))
        self.assertEqual(kx.kappa0(mr, 4), 31)
        mG = kx.normalised(kx.maps_of(s7.tree_G, 5), 5, range(1, 5))
        self.assertEqual(mG[()], (0, 1, 1))
        self.assertEqual(kx.kappa0(mG, 5), 62)


class TestVerdict(unittest.TestCase):
    def rec(self, name, status, v, bound=None, hint=None, ok=True):
        return {"name": name, "status": status, "objective": v, "bound": bound if bound else v,
                "verified_value": v, "verified_ok": ok, "hint_value": hint}

    def sanity(self):
        return [self.rec("kappa1", "OPTIMAL", 4), self.rec("kappa2", "OPTIMAL", 8),
                self.rec("kappa3", "OPTIMAL", 16), self.rec("lambda2", "OPTIMAL", 16)]

    def test_k4_31(self):
        recs = self.sanity() + [self.rec("lambda3", "OPTIMAL", 31, hint=31),
                                self.rec("kappa4_direct", "FEASIBLE", 31, bound=28, hint=31)]
        v = kx.verdict(recs)
        self.assertEqual(v["verdict"], "KAPPA4-31")
        self.assertIn("LAMBDA3-EXACT-31", v["flags"])

    def test_k4_30(self):
        recs = self.sanity() + [self.rec("lambda3", "OPTIMAL", 30, hint=31)]
        v = kx.verdict(recs)
        self.assertEqual(v["verdict"], "BASE-IMPROVED")
        self.assertAlmostEqual(v["base_upper_bound"], round(30 ** 0.2, 6))

    def test_bug(self):
        recs = self.sanity() + [self.rec("lambda3", "OPTIMAL", 29, hint=31)]
        self.assertEqual(kx.verdict(recs)["verdict"], "BUG")
        recs = self.sanity()[:3]
        self.assertEqual(kx.verdict(recs)["verdict"], "BUG")
        recs = self.sanity() + [self.rec("lambda3", "FEASIBLE", 31, bound=32, hint=31)]
        self.assertEqual(kx.verdict(recs)["verdict"], "BUG")

    def test_h6(self):
        recs = self.sanity() + [self.rec("lambda4", "FEASIBLE", 61, bound=40, hint=62)]
        v = kx.verdict(recs)
        self.assertEqual(v["verdict"], "BASE-IMPROVED")
        self.assertIn("BASE-IMPROVED-H6", v["flags"])


if __name__ == "__main__":
    unittest.main()
