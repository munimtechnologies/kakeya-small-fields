# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Tests for lemma_l.py (note a159, Theorem 35). Standard library only; the numpy parts are
skipped when numpy is missing. Run: python test_lemma_l.py  (or python -m unittest -v)."""
import itertools
import math
import os
import random
import shutil
import sys
import tempfile
import unittest
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lemma_l as LL  # noqa: E402

try:
    import numpy  # noqa: F401
    HAVE_NP = True
except ImportError:
    HAVE_NP = False


def coord_functional(sp, i):
    c = [0] * sp.k
    c[i] = 1
    return sp.funcs.index(c)


class TestField(unittest.TestCase):
    def test_axioms_small(self):
        for q in (2, 3, 4, 5, 8, 9):
            F = LL.Field(q)
            R = range(q)
            for a, b, c in itertools.product(R, R, R):
                self.assertEqual(F.add[F.add[a][b]][c], F.add[a][F.add[b][c]])
                self.assertEqual(F.mul[F.mul[a][b]][c], F.mul[a][F.mul[b][c]])
                self.assertEqual(F.mul[a][F.add[b][c]], F.add[F.mul[a][b]][F.mul[a][c]])
            for a in R:
                self.assertEqual(F.add[a][0], a)
                self.assertEqual(F.mul[a][1], a)
                self.assertEqual(F.add[a][F.neg[a]], 0)
                if a:
                    self.assertIn(1, F.mul[a], f"no inverse for {a} in F_{q}")

    def test_inverses_large(self):
        for q in (16, 25, 27):
            F = LL.Field(q)
            for a in range(1, q):
                self.assertEqual(sorted(F.mul[a]), list(range(q)))
            rng = random.Random(q)
            for _ in range(3000):
                a, b, c = (rng.randrange(q) for _ in range(3))
                self.assertEqual(F.mul[F.mul[a][b]][c], F.mul[a][F.mul[b][c]])
                self.assertEqual(F.mul[a][F.add[b][c]], F.add[F.mul[a][b]][F.mul[a][c]])


class TestSpace(unittest.TestCase):
    def test_tables(self):
        for q, k in ((2, 3), (3, 2), (4, 2), (5, 2), (3, 3)):
            sp = LL.Space(q, k)
            self.assertEqual(len(sp.funcs), (q ** k - 1) // (q - 1))
            rng = random.Random(7)
            for _ in range(300):
                x, y = rng.randrange(sp.N), rng.randrange(sp.N)
                t = rng.randrange(q)
                self.assertEqual(sp.vadd[x][sp.vneg[x]], 0)
                self.assertEqual(sp.smul[1][x], x)
                self.assertEqual(sp.smul[t][sp.vadd[x][y]], sp.vadd[sp.smul[t][x]][sp.smul[t][y]])
                for L in sp.lval:
                    self.assertEqual(L[sp.vadd[x][y]], sp.F.add[L[x]][L[y]])
                    self.assertEqual(L[sp.smul[t][x]], sp.F.mul[t][L[x]])


class TestEntropy(unittest.TestCase):
    def test_conditional_entropy_direct(self):
        """profile's Lambda_l equals sum_t H(l(X) | Y_t) computed from the joint law."""
        rng = random.Random(3)
        for q, k in ((3, 2), (4, 2), (2, 3)):
            sp = LL.Space(q, k)
            for _ in range(5):
                P = [rng.randrange(sp.N) for _ in range(sp.N)]
                lam, lams = LL.profile(sp, P)
                for i, L in enumerate(sp.lval):
                    tot = 0.0
                    for t in range(q):
                        Y = sp.ys(P, t)
                        py = Counter(Y)
                        pya = Counter(zip(Y, L))
                        for (y, a), n in pya.items():
                            tot += n / sp.N * math.log2(py[y] / n)
                    self.assertAlmostEqual(tot, lams[i], places=9)
                direct = sum(LL.cond_ent(sp.ys(P, t)) for t in range(q))
                self.assertAlmostEqual(lam, direct, places=9)
                self.assertAlmostEqual(lam, LL.loss(sp, P), places=9)

    def test_k1_bound_exhaustive(self):
        """C_q(1): Lambda(P) <= q - 1 for every map of F_q, with equality attained."""
        for q in (2, 3, 4, 5):
            sp = LL.Space(q, 1)
            best = 0.0
            for rest in itertools.product(range(q), repeat=q - 1):
                P = [0] + list(rest)
                lam, lams = LL.profile(sp, P)
                self.assertLessEqual(lam, q - 1 + LL.TOL)
                self.assertAlmostEqual(lams[0], lam, places=9)
                best = max(best, lam)
            self.assertAlmostEqual(best, q - 1, places=9)

    def test_q2_conjecture_holds(self):
        """For q = 2, Lambda(P) <= k is a theorem (H(A) + H(A + X) >= H(X))."""
        rng = random.Random(11)
        for k in (2, 3, 4):
            sp = LL.Space(2, k)
            for _ in range(200):
                P = [rng.randrange(sp.N) for _ in range(sp.N)]
                self.assertLessEqual(LL.loss(sp, P), k + LL.TOL)


class TestTheorem35(unittest.TestCase):
    def test_products_are_tight(self):
        for q, k in ((2, 3), (3, 2), (4, 2), (5, 2), (3, 3), (9, 2), (8, 2)):
            sp = LL.Space(q, k)
            P = LL.frobenius_product(sp) if sp.F.p == 2 else LL.square_product(sp)
            lam, lams = LL.profile(sp, P)
            self.assertAlmostEqual(lam, k * (q - 1), places=9, msg=(q, k))
            li = coord_functional(sp, 0)
            self.assertAlmostEqual(lams[li], q - 1, places=9)
            self.assertAlmostEqual(min(lams), q - 1, places=9)
            self.assertAlmostEqual(LL.chain_bound(sp, P, li, 1), lam, places=9)
            self.assertFalse(LL.exact_beats(sp, P))

    def test_chain_bound_is_an_upper_bound(self):
        rng = random.Random(5)
        for q, k, trials in ((3, 2, 60), (2, 3, 60), (4, 2, 40), (5, 2, 15), (3, 3, 8),
                             (2, 4, 10)):
            sp = LL.Space(q, k)
            for _ in range(trials):
                P = [rng.randrange(sp.N) for _ in range(sp.N)]
                if rng.random() < 0.5:
                    # sparse images give large fibres, the interesting regime
                    img = [rng.randrange(sp.N) for _ in range(max(2, sp.N // 4))]
                    P = [rng.choice(img) for _ in range(sp.N)]
                lam, lams = LL.profile(sp, P)
                for li, L in enumerate(sp.lval):
                    for v in range(sp.N):
                        if L[v] == 1:
                            c = LL.chain_bound(sp, P, li, v, lams[li])
                            self.assertLessEqual(lam, c + LL.TOL, msg=(q, k, P, li, v))
                bc = LL.best_chain(sp, P)
                self.assertLessEqual(lam, bc[0] + LL.TOL)

    def test_identity_not_a_counterexample(self):
        for q, k in ((3, 2), (4, 2), (5, 2)):
            sp = LL.Space(q, k)
            P = list(range(sp.N))
            self.assertAlmostEqual(LL.loss(sp, P), k * math.log2(q), places=9)
            self.assertFalse(LL.exact_beats(sp, P))


@unittest.skipUnless(HAVE_NP, "numpy not installed")
class TestNumpy(unittest.TestCase):
    def test_np_profile_matches(self):
        import numpy as np
        rng = random.Random(9)
        for q, k in ((3, 2), (2, 3), (4, 2)):
            sp = LL.Space(q, k)
            tabs = LL.np_tables(sp)
            maps = [[rng.randrange(sp.N) for _ in range(sp.N)] for _ in range(30)]
            maps.append(LL.frobenius_product(sp) if sp.F.p == 2 else LL.square_product(sp))
            lam, lams = LL.np_profile(sp, np.array(maps, dtype=np.int32), tabs)
            for j, P in enumerate(maps):
                l1, ls1 = LL.profile(sp, P)
                self.assertAlmostEqual(float(lam[j]), l1, places=9)
                for i in range(len(sp.funcs)):
                    self.assertAlmostEqual(float(lams[i, j]), ls1[i], places=9)

    def test_small_runs(self):
        d = tempfile.mkdtemp()
        try:
            rep = LL.run_exhaustive(2, 2, d)
            self.assertTrue(rep["complete"])
            self.assertEqual(rep["maps"], 4 ** 3)
            self.assertAlmostEqual(rep["max_lambda"], 2.0, places=9)
            self.assertEqual(rep["maps_above_threshold"], 0)
            rep = LL.run_additive(2, 2, d)
            self.assertEqual(rep["maps"], 16)
            self.assertLessEqual(rep["max_lambda"], 2 + LL.TOL)
            rep = LL.run_anneal(3, 2, 2, 1, d)
            self.assertEqual(rep["C_counterexamples"], [])
            self.assertTrue(os.path.exists(os.path.join(d, "lemmal_anneal_q3k2_s1.json")))
        finally:
            shutil.rmtree(d)


if __name__ == "__main__":
    res = unittest.main(exit=False, verbosity=2).result
    print("TESTS", "OK" if res.wasSuccessful() else "FAILED", flush=True)
    sys.exit(0 if res.wasSuccessful() else 1)
