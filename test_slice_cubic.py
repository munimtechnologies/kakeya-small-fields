# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Tests for slice_cubic.py (note a161: Theorem 37, Lemma 111, Proposition 41). Standard library
only. Run: python test_slice_cubic.py  (or python -m unittest -v)."""
import math
import os
import random
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import inverse_family as IF  # noqa: E402
import lemma_l as LL  # noqa: E402
import slice_cubic as SC  # noqa: E402

L3 = math.log2(3)


def setup(q, s=None):
    E = IF.QuadExt(q)
    if s is None:
        s = E.join(0, 1)
    P = IF.inverse_map(E, s)
    sp = LL.Space(q, 2)
    _, lams = LL.profile(sp, P)
    return E, P, sp, lams


class TestSlices(unittest.TestCase):
    def check_all(self, q, s=None, v_step=1):
        E, P, sp, lams = setup(q, s)
        n = 0
        for li, L in enumerate(sp.lval):
            d = SC.kernel_dir(sp, li)
            vs = [v for v in range(sp.N) if L[v] == 1][::v_step]
            for v in vs:
                st = SC.slice_stats(sp, P, li, v)
                eps = SC.eps_flag(E, sp, li, v)
                allowed = [SC.predicted_T(q, eps, r) for r in SC.allowed_r(q, eps)]
                assembled = 0.0
                for a in range(1, q):
                    sizes, lam = st[a]
                    self.assertLessEqual(max(sizes), 3, (q, li, v, a))       # fibres <= 3
                    T = sizes.get(3, 0)
                    self.assertIn(T, allowed, (q, li, v, a, eps))             # group-law count
                    self.assertAlmostEqual(lam, SC.slice_lambda(q, T), places=9)
                    assembled += SC.slice_lambda(q, T)
                lam0 = st[0][1]
                if SC.proportional(sp, E.inv0(d), v):
                    self.assertAlmostEqual(lam0, math.log2(q), places=9)    # Q_0 affine
                else:
                    self.assertAlmostEqual(lam0, q - 1, places=9)           # Q_0 an arc
                chain = lams[li] + (lam0 + assembled) / q
                self.assertAlmostEqual(chain, LL.chain_bound(sp, P, li, v, lams[li]), places=9)
                n += 1
        return n

    def test_q4_all_l_v(self):
        self.assertEqual(self.check_all(4), 5 * 4)       # q + 1 lines, q vectors v each

    def test_q4_other_s(self):
        E = IF.QuadExt(4)
        for s in (E.join(1, 1), E.join(2, 3)):
            self.assertEqual(self.check_all(4, s=s), 20)

    def test_q8_all_l_v(self):
        self.assertEqual(self.check_all(8), 9 * 8)

    def test_q16_all_l_v(self):
        self.assertEqual(self.check_all(16), 17 * 16)

    def test_eps_one_forces_flex_count(self):
        """With v in F_q d^{-1} the point at infinity is a flex: T = ((q-2)^2 + 2 gcd(3, q+1) - 6)/6."""
        for q, T in ((4, 0), (8, 6), (16, 32)):
            self.assertEqual(SC.theorem37_chain(q)[1], T)


class TestTheorem37(unittest.TestCase):
    def test_closed_form_chain(self):
        for q in (4, 8, 16):
            E, P, sp, lams = setup(q)
            for li, f in enumerate(sp.funcs):
                v = SC.inverse_v(E, sp, li)
                if f == [0, 1]:                          # ker l = F_q: no such v
                    self.assertIsNone(v)
                    continue
                self.assertEqual(SC.eps_flag(E, sp, li, v), 1)
                c = LL.chain_bound(sp, P, li, v, lams[li])
                self.assertAlmostEqual(c, SC.theorem37_chain(q)[0], places=9)
                self.assertLess(c, 2 * (q - 1))

    def test_q4_value_and_best(self):
        self.assertAlmostEqual(SC.theorem37_chain(4)[0], 47 / 8, places=12)
        E, P, sp, _ = setup(4)
        self.assertLessEqual(LL.best_chain(sp, P)[0], 47 / 8 + LL.TOL)

    def test_margin_all_even_q(self):
        for e in range(2, 31):
            q = 2 ** e
            c, T = SC.theorem37_chain(q)
            self.assertGreaterEqual(T, 0)
            self.assertLess(c, 2 * (q - 1), q)
            # the cruder bound (every slice a != 0 at most q - 1) already works:
            crude = q - 1 + (q - 2) / q ** 2 + (math.log2(q) + (q - 1) ** 2) / q
            self.assertLess(crude, 2 * (q - 1), q)


class TestLemma111(unittest.TestCase):
    def test_slack_identity_random_maps(self):
        rng = random.Random(161)
        for q, k, maps in ((3, 2, 6), (4, 2, 4), (2, 3, 6)):
            sp = LL.Space(q, k)
            for i in range(maps):
                if i % 2:
                    vals = rng.sample(range(sp.N), 3)       # large fibres
                    P = [rng.choice(vals) for _ in range(sp.N)]
                else:
                    P = [rng.randrange(sp.N) for _ in range(sp.N)]
                lam = LL.loss(sp, P)
                for li, L in enumerate(sp.lval):
                    for v in [v for v in range(sp.N) if L[v] == 1][:4]:
                        self.assertAlmostEqual(LL.chain_bound(sp, P, li, v),
                                               lam + SC.slack(sp, P, li, v), places=9)

    def test_products_have_zero_slack(self):
        sp = LL.Space(3, 2)
        f = [0, 1, 1]                       # x -> x^2 on F_3, an arc (Lambda = 2)
        P = [sp.enc([f[c[0]], f[c[1]]]) for c in sp.coords]
        li = sp.funcs.index([1, 0])
        self.assertAlmostEqual(SC.slack(sp, P, li, sp.enc([1, 0])), 0.0, places=12)
        self.assertAlmostEqual(LL.loss(sp, P), 4.0, places=9)


class F9:
    """F_9 = F_3[i]/(i^2 + 1); c0 + c1 i is encoded as c0 + 3 c1 (lemma_l's Space(3, 2))."""

    @staticmethod
    def mul(x, z):
        a0, a1, b0, b1 = x % 3, x // 3, z % 3, z // 3
        return (a0 * b0 - a1 * b1) % 3 + 3 * ((a0 * b1 + a1 * b0) % 3)

    @staticmethod
    def add(x, z):
        return (x % 3 + z % 3) % 3 + 3 * ((x // 3 + z // 3) % 3)

    @classmethod
    def power(cls, x, e):
        r = 1
        for _ in range(e):
            r = cls.mul(r, x)
        return r


class TestProposition41(unittest.TestCase):
    """q = 3: every map x -> a/x + b x on F_9 (a != 0, b outside F_3) satisfies Lemma L."""

    def test_field(self):
        for x in range(1, 9):
            self.assertEqual(F9.mul(x, F9.power(x, 7)), 1)

    def test_family(self):
        sp = LL.Space(3, 2)
        for x in range(9):
            for t in range(3):
                self.assertEqual(F9.mul(t, x), sp.smul[t][x])
        n = 0
        for a in range(1, 9):
            square = F9.power(a, 4) == 1
            for b in range(3, 9):
                P = [F9.add(F9.mul(a, F9.power(x, 7)), F9.mul(b, x)) for x in range(9)]
                lam, lams = LL.profile(sp, P)
                if square:
                    self.assertAlmostEqual(lam, L3 / 3 + 20 / 9, places=9, msg=(a, b))
                    self.assertAlmostEqual(min(lams), L3 / 3 + 8 / 9, places=9, msg=(a, b))
                else:
                    self.assertAlmostEqual(lam, 2 * L3 / 3 + 16 / 9, places=9, msg=(a, b))
                    self.assertAlmostEqual(min(lams), L3 / 3 + 4 / 3, places=9, msg=(a, b))
                self.assertLessEqual(min(lams), 2)
                n += 1
        self.assertEqual(n, 48)


if __name__ == "__main__":
    res = unittest.main(exit=False, verbosity=2).result
    print("TESTS", "OK" if res.wasSuccessful() else "FAILED", flush=True)
    sys.exit(0 if res.wasSuccessful() else 1)
