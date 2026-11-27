# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Controls for f3cert/f3cert.py (f3cert/PREREG.md).

1. Bit-sliced F_3 arithmetic, spans, canonical keys and intersections against brute force.
2. The linear copy model reproduces Tomar's six-pair page exactly
   (z0..z5 = (a,b), (a,c), (d,b), (d,c), (e,a+b-e), (e,c)).
3. SOUNDNESS on real distributions: for random difference-injective laws (x, y) = (f(d), f(d)-d)
   with d uniform on F_3^n, the conditional copies are carried out exactly on the joint law of
   the symbols, and then: every vertex has the law of (x, y); all spans merged into one entropy
   class (closure, equal-law identifications) have equal entropy; every span has entropy at
   most its F_3-dimension (in units of log 3^n); every submodularity row (plain and
   intersection form), monotonicity row and conditional-independence row holds.
4. If scipy is installed: the LP on Tomar's page gives a certified bound between 1/2 and the
   value 0.579380 of the KLSS construction (which every sound bound must respect)."""
import itertools
import math
import os
import random
import sys
import unittest
from fractions import Fraction

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import f3cert as F
except ImportError:  # pragma: no cover
    import f3cert as F


def naive_rank(vecs, m):
    rows = [list(v) for v in vecs]
    r = 0
    for c in range(m):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] % 3:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = 1 if rows[r][c] % 3 == 1 else 2
        rows[r] = [(inv * a) % 3 for a in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % 3:
                f = rows[i][c]
                rows[i] = [(a - f * b) % 3 for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def span_elements(S, m):
    B = S.basis()
    out = set()
    for cs in itertools.product(range(3), repeat=len(B)):
        v = F.ZERO
        for c, b in zip(cs, B):
            v = F.vadd(v, F.vscale(c, b))
        out.add(tuple(F.to_list(v, m)))
    return out


class TestArithmetic(unittest.TestCase):
    def test_vector_ops(self):
        rng = random.Random(1)
        for _ in range(3000):
            m = rng.randint(1, 70)
            a = [rng.randrange(3) for _ in range(m)]
            b = [rng.randrange(3) for _ in range(m)]
            x, y = F.from_list(a), F.from_list(b)
            self.assertEqual(F.to_list(F.vadd(x, y), m), [(u + v) % 3 for u, v in zip(a, b)])
            self.assertEqual(F.to_list(F.vsub(x, y), m), [(u - v) % 3 for u, v in zip(a, b)])
            self.assertEqual(F.to_list(F.vneg(x), m), [(-u) % 3 for u in a])
            for c in range(-3, 4):
                self.assertEqual(F.to_list(F.vscale(c, x), m), [(c * u) % 3 for u in a])
            self.assertEqual(x[0] & x[1], 0)

    def test_span_rank_key_membership(self):
        rng = random.Random(2)
        m = 6
        for _ in range(400):
            k = rng.randint(0, 7)
            vecs = [[rng.randrange(3) for _ in range(m)] for _ in range(k)]
            S = F.span_of([F.from_list(v) for v in vecs])
            self.assertEqual(S.dim(), naive_rank(vecs, m))
            # the same subspace from shuffled, rescaled and recombined generators
            gens = [F.from_list(v) for v in vecs]
            rng.shuffle(gens)
            gens = [F.vscale(rng.choice((1, 2)), g) for g in gens]
            if len(gens) >= 2:
                gens.append(F.vadd(gens[0], gens[1]))
            T = F.span_of(gens)
            self.assertEqual(S.key(m + 1), T.key(m + 1))
            elems = span_elements(S, m)
            self.assertEqual(len(elems), 3 ** S.dim())
            for _ in range(20):
                w = [rng.randrange(3) for _ in range(m)]
                self.assertEqual(S.contains(F.from_list(w)), tuple(w) in elems)
            # RREF: pivot coefficient 1 and zero in every other row
            for c, r in S.rows.items():
                self.assertEqual(F.vsupp(r).bit_length() - 1, c)
                self.assertEqual(F.coef(r, c), 1)
                for c2, r2 in S.rows.items():
                    if c2 != c:
                        self.assertEqual(F.coef(r2, c), 0)

    def test_intersection(self):
        rng = random.Random(3)
        m = 5
        for _ in range(300):
            A = F.span_of([F.from_list([rng.randrange(3) for _ in range(m)])
                           for _ in range(rng.randint(0, 4))])
            B = F.span_of([F.from_list([rng.randrange(3) for _ in range(m)])
                           for _ in range(rng.randint(0, 4))])
            I = F.intersect(A, B, m)
            ea, eb, ei = span_elements(A, m), span_elements(B, m), span_elements(I, m)
            self.assertEqual(ei, ea & eb)

    def test_tracked_map(self):
        rng = random.Random(4)
        m = 6
        for _ in range(200):
            S = F.Span(track=True)
            pairs = []
            for _ in range(rng.randint(1, 5)):
                v = F.from_list([rng.randrange(3) for _ in range(m)])
                im = F.from_list([rng.randrange(3) for _ in range(m)])
                if not S.contains(v):
                    S.insert(v, im)
                    pairs.append((v, im))
            # the tracked map is linear and sends each inserted vector to its image
            for v, im in pairs:
                r, acc = S.reduce(v)
                self.assertEqual(r, F.ZERO)
                self.assertEqual(acc, im)
            if len(pairs) >= 2:
                (v1, i1), (v2, i2) = pairs[0], pairs[1]
                r, acc = S.reduce(F.vsub(v1, F.vscale(2, v2)))
                self.assertEqual(r, F.ZERO)
                self.assertEqual(acc, F.vsub(i1, F.vscale(2, i2)))


class TestTomarPage(unittest.TestCase):
    def test_parametrisation(self):
        cfg = F.build_config(F.TOMAR_PAGE)
        a, b, c, d, e = (F.unit(k) for k in range(5))
        want = [(a, b), (a, c), (d, b), (d, c), (e, F.vsub(F.vadd(a, b), e)), (e, c)]
        self.assertEqual(cfg.nsym, 5)
        self.assertEqual([(cfg.X[v], cfg.Y[v]) for v in range(6)], want)


EXTRA_PAGE_STEP = {"U": [0, 1, 2, 3, 4, 5], "V": [[2, [1, 0]], [0, [1, 1]]]}


class Sim:
    """Exact conditional copies of a law on F_3^n, carried out on the symbols.  Group elements
    of F_3^n are integers 0 .. 3^n - 1 (base-3 digits); f maps d to x and y = x - d."""

    def __init__(self, cfg, n, f):
        self.cfg, self.n = cfg, n
        self.q = q = 3 ** n
        elems = list(itertools.product(range(3), repeat=n))
        idx = {e: i for i, e in enumerate(elems)}
        self.ADD = [[idx[tuple((u + v) % 3 for u, v in zip(a, b))] for b in elems] for a in elems]
        self.SUB = [[idx[tuple((u - v) % 3 for u, v in zip(a, b))] for b in elems] for a in elems]
        self.base = {}
        for dd in range(q):
            x = f[dd]
            y = self.SUB[x][dd]                        # d = x - y
            self.base[(x, y)] = self.base.get((x, y), Fraction(0)) + Fraction(1, q)
        joint = dict(self.base)
        for st in cfg.steps:
            G = [self.nz(r) for r in st["G"].basis()]
            comp = [self.nz(fk) for _k, fk in st["comp"]]
            mgu, mg = {}, {}
            for w, p in joint.items():
                g = tuple(self.ev(r, w) for r in G)
                u = tuple(self.ev(fk, w) for fk in comp)
                mgu[(g, u)] = mgu.get((g, u), Fraction(0)) + p
                mg[g] = mg.get(g, Fraction(0)) + p
            byg = {}
            for (g, u), p in mgu.items():
                byg.setdefault(g, []).append((u, p / mg[g]))
            new = {}
            for w, p in joint.items():
                g = tuple(self.ev(r, w) for r in G)
                for u, pu in byg[g]:
                    key = w + u
                    new[key] = new.get(key, Fraction(0)) + p * pu
            joint = new
        total = sum(joint.values())
        assert total == 1
        self.joint = [(w, float(p)) for w, p in joint.items()]
        self.cache = {}

    @staticmethod
    def nz(vec):
        out = []
        c = 0
        s = F.vsupp(vec)
        while s >> c:
            k = F.coef(vec, c)
            if k:
                out.append((c, k))
            c += 1
        return out

    def ev(self, nz, w):
        acc = 0
        A, S = self.ADD, self.SUB
        for c, k in nz:
            acc = A[acc][w[c]] if k == 1 else S[acc][w[c]]
        return acc

    def H(self, Sp):
        B = Sp.basis()
        key = tuple(B)
        if key in self.cache:
            return self.cache[key]
        nzs = [self.nz(r) for r in B]
        marg = {}
        for w, p in self.joint:
            t = tuple(self.ev(r, w) for r in nzs)
            marg[t] = marg.get(t, 0.0) + p
        h = -sum(p * math.log(p) for p in marg.values() if p > 0) / math.log(self.q)
        self.cache[key] = h
        return h

    def law(self, fx, fy):
        out = {}
        a, b = self.nz(fx), self.nz(fy)
        for w, p in self.joint:
            t = (self.ev(a, w), self.ev(b, w))
            out[t] = out.get(t, 0.0) + p
        return out


class TestSoundness(unittest.TestCase):
    def run_case(self, steps, n, seed, nrows):
        rng = random.Random(seed)
        f = {dd: rng.randrange(3 ** n) for dd in range(3 ** n)}
        cfg = F.build_config(steps)
        sim = Sim(cfg, n, f)
        seen = []
        reg = F.Registry(cfg, trace=lambda S, cid: seen.append((cid, sim.H(S), S.dim())))
        # vertex laws
        base = {k: float(v) for k, v in sim.base.items()}
        for v in range(cfg.nv()):
            law = sim.law(cfg.X[v], cfg.Y[v])
            self.assertEqual(set(k for k, p in law.items() if p > 1e-12), set(base))
            for k, p in base.items():
                self.assertAlmostEqual(law[k], p, places=12)
        rows = []
        R = []
        for v in range(cfg.nv()):
            R.extend(cfg.readings(v))
        for _ in range(nrows):
            K = [rng.choice(R) for _ in range(rng.randint(0, 3))]
            i, j = rng.choice(R), rng.choice(R)
            if rng.random() < 0.3:      # cross forms too
                i = F.vadd(i, F.vscale(rng.choice((1, 2)), rng.choice(R)))
            rows.append(("ge",) + F.sub_row(reg, K, i, j, True))
            rows.append(("ge",) + F.sub_row(reg, K, i, j, False))
            for t, spec in F.mono_rows(reg, K, i, j):
                rows.append(("ge", t, spec))
        for s in range(len(cfg.steps)):
            rows.append(("eq",) + F.ci_row(reg, s))
        # all members of an entropy class have equal entropy, and the uniform bound holds
        val = {}
        for cid, h, dim in seen:
            self.assertLessEqual(h, dim + 1e-9)
            r = reg.find(cid)
            if r in val:
                self.assertAlmostEqual(val[r], h, places=9)
            else:
                val[r] = h
        for root in set(reg.find(c) for c in range(len(reg.parent))):
            self.assertIn(root, val)
            self.assertLessEqual(val[root], reg.ub[root] + 1e-9)
        for kind, terms, spec in rows:
            tot = sum(a * val[reg.find(cid)] for cid, a in terms)
            if kind == "ge":
                self.assertGreaterEqual(tot, -1e-9, msg=str(spec))
            else:
                self.assertAlmostEqual(tot, 0.0, places=9, msg=str(spec))
        # vertex 0: h(d) = 1 (uniform difference), h(x, y) = h(d)
        x, y, s, d, xy = F.vertex0(reg)
        self.assertEqual(reg.find(d), reg.find(xy))
        self.assertAlmostEqual(val[reg.find(d)], 1.0, places=12)
        return reg

    def test_tomar_page_n1(self):
        for seed in range(6):
            self.run_case(F.TOMAR_PAGE, 1, seed, 120)

    def test_tomar_page_plus_page_copy_n1(self):
        for seed in range(2):
            self.run_case(F.TOMAR_PAGE + [EXTRA_PAGE_STEP], 1, 100 + seed, 100)

    def test_tomar_page_n2(self):
        self.run_case(F.TOMAR_PAGE, 2, 7, 30)

    def test_product_witness_value(self):
        # the KLSS / Ruzsa witness f = (0 -> 0, 1 -> 0, 2 -> 1) has h(x) = h(y) = h(s) = KLSS_W
        f = {0: 0, 1: 0, 2: 1}
        cfg = F.build_config([])
        sim = Sim(cfg, 1, f)
        for vec in (cfg.X[0], cfg.Y[0], cfg.S(0)):
            self.assertAlmostEqual(sim.H(F.span_of([vec])), F.KLSS_W, places=12)
        self.assertAlmostEqual(sim.H(F.span_of([cfg.D(0)])), 1.0, places=12)


def _have_scipy():
    try:
        import scipy  # noqa: F401
        return True
    except ImportError:
        return False


@unittest.skipUnless(_have_scipy(), "scipy not installed")
class TestLP(unittest.TestCase):
    def test_tomar_page_lp(self):
        cfg = F.build_config(F.TOMAR_PAGE)
        reg = F.Registry(cfg)
        x, y, s, d, xy = F.vertex0(reg)
        rows = F.aug_pairs(reg, cross=True, cap=None, rng=random.Random(0))
        ci = [F.ci_row(reg, k) for k in range(len(cfg.steps))]
        for uni in (False, True):
            info, cert = F.solve_lp(reg, rows, ci, {x: 1}, d, [x, y, s], uni)
            self.assertEqual(info["status"], 0)
            self.assertGreaterEqual(cert["lb"], Fraction(1, 2) - Fraction(1, 10 ** 9))
            self.assertLessEqual(float(cert["lb"]), F.KLSS_W + 1e-9)
            self.assertLessEqual(float(cert["lb"]), info["value"] + 1e-7)


if __name__ == "__main__":
    unittest.main()
