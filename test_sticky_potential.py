# Tests for sticky_potential.py (note a183, Theorem 72 and Lemma 153). Stdlib only.
# MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
# Every assertion is a hand computation or a consequence of a proved statement:
# Lemma 153 (the potential inequality holds for ANY positive child vectors), Theorem 72,
# Proposition 78 (composition) and Lemma 151 (f(2) = 4).

import itertools
import json
import math
import os
import random
import unittest

import sticky_potential as sp


class TestRates(unittest.TestCase):
    def test_hand_values(self):
        self.assertAlmostEqual(sp.affine_rate(0.24), 1.933557628, delta=1e-8)
        self.assertAlmostEqual(sp.triangle_rate(0.24, 0.38), 1.933440596, delta=1e-8)
        self.assertAlmostEqual(sp.rate(), 1.933440596, delta=1e-8)
        self.assertAlmostEqual(sp.h2(0.38), 0.664064127, delta=1e-8)
        self.assertAlmostEqual(sp.h2(0.24), 0.551079928, delta=1e-8)

    def test_beats_entropy_bound_and_klss(self):
        self.assertGreater(sp.rate(), math.log(27.0 / 4.0) + 0.0238)
        self.assertGreater(sp.base(), 1.90499)
        self.assertGreater(sp.base(), sp.BASE_KLSS + 0.015)

    def test_reference_bases(self):
        self.assertAlmostEqual(sp.BASE_KLSS, (27.0 / 4.0) ** (1.0 / 3.0), delta=1e-12)
        self.assertAlmostEqual(sp.BASE_KLSS, 1.889882, delta=1e-6)
        self.assertAlmostEqual(sp.BASE_ALL_KAKEYA_LOWER_A180, 1.82074, delta=1e-5)

    def test_c_zero_is_the_entropy_bound(self):
        # c = 0, u = 1/3 recovers the a182 rate log(27/4)
        self.assertAlmostEqual(sp.triangle_rate(0.0, 1.0 / 3.0), math.log(27.0 / 4.0), delta=1e-12)


class TestPotential(unittest.TestCase):
    def test_leaf_is_zero(self):
        self.assertEqual(sp.phi(sp.LEAF), 0.0)

    def test_phi_at_most_three_log_max(self):
        rng = random.Random(72)
        for _ in range(500):
            v = tuple(math.exp(rng.uniform(-4, 4)) for _ in range(3))
            self.assertLessEqual(sp.phi(v), 3 * math.log(max(v)) + 1e-12)

    def test_phi_monotone(self):
        rng = random.Random(153)
        for _ in range(500):
            v = [math.exp(rng.uniform(-4, 4)) for _ in range(3)]
            t = rng.randrange(3)
            w = list(v)
            w[t] *= math.exp(rng.uniform(0, 2))
            self.assertGreaterEqual(sp.phi(w), sp.phi(v) - 1e-12)

    def test_affine_on_leaves_is_tight(self):
        leaf3 = (sp.LEAF,) * 3
        self.assertAlmostEqual(sp.node_gain(leaf3), sp.affine_rate(sp.C_STAR), delta=1e-12)

    def test_near_tight_triangle(self):
        # children built so that every Gibbs step in the proof is an equality (r_t = w_iso(t))
        ch = ((0.38, 0.62, 2.28), (0.62, 0.38, 2.28), (0.62, 0.62, 0.72))
        p = sp.triangle(ch)
        for a, b in zip(p, (1.0, 1.0, 3.0)):
            self.assertAlmostEqual(a, b, delta=1e-12)
        gains = [sp.phi(p) - sp.phi(x) for x in ch]
        avg = 0.38 * gains[0] + 0.38 * gains[1] + 0.24 * gains[2]
        self.assertAlmostEqual(avg, sp.triangle_rate(sp.C_STAR, sp.U_STAR), delta=1e-9)
        self.assertGreaterEqual(max(gains), sp.rate() - 1e-12)
        self.assertLessEqual(max(gains), sp.rate() + 0.003)

    def test_obstruction_example(self):
        # the shape that defeats the potential min(A, G) (prereg-sticky-front.md, Remark)
        ch = ((1, 2, 0.5), (2, 1, 0.5), (2, 2, 0.25))
        self.assertGreaterEqual(sp.node_gain(ch), sp.rate() - 1e-12)

    def test_lemma153_on_a_grid(self):
        vals = [0.25, 0.5, 1.0, 1.5, 2.0, 3.0, 8.0]
        vecs = [(1.0, 1.0, 1.0), (0.5, 1.0, 1.0), (1.0, 3.0, 3.0), (3.0, 3.0, 1.0),
                (0.25, 2.0, 2.0), (2.0, 0.5, 1.5), (8.0, 1.0, 0.25), (1.5, 3.0, 0.5)]
        vecs += [(a, b, 1.0) for a in vals for b in vals][::5]
        for ch in itertools.product(vecs, repeat=3):
            self.assertGreaterEqual(sp.node_gain(ch), sp.rate() - 1e-9)

    def test_lemma153_random(self):
        rng = random.Random(183)
        for _ in range(3000):
            ch = tuple(tuple(math.exp(rng.uniform(-3, 3)) for _ in range(3)) for _ in range(3))
            self.assertGreaterEqual(sp.node_gain(ch), sp.rate() - 1e-9)


class TestFronts(unittest.TestCase):
    def test_fast_pareto_equals_simple(self):
        rng = random.Random(78)
        for _ in range(40):
            vecs = [tuple(rng.randint(1, 12) for _ in range(3)) for _ in range(rng.randint(1, 60))]
            self.assertEqual(sp.pareto_min_fast(vecs), sp.pareto_min(vecs))

    @classmethod
    def setUpClass(cls):
        cls.fr = sp.fronts(3)

    def test_height_1(self):
        self.assertEqual(self.fr[1], [(1, 3, 3), (2, 2, 2), (3, 1, 3), (3, 3, 1)])

    def test_lemma151(self):
        self.assertEqual(min(max(v) for v in self.fr[2]), 4)

    def test_theorem72_on_exact_fronts(self):
        lam = sp.rate()
        for h in (1, 2, 3):
            for v in self.fr[h]:
                self.assertGreaterEqual(sp.phi(v), h * lam - 1e-9)
                self.assertGreaterEqual(max(v), math.exp(h * lam / 3.0) - 1e-9)

    def test_proposition78_composition(self):
        # coordinatewise products of achievable vectors (any slice relabelling) are achievable
        for (h1, h2) in ((1, 1), (1, 2)):
            target = self.fr[h1 + h2]
            for v in self.fr[h1]:
                for w in self.fr[h2]:
                    for perm in itertools.permutations(range(3)):
                        vw = tuple(v[t] * w[perm[t]] for t in range(3))
                        self.assertTrue(any(sp.leq(f, vw) for f in target), (v, w, perm))

    def test_fronts_symmetric(self):
        for fr in self.fr[1:]:
            s = set(fr)
            for v in fr:
                for perm in itertools.permutations(range(3)):
                    self.assertIn(tuple(v[perm[t]] for t in range(3)), s)


class TestResultsFile(unittest.TestCase):
    PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results",
                        "sticky_potential_bound.json")

    @unittest.skipUnless(os.path.exists(PATH), "results file not present next to the tests")
    def test_matches_code(self):
        with open(self.PATH) as fh:
            stored = json.load(fh)
        fresh = sp.results()
        for key in ("c", "u", "affine_rate", "triangle_rate", "lambda", "log_27_over_4",
                    "gain_over_entropy_bound", "base_new_sticky_lower"):
            self.assertAlmostEqual(stored[key], fresh[key], delta=1e-6, msg=key)
        self.assertEqual([b["label"] for b in stored["bases"]], [b["label"] for b in fresh["bases"]])
        for a, b in zip(stored["bases"], fresh["bases"]):
            self.assertAlmostEqual(a["value"], b["value"], delta=1e-6, msg=a["label"])


if __name__ == "__main__":
    unittest.main()
