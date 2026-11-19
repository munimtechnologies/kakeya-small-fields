# Tests for sticky_barrier.py (note a185). Stdlib only.
# MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
# Each test checks an exact identity used in the proofs of note a185, or recomputes a number
# that the note quotes, with an explicit tolerance.

import itertools
import json
import math
import os
import random
import unittest

import sticky_barrier as sb


class TestEntropyFunction(unittest.TestCase):
    def test_product_potential_value(self):
        # beta uniform: V = h2(1/3) = (1/3) log(27/4), the a182 rate
        v = sb.V((1 / 3.0, 1 / 3.0, 1 / 3.0))
        self.assertAlmostEqual(v, math.log(27.0 / 4.0) / 3.0, delta=1e-12)

    def test_kkt_weights_sum_to_one_and_satisfy_kkt(self):
        rng = random.Random(185)
        for _ in range(200):
            a = [rng.uniform(0.05, 1.0) for _ in range(3)]
            beta = [x / sum(a) for x in a]
            nu, w = sb.kkt_weights(beta)
            self.assertAlmostEqual(sum(w), 1.0, delta=1e-12)
            for b, x in zip(beta, w):
                self.assertTrue(0.0 < x < 1.0)
                self.assertAlmostEqual(b * math.log((1.0 - x) / x), nu, delta=1e-9)

    def test_kkt_maximiser_beats_random_weights(self):
        rng = random.Random(1851)
        for _ in range(100):
            a = [rng.uniform(0.05, 1.0) for _ in range(3)]
            beta = [x / sum(a) for x in a]
            best = sb.V(beta)
            for _ in range(50):
                z = [rng.random() for _ in range(3)]
                w = [x / sum(z) for x in z]
                self.assertLessEqual(sum(b * sb.h2(x) for b, x in zip(beta, w)), best + 1e-12)

    def test_V_is_convex(self):
        # V is a maximum of linear functions of beta
        rng = random.Random(1852)
        for _ in range(200):
            p = [rng.uniform(0.02, 1.0) for _ in range(3)]
            q = [rng.uniform(0.02, 1.0) for _ in range(3)]
            p = [x / sum(p) for x in p]
            q = [x / sum(q) for x in q]
            m = [(x + y) / 2.0 for x, y in zip(p, q)]
            self.assertLessEqual(sb.V(m), (sb.V(p) + sb.V(q)) / 2.0 + 1e-12)

    def test_boundary_value(self):
        self.assertAlmostEqual(sb.V((0.0, 0.5, 0.5)), math.log(2.0), delta=1e-15)
        self.assertAlmostEqual(sb.V((0.0, 0.0, 1.0)), math.log(2.0), delta=1e-15)


class TestTightConfigurations(unittest.TestCase):
    def test_affine_equal_children(self):
        rng = random.Random(82)
        for _ in range(200):
            v = tuple(rng.randint(1, 40) for _ in range(3))
            for s in range(3):
                p = sb.affine([v, v, v], s)
                self.assertEqual(p, tuple(v[t] if t == s else 3 * v[t] for t in range(3)))

    def test_affine_linear_gap(self):
        rng = random.Random(821)
        for _ in range(100):
            a = [rng.uniform(0.01, 1.0) for _ in range(3)]
            beta = [x / sum(a) for x in a]
            v = tuple(rng.uniform(1.0, 50.0) for _ in range(3))
            for s in range(3):
                gap = sb.linear_phi(beta, sb.affine([v, v, v], s)) - sb.linear_phi(beta, v)
                self.assertAlmostEqual(gap, (1.0 - beta[s]) * math.log(3.0), delta=1e-10)

    def test_triangle_children_rebuild_parent(self):
        rng = random.Random(157)
        for _ in range(300):
            p = tuple(rng.uniform(1.0, 1000.0) for _ in range(3))
            r = [rng.uniform(0.01, 0.99) for _ in range(3)]
            q = sb.triangle(sb.triangle_children(p, r))
            for a, b in zip(p, q):
                self.assertAlmostEqual(a, b, delta=1e-9 * a)

    def test_triangle_gaps_match_logs(self):
        rng = random.Random(1571)
        for _ in range(100):
            a = [rng.uniform(0.01, 1.0) for _ in range(3)]
            beta = [x / sum(a) for x in a]
            p = tuple(rng.uniform(1.0, 100.0) for _ in range(3))
            r = [rng.uniform(0.05, 0.95) for _ in range(3)]
            kids = sb.triangle_children(p, r)
            gaps = sb.triangle_gaps(beta, r)
            for x in range(3):
                self.assertAlmostEqual(sb.linear_phi(beta, p) - sb.linear_phi(beta, kids[x]),
                                       gaps[x], delta=1e-10)

    def test_gibbs_identity(self):
        # sum_x w_x gap_x = sum_t beta_t CE(w_t, r_t)
        rng = random.Random(1572)
        for _ in range(300):
            a = [rng.uniform(0.01, 1.0) for _ in range(3)]
            beta = [x / sum(a) for x in a]
            z = [rng.uniform(0.01, 1.0) for _ in range(3)]
            w = [x / sum(z) for x in z]
            r = [rng.uniform(0.02, 0.98) for _ in range(3)]
            lhs = sum(wx * g for wx, g in zip(w, sb.triangle_gaps(beta, r)))
            rhs = sum(beta[t] * sb.cross_entropy(w[t], r[t]) for t in range(3))
            self.assertAlmostEqual(lhs, rhs, delta=1e-12)

    def test_lemma157_lower_bound(self):
        # max_x gap_x >= V(beta) for every r
        rng = random.Random(1573)
        for _ in range(100):
            a = [rng.uniform(0.02, 1.0) for _ in range(3)]
            beta = [x / sum(a) for x in a]
            v = sb.V(beta)
            for _ in range(40):
                r = [rng.uniform(0.01, 0.99) for _ in range(3)]
                self.assertGreaterEqual(max(sb.triangle_gaps(beta, r)), v - 1e-12)

    def test_lemma157_saddle(self):
        # with r = w* (the KKT weights) all three gaps are equal to V(beta)
        rng = random.Random(1574)
        for _ in range(200):
            a = [rng.uniform(0.02, 1.0) for _ in range(3)]
            beta = [x / sum(a) for x in a]
            _, w = sb.kkt_weights(beta)
            v = sb.V(beta)
            for g in sb.triangle_gaps(beta, w):
                self.assertAlmostEqual(g, v, delta=1e-9)


class TestBarrierNumbers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.opt = sb.optimum()

    def test_optimum_values(self):
        o = self.opt
        self.assertAlmostEqual(o["c"], 0.24008, delta=1e-3)
        self.assertAlmostEqual(o["u"], 0.3807, delta=2e-3)
        self.assertGreater(o["lambda"], 1.93344)
        self.assertLess(o["lambda"], 1.93350)
        self.assertGreater(o["base"], 1.90499)
        self.assertLess(o["base"], 1.90504)
        b = sb.beta_c(o["c"])
        self.assertAlmostEqual(sb.affine_bound(b), sb.V(b), delta=1e-9)

    def test_mu_star_below_log2(self):
        self.assertLess(self.opt["mu"], math.log(2.0) - 0.04)
        self.assertLess(self.opt["base"], 2.0)

    def test_a183_close_to_optimum(self):
        a183 = min((2.0 - 0.24) * math.log(3.0), 2.48 * sb.h2(0.38) + 0.52 * sb.h2(0.24))
        self.assertLessEqual(a183, self.opt["lambda"] + 1e-12)
        self.assertLess(self.opt["lambda"] - a183, 5e-5)
        self.assertLessEqual(3.0 * sb.mu(sb.beta_c(0.24)), self.opt["lambda"] + 1e-12)

    def test_grid_never_beats_mu_star(self):
        # Proposition 82: min(A, V) <= mu_star on the whole simplex
        n = 60
        star = self.opt["mu"]
        for i in range(n + 1):
            for j in range(n + 1 - i):
                beta = (i / float(n), j / float(n), (n - i - j) / float(n))
                self.assertLessEqual(sb.mu(beta), star + 1e-9, msg=str(beta))

    def test_lemma156_affine_threshold_forces_V_below_log2(self):
        self.assertLess(sb.B0, 0.5)
        self.assertAlmostEqual(sb.affine_bound((sb.B0, 0.3, 1.0 - 0.3 - sb.B0)), math.log(2.0),
                               delta=1e-12)
        vertex = sb.V((sb.B0, sb.B0, 1.0 - 2.0 * sb.B0))
        self.assertAlmostEqual(vertex, 0.63788, delta=1e-4)
        n = 60
        for i in range(n + 1):
            for j in range(n + 1 - i):
                beta = (i / float(n), j / float(n), (n - i - j) / float(n))
                if max(beta) <= sb.B0:
                    self.assertLessEqual(sb.V(beta), vertex + 1e-9)
                    self.assertLess(sb.V(beta), math.log(2.0) - 0.05)

    def test_family_is_enough(self):
        # For fixed max weight b in [1/3, 1/2] the convex V peaks at the vertex (b, b, 1 - 2b).
        rng = random.Random(1575)
        for _ in range(300):
            b = rng.uniform(1 / 3.0 + 1e-6, 0.5 - 1e-6)
            x = rng.uniform(1.0 - 2.0 * b, b)
            beta = (b, x, 1.0 - b - x)
            if min(beta) <= 0.0 or max(beta) > b + 1e-15:
                continue
            self.assertLessEqual(sb.V(beta), sb.V((b, b, 1.0 - 2.0 * b)) + 1e-9)


class TestResultsFile(unittest.TestCase):
    PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "sticky_barrier.json")
    TOL = {"c_star": 1e-3, "u_star": 2e-3, "mu_star": 1e-5, "lambda_star": 3e-5,
           "base_star": 3e-5, "ln2": 1e-6, "affine_threshold_b0": 1e-6, "vertex_V_at_b0": 1e-4,
           "product_potential_V": 1e-6, "a183_lambda": 2e-6, "a183_base": 2e-6,
           "a183_family_mu_at_c_0_24": 1e-5}

    @unittest.skipUnless(os.path.exists(PATH), "results file not present next to the tests")
    def test_matches_code(self):
        with open(self.PATH) as fh:
            stored = json.load(fh)
        fresh = json.loads(json.dumps(sb.results()))
        for key, tol in self.TOL.items():
            self.assertAlmostEqual(stored[key], fresh[key], delta=tol, msg=key)
        self.assertEqual(stored["note"], "a185")
        self.assertEqual([b["label"] for b in stored["bases"]], [b["label"] for b in fresh["bases"]])
        for s, f in zip(stored["bases"], fresh["bases"]):
            self.assertAlmostEqual(s["value"], f["value"], delta=3e-5, msg=s["label"])


if __name__ == "__main__":
    unittest.main()
