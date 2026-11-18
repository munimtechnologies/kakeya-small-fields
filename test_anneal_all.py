# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""Tests for anneal_all.py. Each test checks a proved fact or an internal consistency
property (the fast incremental bookkeeping agrees with an independent recomputation)."""
import itertools
import math
import random
import unittest

import anneal_all as A


class TestAnnealAll(unittest.TestCase):

    def test_frame_maps_are_exactly_extremal(self):
        # Frame products: Lambda = k(q-1) exactly (each coordinate gives 1 - 1/q per slice).
        for q, k in [(3, 1), (3, 2), (3, 3), (5, 1), (5, 2), (7, 1)]:
            sp = A.Space(q, k)
            P = sp.frame_map()
            self.assertEqual(A.exact_compare(sp, P), 0)
            self.assertAlmostEqual(A.lam(sp, P), k * (q - 1), places=9)
            self.assertAlmostEqual(A.lambda_bruteforce(q, k, P), k * (q - 1), places=9)

    def test_fast_equals_bruteforce_on_random_maps(self):
        rng = random.Random(1)
        for q, k in [(3, 2), (3, 3), (5, 2)]:
            sp = A.Space(q, k)
            for _ in range(5):
                P = sp.random_map(rng)
                self.assertAlmostEqual(A.lam(sp, P), A.lambda_bruteforce(q, k, P), places=9)

    def test_incremental_bookkeeping(self):
        rng = random.Random(2)
        for q, k in [(3, 3), (5, 2)]:
            sp = A.Space(q, k)
            st = A.State(sp, sp.random_map(rng))
            for _ in range(3000):
                x = rng.randrange(sp.N)
                if rng.random() < 0.5:
                    y = rng.randrange(sp.N)
                    p = st.join_value(x, y, rng.randrange(q)) if y != x else rng.randrange(sp.N)
                else:
                    p = rng.randrange(sp.N)
                d = st.delta(x, p)
                before = st.S
                st.apply(x, p, d)
                self.assertAlmostEqual(st.S, before + d, places=9)
            self.assertAlmostEqual(st.S, A.score(sp, st.P), places=6)
            for t in range(q):
                c = A.slice_counts(sp, st.P, t)
                for y in range(sp.N):
                    self.assertEqual(st.c[t][y], c.get(y, 0))

    def test_join_move_joins_the_fibre(self):
        rng = random.Random(3)
        sp = A.Space(5, 2)
        st = A.State(sp, sp.random_map(rng))
        for _ in range(200):
            x, y, t = rng.randrange(sp.N), rng.randrange(sp.N), rng.randrange(5)
            p = st.join_value(x, y, t)
            st.apply(x, p, st.delta(x, p))
            self.assertEqual(st.v[t][x], st.v[t][y])

    def test_one_dimension_exhaustive_q3_q5(self):
        # C_q(1) is proved (README): every f : F_q -> F_q has Lambda <= q - 1, and x^2 attains it.
        for q in (3, 5):
            sp = A.Space(q, 1)
            best = -1
            for P in itertools.product(range(q), repeat=q):
                c = A.exact_compare(sp, list(P))
                self.assertLessEqual(c, 0)
                best = max(best, c)
            self.assertEqual(best, 0)

    def test_anneal_q3_k2_respects_proved_bound(self):
        # C_3(2) holds for all maps (branch and bound in the README), so no run may exceed 4.
        rng = random.Random(4)
        sp = A.Space(3, 2)
        for start in (sp.random_map(rng), [0] * sp.N, A.perturbed_frame(sp, rng, 0.3)):
            S, P = A.anneal(sp, rng, 20000, start)
            self.assertGreaterEqual(S, A.score(sp, start) - 1e-9)
            self.assertLessEqual(A.exact_compare(sp, P), 0)
            self.assertAlmostEqual(S / sp.N, A.lambda_bruteforce(3, 2, P), places=9)

    def test_quadratic_detector(self):
        sp = A.Space(3, 2)
        self.assertTrue(A.is_quadratic(sp, sp.frame_map()))
        # x1^2 x2 has degree 3: its third difference in directions e1, e1, e2 is 2 != 0.
        cubic = [sp.enc([(d[0] * d[0] * d[1]) % 3, 0]) for d in sp.digits]
        self.assertFalse(A.is_quadratic(sp, cubic))

    def test_run_case_smoke(self):
        r = A.run_case(3, 2, 0.0, 7, None, log=lambda s: None)
        self.assertEqual(r["target_k_q_minus_1"], 4)
        self.assertLessEqual(r["exact_compare_best_vs_target"], 0)
        self.assertAlmostEqual(r["best_lambda_fast"], r["best_lambda_bruteforce"], places=9)


if __name__ == "__main__":
    unittest.main()
