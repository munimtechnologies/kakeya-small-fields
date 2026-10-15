"""Tests for exact_h2.py (README section 9). Pure Python; the full F_3^2 search takes seconds to a
minute. By MV2 of Munim, Inc.; researched and written with AI agents working in MV2's name.
Code Apache-2.0."""
import math
import random
import unittest

from exact_h2 import brute_force, digits, score, search, squares, tables, threshold


class Basics(unittest.TestCase):
    def test_tables_match_coordinates(self):
        for q, k in [(2, 3), (3, 2), (5, 2)]:
            add, mul = tables(q, k)
            for u in range(q ** k):
                for v in range(q ** k):
                    want = [(a + b) % q for a, b in zip(digits(q, k, u), digits(q, k, v))]
                    self.assertEqual(digits(q, k, add[u][v]), want)
                for t in range(q):
                    self.assertEqual(digits(q, k, mul[t][u]), [t * a % q for a in digits(q, k, u)])

    def test_squares_reach_the_threshold(self):
        # each slice of x^2 + t x on F_3^2 has fibres 4, 2, 2, 1: 8 + 2 + 2 = 12, three slices = 36
        self.assertAlmostEqual(score(3, 2, squares(3, 2)), 36.0, places=9)
        self.assertEqual(threshold(3, 2), 36)
        for q, k in [(3, 1), (5, 1), (3, 3), (5, 2)]:
            self.assertAlmostEqual(score(q, k, squares(q, k)), threshold(q, k), places=9)

    def test_quoted_ceilings(self):
        # Corollary 2: S(P) <= q^(k+1) * k * log2((2q - 1)/q)
        self.assertAlmostEqual(27 * 2 * math.log2(5 / 3), 39.80, places=2)
        self.assertAlmostEqual(81 * 3 * math.log2(5 / 3), 179.08, places=2)
        self.assertEqual(threshold(3, 3), 162)
        self.assertEqual(9 ** 8, 43046721)

    def test_translation_does_not_change_the_score(self):
        rng = random.Random(5)
        add, _ = tables(3, 2)
        for _ in range(20):
            P = [rng.randrange(9) for _ in range(9)]
            c = rng.randrange(9)
            self.assertAlmostEqual(score(3, 2, P), score(3, 2, [add[p][c] for p in P]), places=9)


class AgainstBruteForce(unittest.TestCase):
    def check(self, q, k, fixed=None):
        best, count = brute_force(q, k, fixed)
        everything = search(q, k, -1.0, fixed)
        self.assertAlmostEqual(everything["max_score"], best, places=9)
        self.assertEqual(everything["maps_at_max"], count)
        self.assertEqual(everything["maps_at_or_above_floor"],
                         (q ** k) ** (q ** k - 1 - len(fixed or {})))
        at_max = search(q, k, best, fixed)
        self.assertAlmostEqual(at_max["max_score"], best, places=9)
        self.assertEqual(at_max["maps_at_max"], count)
        self.assertEqual(at_max["maps_at_or_above_floor"], count)
        self.assertAlmostEqual(score(q, k, at_max["example"]), best, places=9)
        above = search(q, k, best + 0.25, fixed)
        self.assertIsNone(above["max_score"])
        self.assertEqual(above["maps_at_or_above_floor"], 0)
        return best

    def test_small_complete_cases(self):
        # k = 1: the maximum is (q - 1) q (README section 4); q = 2: h_k = k/2, so S = k 2^k
        self.assertAlmostEqual(self.check(2, 1), 2.0, places=9)
        self.assertAlmostEqual(self.check(3, 1), 6.0, places=9)
        self.assertAlmostEqual(self.check(5, 1), 20.0, places=9)
        self.assertAlmostEqual(self.check(2, 2), 8.0, places=9)

    def test_partial_cases_on_F3_squared(self):
        sq = squares(3, 2)
        self.check(3, 2, {x: sq[x] for x in range(1, 5)})
        self.check(3, 2, {x: sq[x] for x in range(1, 6)})
        rng = random.Random(11)
        for _ in range(3):
            self.check(3, 2, {x: rng.randrange(9) for x in range(1, 6)})
        self.check(3, 2, {x: rng.randrange(9) for x in range(1, 5)})


class FullSearches(unittest.TestCase):
    def test_q2_k3_matches_theory(self):
        # H(Y_0) + H(Y_1) >= H(X) = 3 gives h_3 >= 3/2, so the maximum is 3 * 2^3 = 24
        result = search(2, 3, threshold(2, 3))
        self.assertAlmostEqual(result["max_score"], 24.0, places=9)
        self.assertAlmostEqual(score(2, 3, result["example"]), 24.0, places=9)

    def test_every_map_on_F3_squared(self):
        """README section 9: no map on F_3^2 beats the coordinatewise squares (S = 36)."""
        result = search(3, 2, threshold(3, 2))
        best = result["max_score"]
        P = result["example"]
        shown = [[digits(3, 2, x), digits(3, 2, P[x])] for x in range(9)]
        self.assertAlmostEqual(best, 36.0, places=9,
                               msg=f"max S = {best!r}, map {shown}, nodes {result['nodes']}")
        self.assertAlmostEqual(score(3, 2, P), best, places=9)
        self.assertGreaterEqual(result["maps_at_max"], 1)


if __name__ == "__main__":
    unittest.main()
