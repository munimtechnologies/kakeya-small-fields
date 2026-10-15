import math
import random
import unittest

from kakeya_entropy import (Field, exponent, improvement_threshold, square_witness, vectors,
                            witness_score)
from search_h2 import anneal, as_dict, score_codes, tables

try:
    import numpy  # noqa: F401
    HAVE_NUMPY = True
except ImportError:
    HAVE_NUMPY = False


class ScoreTests(unittest.TestCase):
    def test_codes_match_dict_score(self):
        rng = random.Random(2)
        for q, k in ((3, 2), (4, 2), (2, 3), (5, 1)):
            F, vs, index, add, tx = tables(q, k)
            for _ in range(10):
                codes = [rng.randrange(q ** k) for _ in vs]
                self.assertAlmostEqual(score_codes(q, k, add, tx, codes),
                                       witness_score(F, k, as_dict(vs, codes)), places=9)
            square = [index[v] for v in square_witness(F, k).values()]
            self.assertAlmostEqual(score_codes(q, k, add, tx, square),
                                   improvement_threshold(q, k), places=9)

    def test_anneal_smoke(self):
        out = anneal(3, 2, 1, seed=3)
        self.assertGreaterEqual(out["max_score"], 36 - 1e-9)
        self.assertAlmostEqual(out["max_score"], out["score_rechecked"], places=9)
        out = anneal(2, 3, 1, seed=4)
        self.assertAlmostEqual(out["max_score"], 24.0, places=9)  # h_3(2) = 3/2 exactly


@unittest.skipUnless(HAVE_NUMPY, "numpy is needed for the exhaustive search")
class ExhaustiveTests(unittest.TestCase):
    def test_known_values(self):
        from search_h2 import exhaustive
        # h_1 = c_q, so the best one-dimensional score is (q - 1) q; h_2 = 1 for q = 2.
        for q, k, inner in ((3, 1, 1), (5, 1, 2), (2, 2, 2)):
            out = exhaustive(q, k, inner)
            self.assertAlmostEqual(out["max_score"], improvement_threshold(q, k), places=9)
            self.assertEqual(out["maps_checked"], (q ** k) ** (q ** k - 1))
            self.assertEqual(out["maps_above_threshold"], 0)
            self.assertAlmostEqual(out["h_min"], k * exponent(q), places=9)
            for ex in out["examples"]:
                self.assertAlmostEqual(ex["score_rechecked"], out["max_score"], places=9)

    def test_matches_brute_force(self):
        from search_h2 import exhaustive
        q, k = 3, 1
        F = Field(q)
        xs = vectors(q, k)
        best = max(witness_score(F, k, {xs[0]: xs[0], xs[1]: a, xs[2]: b})
                   for a in xs for b in xs)
        self.assertAlmostEqual(exhaustive(q, k, 1)["max_score"], best, places=9)
        self.assertAlmostEqual(best, 6.0, places=9)
        self.assertTrue(math.isclose(best, (q - 1) * q))


if __name__ == "__main__":
    unittest.main()
