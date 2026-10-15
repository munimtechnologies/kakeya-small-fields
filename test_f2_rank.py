"""Tests for f2_rank.py: Kakeya sets of rank r over F_2 (section 11 of the README).

By MV2 of Munim, Inc. Researched and written with AI agents working in his name.
Licence: Apache-2.0.
"""

import itertools
import math
import random
import unittest

import f2_rank as F

# Least size of a rank-r Kakeya set in F_2^n, keyed by (n, r). Proposition 3 gives the rows
# r = n - 1 (2^n - 1) and r = n - 2 (2^n - 3); r = n is the whole space; (4, 1) = 6 is the
# smallest difference basis of F_2^4.
EXACT = {(1, 1): 2, (2, 1): 3, (2, 2): 4, (3, 1): 5, (3, 2): 7, (3, 3): 8,
         (4, 1): 6, (4, 2): 13, (4, 3): 15, (4, 4): 16}


def floor_bits(n, r):
    """(2^r - 1) n, the lower bound of Theorem 7 for the sum of the 2^r slice entropies."""
    return (2 ** r - 1) * n


class SubspaceTests(unittest.TestCase):
    def test_subspace_counts(self):
        pairs = [(n, r) for n in range(1, 6) for r in range(1, min(n, 3) + 1)] + [(5, 4)]
        for n, r in pairs:
            self.assertEqual(len(F.subspaces(n, r)), F.gaussian_binomial_2(n, r), (n, r))
        self.assertEqual(F.gaussian_binomial_2(4, 2), 35)
        self.assertEqual(F.gaussian_binomial_2(5, 2), 155)

    def test_cosets_partition_the_space(self):
        for n, r in [(3, 1), (3, 2), (4, 2), (4, 3)]:
            full = 2 ** (2 ** n) - 1
            for sub in F.subspaces(n, r):
                cosets = F.coset_masks(n, sub)
                self.assertEqual(len(cosets), 2 ** (n - r))
                union = 0
                for c in cosets:
                    self.assertEqual(union & c, 0)
                    union |= c
                self.assertEqual(union, full)


class SmallValueTests(unittest.TestCase):
    def test_entropy_floor(self):
        self.assertEqual(F.entropy_floor(2, 2), 3)
        self.assertEqual(F.entropy_floor(3, 2), 5)
        self.assertEqual(F.entropy_floor(4, 2), 8)
        self.assertEqual(F.entropy_floor(4, 1), 4)
        self.assertEqual(F.entropy_floor(4, 3), 12)

    def test_exact_values_by_exhaustive_search(self):
        for (n, r), expected in sorted(EXACT.items()):
            size, example = F.min_kakeya(n, r)
            self.assertEqual(size, expected,
                             "K_%d(%d, 2): search found %d, example %s" % (r, n, size, example))
            self.assertTrue(F.kakeya_tester(n, r)(F.mask_of(example)))
            # Theorem 7: |K|^(2^r) >= 2^((2^r - 1) n).
            self.assertGreaterEqual(size ** (2 ** r), 2 ** floor_bits(n, r))
            self.assertGreaterEqual(size, F.entropy_floor(n, r))
            # KLSS Corollary 11 at q = 2: |K| < 2^(n (1 - 2^-r) + r + 1).
            self.assertLess(size, 2 ** (n * (1 - 2 ** (-r)) + r + 1))

    def test_proposition_3_rows_in_the_table(self):
        for (n, r), value in EXACT.items():
            if r == n - 1:
                self.assertEqual(value, 2 ** n - 1)
            if r == n - 2:
                self.assertEqual(value, 2 ** n - 3)

    def test_proposition_3_in_f2_5(self):
        n = 5
        full = 2 ** (2 ** n) - 1
        hyper = F.kakeya_tester(n, 4)
        self.assertTrue(hyper(full ^ 1))
        for a in range(1, 2 ** n):
            self.assertFalse(hyper(full ^ F.mask_of([0, a])), a)
        rank3 = F.kakeya_tester(n, 3)
        for c in itertools.combinations(range(1, 2 ** n), 2):
            self.assertTrue(rank3(full ^ F.mask_of((0,) + c)), c)
        for c in itertools.combinations(range(1, 2 ** n), 3):
            self.assertFalse(rank3(full ^ F.mask_of((0,) + c)), c)


class EntropyInequalityTests(unittest.TestCase):
    """Theorem 7: sum over t in F_2^r of H(A + t.d) >= (2^r - 1) n for every base point A."""

    def test_constant_base_point_gives_equality(self):
        for n, r in [(1, 1), (2, 1), (2, 2), (3, 2), (2, 3), (1, 4)]:
            table = [0] * 2 ** (n * r)
            self.assertAlmostEqual(F.entropy_sum(n, r, table), floor_bits(n, r), places=9)

    def test_every_deterministic_base_point_small_cases(self):
        for n, r in [(1, 1), (1, 2), (1, 3), (2, 1)]:
            shifts = F.shift_table(n, r)
            values = [F.entropy_sum(n, r, list(table), shifts)
                      for table in itertools.product(range(2 ** n), repeat=2 ** (n * r))]
            self.assertGreaterEqual(min(values), floor_bits(n, r) - 1e-9, (n, r))
            self.assertAlmostEqual(min(values), floor_bits(n, r), places=9)

    def test_local_minima_never_go_below(self):
        # (n, r) = (2, 2) is the block question for q = r = 2, k = 2: a map P on 2 x 2 matrices
        # with sum of entropies below 6 (equivalently S(P) > 160) would beat 2^(3/4).
        rng = random.Random(20261015)
        for n, r, restarts in [(2, 2, 100), (1, 4, 20), (2, 3, 4), (3, 2, 4)]:
            shifts = F.shift_table(n, r)
            for _ in range(restarts):
                value, table = F.local_minimum(n, r, rng, shifts)
                self.assertGreaterEqual(value, floor_bits(n, r) - 1e-9, (n, r, table))

    def test_random_base_points(self):
        rng = random.Random(7)
        for n, r in [(2, 2), (3, 2), (2, 3), (1, 4)]:
            shifts = F.shift_table(n, r)
            for _ in range(10):
                laws = []
                for _ in range(2 ** (n * r)):
                    support = rng.sample(range(2 ** n), rng.randint(1, min(3, 2 ** n)))
                    weights = [rng.random() + 0.01 for _ in support]
                    total = sum(weights)
                    laws.append({a: w / total for a, w in zip(support, weights)})
                value = F.entropy_sum_random(n, r, laws, shifts)
                self.assertGreaterEqual(value, floor_bits(n, r) - 1e-9, (n, r))

    def test_random_and_deterministic_versions_agree(self):
        rng = random.Random(3)
        n, r = 2, 2
        table = [rng.randrange(4) for _ in range(16)]
        self.assertAlmostEqual(F.entropy_sum(n, r, table),
                               F.entropy_sum_random(n, r, [{a: 1.0} for a in table]), places=9)

    def test_witnesses_of_smallest_sets(self):
        for n, r in [(3, 2), (4, 1), (4, 2), (4, 3)]:
            size, example = F.min_kakeya(n, r)
            table = F.witness_table(n, r, example)
            shifts = F.shift_table(n, r)
            members = set(example)
            for i, a in enumerate(table):
                for t in range(2 ** r):
                    self.assertIn(a ^ shifts[i][t], members)
            value = F.entropy_sum(n, r, table, shifts)
            self.assertLessEqual(value, 2 ** r * math.log2(size) + 1e-9)
            self.assertGreaterEqual(value, floor_bits(n, r) - 1e-9)


class NumberTests(unittest.TestCase):
    def test_quoted_numbers(self):
        for r, value in [(1, 1.4142), (2, 1.6818), (3, 1.8340), (4, 1.9152)]:
            self.assertAlmostEqual(F.new_base(r), value, places=4)
        for r, value in [(1, 1.3333), (2, 1.6), (3, 1.7778), (4, 1.8824)]:
            self.assertAlmostEqual(F.klss_lower_base(r), value, places=4)

    def test_new_base_is_klss_theorem_10_and_beats_theorem_1(self):
        for r in range(1, 12):
            self.assertAlmostEqual(F.new_base(r), 2 ** (1 - 2.0 ** (-r)), places=12)
            self.assertGreater(F.new_base(r), F.klss_lower_base(r))

    def test_counting_bound_for_rank_2(self):
        # Counting the triples a, a + w_1, a + w_2 only gives base 2^(2/3).
        self.assertAlmostEqual(2 ** (2 / 3), 1.5874, places=4)
        self.assertLess(2 ** (2 / 3), F.klss_lower_base(2))

    def test_general_q_pairing_is_weaker(self):
        # Over F_q the pairing gives base q^(1 - (1 - 1/q)^r), never better than KLSS Theorem 1
        # when q >= 3, and better than it when q = 2.
        for q in [3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27, 32, 49, 64]:
            for r in range(1, 9):
                pairing = q ** (1 - (1 - 1 / q) ** r)
                self.assertLessEqual(pairing, F.klss_lower_base(r, q) + 1e-12, (q, r))
                self.assertGreaterEqual((q - 1) ** (r - 1) * math.log(q), 1.0)
        for r in range(1, 12):
            self.assertGreater(2 ** (1 - 0.5 ** r), F.klss_lower_base(r, 2))

    def test_table_rows(self):
        rows = F.table_rows()
        self.assertEqual([row[0] for row in rows], [1, 2, 3, 4, 5, 6])


if __name__ == "__main__":
    unittest.main()
