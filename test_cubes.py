"""Tests for cubes.py: translates of cubes in finite groups (section 12 of the README).

By MV2 of Munim, Inc. Researched and written with AI agents working in his name.
Licence: Apache-2.0.
"""

import itertools
import math
import random
import unittest

import cubes as C


def floor_bits(order, m):
    """(m - 1) log2 N, the lower bound of Lemma 6 for an m-point pattern."""
    return (m - 1) * math.log2(order)


class GroupTests(unittest.TestCase):
    def test_group_axioms(self):
        for g in C.small_groups():
            n, mul = g.order, g.mul
            for a in range(n):
                self.assertEqual(mul[0][a], a, g.name)
                self.assertEqual(mul[a][0], a, g.name)
                self.assertEqual(mul[a][g.inv[a]], 0, g.name)
                self.assertEqual(sorted(mul[a]), list(range(n)), g.name)
            for a, b, c in itertools.product(range(n), repeat=3):
                if n <= 12 or (a + b + c) % 7 == 0:
                    self.assertEqual(mul[mul[a][b]][c], mul[a][mul[b][c]], g.name)

    def test_orders_and_commutativity(self):
        names = {g.name: g for g in C.small_groups()}
        self.assertEqual(names["S_3"].order, 6)
        self.assertEqual(names["S_3 x Z_2"].order, 12)
        self.assertEqual(names["Z_2 x Z_2 x Z_2 x Z_2"].order, 16)
        s3 = names["S_3"]
        self.assertTrue(any(s3.mul[a][b] != s3.mul[b][a] for a in range(6) for b in range(6)))
        for name in ["Z_16", "Z_4 x Z_4", "Z_2 x Z_8"]:
            g = names[name]
            self.assertTrue(all(g.mul[a][b] == g.mul[b][a] for a in range(16) for b in range(16)))

    def test_patterns(self):
        self.assertEqual(C.cube(2), [(0, 0), (0, 1), (1, 0), (1, 1)])
        self.assertEqual(C.simplex(2), [(0, 0), (1, 0), (0, 1)])
        self.assertEqual(len(C.cube(4)), 16)
        self.assertEqual(len(set(C.simplex(5))), 6)

    def test_words_are_ordered_products(self):
        s3 = C.symmetric3()
        for d in itertools.product(range(6), repeat=2):
            self.assertEqual(C.word(s3, d, (1, 1)), s3.mul[d[0]][d[1]])
            self.assertEqual(C.word(s3, d, (0, 1)), d[1])
            self.assertEqual(C.word(s3, d, (0, 0)), 0)


class LemmaSixTests(unittest.TestCase):
    """Lemma 6: sum over t in T of H(A w_t(d)) >= (|T| - 1) log2 N for every T in {0,1}^r."""

    def test_every_base_point_and_every_pattern_small_cases(self):
        # All deterministic A : G^r -> G (random A are mixtures, and entropy is concave).
        for group, r in [(C.cyclic(3), 2), (C.cyclic(2), 3), (C.cyclic(2), 2),
                         (C.cyclic(4), 1), (C.cyclic(5), 1), (C.symmetric3(), 1),
                         (C.product(C.cyclic(2), C.cyclic(2)), 1)]:
            minima = C.exhaustive_minima(group, r)
            self.assertEqual(len(minima), 2 ** (2 ** r) - 1)
            for pattern, value in minima.items():
                target = floor_bits(group.order, len(pattern))
                self.assertGreaterEqual(value, target - 1e-9, (group.name, pattern))
                # A = w_s(d)^(-1) attains the bound, so the minimum is exactly (|T| - 1) log2 N.
                self.assertAlmostEqual(value, target, places=9, msg=(group.name, pattern))

    def test_equality_case(self):
        for group, r in [(C.cyclic(5), 2), (C.symmetric3(), 2), (C.cyclic(3), 3),
                         (C.product(C.cyclic(2), C.cyclic(4)), 2)]:
            for pattern in [C.cube(r), C.simplex(r), C.cube(r)[1:]]:
                words = C.word_table(group, r, pattern)
                for s in pattern:
                    table = C.inverse_base_point(group, r, s)
                    h = C.slice_entropies(group, table, words)
                    for t, value in zip(pattern, h):
                        expected = 0.0 if t == s else math.log2(group.order)
                        self.assertAlmostEqual(value, expected, places=9,
                                               msg=(group.name, pattern, s, t))

    def test_local_minima_never_go_below(self):
        rng = random.Random(20261015)
        cases = [(C.cyclic(4), 2, 12), (C.cyclic(5), 2, 8), (C.symmetric3(), 2, 8),
                 (C.cyclic(3), 3, 3), (C.product(C.cyclic(2), C.cyclic(2)), 2, 4)]
        for group, r, restarts in cases:
            for pattern in [C.cube(r), C.cube(r)[1:], C.simplex(r)]:
                words = C.word_table(group, r, pattern)
                for _ in range(restarts):
                    value, table = C.local_minimum(group, words, rng)
                    self.assertGreaterEqual(value, floor_bits(group.order, len(pattern)) - 1e-9,
                                            (group.name, pattern, table))

    def test_random_tables(self):
        rng = random.Random(5)
        for group, r in [(C.cyclic(6), 2), (C.symmetric3(), 2), (C.cyclic(7), 2),
                         (C.cyclic(3), 3)]:
            pattern = C.cube(r)
            words = C.word_table(group, r, pattern)
            for _ in range(30):
                table = [rng.randrange(group.order) for _ in range(len(words))]
                self.assertGreaterEqual(C.entropy_sum(group, table, words),
                                        floor_bits(group.order, len(pattern)) - 1e-9)


class UniversalSetTests(unittest.TestCase):
    def test_tester_agrees_with_definition(self):
        rng = random.Random(11)
        for group in C.small_groups():
            if group.order > 9:
                continue
            for r, pattern in [(2, C.cube(2)), (2, C.simplex(2)), (1, C.cube(1))]:
                tester = C.universal_tester(group, r, pattern)
                for _ in range(25):
                    size = rng.randint(1, group.order)
                    points = rng.sample(range(group.order), size)
                    self.assertEqual(tester(points),
                                     C.is_universal_naive(group, r, pattern, points),
                                     (group.name, pattern, sorted(points)))

    def test_theorem_8_for_2_cubes_by_exhaustive_search(self):
        # No set below N^(3/4) contains a left translate of every {e, x, y, x y}.
        for group in C.small_groups():
            size, example = C.min_universal(group, 2, C.cube(2))
            self.assertTrue(C.is_universal_naive(group, 2, C.cube(2), example), group.name)
            self.assertGreaterEqual(size ** 4, group.order ** 3, (group.name, size, example))
            self.assertGreaterEqual(size, C.size_floor(group.order, 4))
            self.assertLessEqual(size, group.order)

    def test_theorem_8_for_3_point_sets(self):
        for group in C.small_groups():
            if group.order > 12:
                continue
            size, example = C.min_universal(group, 2, C.simplex(2))
            self.assertTrue(C.is_universal_naive(group, 2, C.simplex(2), example), group.name)
            self.assertGreaterEqual(size ** 3, group.order ** 2, (group.name, size, example))

    def test_f2_values_agree_with_section_11(self):
        # In F_2^n, 2-cube-universal sets are exactly the rank-2 Kakeya sets (n >= 2), and
        # 1-cube-universal sets are the rank-1 Kakeya sets. Section 11 gives K_2(2, 2) = 4,
        # K_2(3, 2) = 7, K_2(4, 2) = 13 and K_1(4, 2) = 6.
        c2 = C.cyclic(2)
        f2 = {2: C.product(c2, c2), 3: C.product(c2, c2, c2), 4: C.product(c2, c2, c2, c2)}
        self.assertEqual(C.min_universal(f2[2], 2, C.cube(2))[0], 4)
        self.assertEqual(C.min_universal(f2[3], 2, C.cube(2))[0], 7)
        self.assertEqual(C.min_universal(f2[4], 2, C.cube(2))[0], 13)
        self.assertEqual(C.min_universal(f2[4], 1, C.cube(1))[0], 6)

    def test_witnesses_put_every_point_in_k(self):
        # The proof of Theorem 8: with A(d) a witness, every Y_t lies in K, so the sum of the
        # slice entropies is at most |T| log2 |K|, and Lemma 6 bounds it below.
        for group in [C.cyclic(7), C.symmetric3(), C.product(C.cyclic(2), C.cyclic(4))]:
            r, pattern = 2, C.cube(2)
            size, example = C.min_universal(group, r, pattern)
            members = set(example)
            words = C.word_table(group, r, pattern)
            table = []
            for row in words:
                a = next(a for a in range(group.order)
                         if all(group.mul[a][w] in members for w in row))
                table.append(a)
                for w in row:
                    self.assertIn(group.mul[a][w], members)
            value = C.entropy_sum(group, table, words)
            self.assertLessEqual(value, len(pattern) * math.log2(size) + 1e-9)
            self.assertGreaterEqual(value, floor_bits(group.order, len(pattern)) - 1e-9)


class NumberTests(unittest.TestCase):
    def test_quoted_exponents(self):
        rows = {r: (count, exact) for r, count, exact in C.table_rows()}
        self.assertAlmostEqual(rows[1][0], 0.5, places=12)
        self.assertAlmostEqual(rows[1][1], 0.5, places=12)
        self.assertAlmostEqual(rows[2][0], 0.6667, places=4)
        self.assertAlmostEqual(rows[2][1], 0.75, places=12)
        self.assertAlmostEqual(rows[3][0], 0.75, places=12)
        self.assertAlmostEqual(rows[3][1], 0.875, places=12)
        self.assertAlmostEqual(rows[4][0], 0.8, places=12)
        self.assertAlmostEqual(rows[4][1], 0.9375, places=12)

    def test_entropy_beats_counting_for_r_at_least_2(self):
        for r in range(2, 20):
            self.assertGreater(C.lower_exponent(2 ** r), C.counting_exponent(r))
        self.assertAlmostEqual(C.lower_exponent(2), C.counting_exponent(1), places=12)

    def test_size_floor(self):
        self.assertEqual(C.size_floor(16, 4), 8)
        self.assertEqual(C.size_floor(9, 4), 6)
        self.assertEqual(C.size_floor(6, 4), 4)
        self.assertEqual(C.size_floor(16, 2), 4)
        for n in range(2, 200):
            for m in range(1, 9):
                k = C.size_floor(n, m)
                self.assertGreaterEqual(k ** m, n ** (m - 1))
                self.assertLess((k - 1) ** m, n ** (m - 1))

    def test_random_upper_bound_is_above_the_lower_bound(self):
        for n in [10, 100, 10 ** 4, 10 ** 6, 2 ** 40]:
            for m in range(1, 17):
                upper = C.random_upper(n, m)
                self.assertGreaterEqual(upper, n ** (1 - 1 / m) - 1e-6)
                self.assertLessEqual(upper, n)
        # The exponents meet: log(upper) / log(N) -> 1 - 1/m.
        for m in [2, 4, 8]:
            ratio = math.log(C.random_upper(2.0 ** 1000, m)) / math.log(2.0 ** 1000)
            self.assertLess(abs(ratio - (1 - 1 / m)), 0.01)


if __name__ == "__main__":
    unittest.main()
