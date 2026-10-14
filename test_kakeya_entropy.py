import math
import random
import unittest
from itertools import product

from kakeya_entropy import (F3, PREVIOUS, Field, block_points, block_weights, central, class_size,
                            composition, directions, entropy, entropy_sum, entropy_sum_uniform,
                            exponent, hoeffding_log2, in_k3, is_kakeya, k3_base, k3_log2_bound,
                            k3_witness, kakeya_set, line_through, lower_base, min_max_weight,
                            new_base, q3_peak, q3_peak_brute, split, square_map, theorem_base,
                            theorem_log2, theta_star, vectors, weight)

FIELDS = (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27)


class FieldTests(unittest.TestCase):
    def test_tables_define_fields(self):
        for q in FIELDS:
            F = Field(q)
            rng = range(q)
            for a in rng:
                self.assertEqual(F.add[a][0], a)
                self.assertEqual(F.mul[a][1], a)
                self.assertEqual(F.add[a][F.neg[a]], 0)
                if a:
                    self.assertEqual(sum(1 for b in rng if F.mul[a][b] == 1), 1, (q, a))
                for b in rng:
                    self.assertEqual(F.add[a][b], F.add[b][a])
                    self.assertEqual(F.mul[a][b], F.mul[b][a])
            sample = random.Random(q).sample(list(product(rng, rng, rng)), min(q ** 3, 400))
            for a, b, c in sample:
                self.assertEqual(F.mul[F.mul[a][b]][c], F.mul[a][F.mul[b][c]])
                self.assertEqual(F.add[F.add[a][b]][c], F.add[a][F.add[b][c]])
                self.assertEqual(F.mul[a][F.add[b][c]], F.add[F.mul[a][b]][F.mul[a][c]])

    def test_characteristic(self):
        for q in FIELDS:
            F = Field(q)
            x = 0
            for _ in range(F.p):
                x = F.add[x][1]
            self.assertEqual(x, 0)


class SquareMapTests(unittest.TestCase):
    def test_fibres(self):
        for q in FIELDS:
            F = Field(q)
            for t in range(q):
                g = square_map(F, t)
                sizes = sorted(g.count(v) for v in set(g))
                if q % 2:
                    self.assertEqual(sizes, [1] + [2] * ((q - 1) // 2), (q, t))
                elif t == 0:
                    self.assertEqual(sizes, [1] * q)
                else:
                    self.assertEqual(sizes, [2] * (q // 2), (q, t))

    def test_each_pair_collides_once(self):
        for q in (3, 4, 5, 8, 9):
            F = Field(q)
            maps = [square_map(F, t) for t in range(q)]
            for x in range(q):
                for y in range(x + 1, q):
                    self.assertEqual(sum(1 for g in maps if g[x] == g[y]), 1)

    def test_uniform_value(self):
        for q in FIELDS:
            F = Field(q)
            self.assertAlmostEqual(entropy_sum(F, [1] * q), entropy_sum_uniform(q), places=9)
            self.assertAlmostEqual(entropy_sum_uniform(q) / q, exponent(q), places=12)
            self.assertAlmostEqual(2 ** exponent(q), new_base(q), places=12)

    def test_uniform_is_the_maximum(self):
        # Lemma 2: concavity plus translation invariance.
        rng = random.Random(20261014)
        for q in FIELDS:
            F = Field(q)
            top = entropy_sum_uniform(q)
            for _ in range(150):
                tau = [rng.random() ** rng.choice((1, 3, 8)) for _ in range(q)]
                self.assertLessEqual(entropy_sum(F, tau), top + 1e-9)
            for s in range(q):
                point = [0] * q
                point[s] = 1
                self.assertLessEqual(entropy_sum(F, point), top + 1e-9)

    def test_translation_invariance(self):
        rng = random.Random(7)
        for q in (3, 4, 5, 8, 9):
            F = Field(q)
            tau = [rng.random() for _ in range(q)]
            base = entropy_sum(F, tau)
            for b in range(q):
                moved = [0.0] * q
                for x in range(q):
                    moved[F.add[x][b]] = tau[x]
                self.assertAlmostEqual(entropy_sum(F, moved), base, places=9)

    def test_square_is_optimal_at_uniform(self):
        # For every f : F_q -> F_q, sum_t H(f + t x) at the uniform measure is at least
        # q log2 q - (q - 1): the method cannot do better than f = x^2.
        for q in (2, 3, 4, 5):
            F = Field(q)
            top = entropy_sum_uniform(q)
            for f in product(range(q), repeat=q):
                self.assertGreaterEqual(entropy_sum(F, [1] * q, list(f)), top - 1e-9)


class BoundTableTests(unittest.TestCase):
    def test_between_lower_and_previous(self):
        for q, (prev, _) in PREVIOUS.items():
            self.assertLess(lower_base(q), new_base(q) + 1e-12, q)
            self.assertLessEqual(new_base(q), prev + 1e-12, q)
            if q >= 4:
                self.assertLess(new_base(q), prev - 0.05, q)
        self.assertAlmostEqual(new_base(2), math.sqrt(2), places=12)
        self.assertAlmostEqual(new_base(3), PREVIOUS[3][0], places=12)

    def test_quoted_values(self):
        quoted = {3: 1.8899, 4: 2.3784, 5: 2.8717, 7: 3.8643, 8: 4.3620, 9: 4.8603, 16: 8.3542}
        for q, v in quoted.items():
            self.assertAlmostEqual(new_base(q), v, delta=1e-4)
        self.assertAlmostEqual(PREVIOUS[4][0], 2.8284, delta=1e-4)
        self.assertAlmostEqual(PREVIOUS[8][0], 6.3321, delta=1e-4)
        self.assertAlmostEqual(lower_base(4), 2.2857, delta=1e-4)
        self.assertAlmostEqual(lower_base(8), 4.2667, delta=1e-4)

    def test_closed_forms(self):
        for q in range(2, 200):
            self.assertLessEqual(new_base(q), q / 2 * (1 + 1 / q) + 1e-12)
            self.assertGreaterEqual(new_base(q), lower_base(q) - 1e-12)
            if q > 3:
                self.assertLess(new_base(q), q / 2 ** (2 / q))


class BlockTests(unittest.TestCase):
    def test_block_points_form_a_line(self):
        rng = random.Random(1)
        for q in (3, 4, 5, 8, 9):
            F = Field(q)
            for _ in range(40):
                u = tuple(rng.randrange(q) for _ in range(5))
                s, lam = rng.randrange(q), rng.randrange(1, q)
                pts = block_points(F, u, s, lam)
                a = pts[0]
                for t in range(q):
                    self.assertEqual(pts[t], tuple(F.add[x][F.mul[t][c]] for x, c in zip(a, u)))

    def test_block_lemma_exhaustive(self):
        # Lemma 1 + 2: sum_t log2 N(g_t(u)) <= m (q log2 q - (q - 1)) for every block u.
        for q, top_m in ((2, 6), (3, 5), (4, 4), (5, 3), (7, 2), (8, 2), (9, 2)):
            F = Field(q)
            for m in range(1, top_m + 1):
                bound = m * entropy_sum_uniform(q) + 1e-9
                for u in vectors(q, m):
                    self.assertLessEqual(sum(math.log2(w) for w in block_weights(F, u)), bound,
                                         (q, m, u))

    def test_class_size(self):
        self.assertEqual(class_size([2, 1, 0]), 3)
        self.assertEqual(class_size([1, 1, 1]), 6)
        self.assertEqual(sum(class_size([a, b, 4 - a - b]) for a in range(5)
                             for b in range(5 - a)), 81)
        for counts in ([3, 2, 1], [0, 5, 0], [4, 4]):
            self.assertLessEqual(math.log2(class_size(counts)),
                                 sum(counts) * entropy(counts) + 1e-9)

    def test_lines_and_weights(self):
        rng = random.Random(3)
        for q, m, r in ((3, 2, 3), (4, 2, 2), (5, 1, 3)):
            F = Field(q)
            for _ in range(30):
                d = tuple(rng.randrange(q) for _ in range(m * r))
                if not any(d):
                    continue
                best, shifts = min_max_weight(F, d, m)
                pts = line_through(F, d, m, shifts)
                self.assertEqual(len(set(pts)), q)
                self.assertEqual(max(weight(F, x, m) for x in pts), best)
                for t in range(q):
                    self.assertEqual(pts[t], tuple(F.add[a][F.mul[t][c]]
                                                   for a, c in zip(pts[0], d)))


class SmallKakeyaTests(unittest.TestCase):
    def check(self, q, m, r):
        F = Field(q)
        n = m * r
        theta = theta_star(F, m, r)
        K = kakeya_set(F, m, r, theta)
        self.assertTrue(is_kakeya(F, n, K), (q, m, r))
        for d in vectors(q, n):
            if any(d):
                best = min_max_weight(F, d, m)[0]
                # Lemma 3 (Hoeffding) for this direction, and the Theorem's threshold.
                self.assertLessEqual(math.log2(best), hoeffding_log2(F, d, m) + 1e-9)
                self.assertLessEqual(math.log2(best),
                                     r * m * exponent(q)
                                     + m * math.log2(q) * math.sqrt(r * math.log(q)) + 1e-9)
        return len(K)

    def test_q3(self):
        for m, r in ((1, 3), (2, 2), (1, 5), (3, 2), (2, 3)):
            self.check(3, m, r)

    def test_q4(self):
        for m, r in ((1, 3), (2, 2)):
            self.check(4, m, r)

    def test_q5(self):
        for m, r in ((1, 3), (2, 2)):
            self.check(5, m, r)

    def test_q8(self):
        self.check(8, 1, 2)


class TheoremNumberTests(unittest.TestCase):
    def test_theorem_bound_tends_to_new_base(self):
        for q in (3, 4, 5, 8):
            a = theorem_base(q, 10 ** 4, 10 ** 4)
            b = theorem_base(q, 10 ** 6, 10 ** 6)
            self.assertGreater(a, b)
            self.assertGreater(b, new_base(q))
            self.assertLess(b, new_base(q) * 1.01)
        self.assertLess(theorem_base(4, 10 ** 4, 10 ** 4), PREVIOUS[4][0])
        self.assertLess(theorem_base(8, 10 ** 4, 10 ** 4), PREVIOUS[8][0])

    def test_theorem_log2_monotone_terms(self):
        self.assertAlmostEqual(theorem_log2(3, 1, 1), math.log2(3) + exponent(3)
                               + math.log2(3) * math.sqrt(math.log(3)), places=9)


class Q3ExplicitTests(unittest.TestCase):
    def test_peak(self):
        for m in range(1, 16):
            self.assertEqual(q3_peak(m), q3_peak_brute(m), m)
            self.assertLessEqual(math.log2(q3_peak(m)), m * math.log2(27 / 4) + 1e-9)
            self.assertLessEqual(central(m), 2 ** m)

    def test_witness_lines_lie_in_k3(self):
        for m, r in ((1, 3), (1, 5), (2, 2), (2, 3), (3, 2), (4, 1), (5, 1)):
            n = m * r
            for d in vectors(3, n):
                if not any(d):
                    continue
                a = k3_witness(d, m)
                pts = [tuple((x + t * c) % 3 for x, c in zip(a, d)) for t in range(3)]
                self.assertEqual(len(set(pts)), 3)
                for x in pts:
                    self.assertTrue(in_k3(x, m), (m, r, d, x))

    def test_witness_on_random_long_directions(self):
        rng = random.Random(42)
        for m, r in ((6, 8), (9, 5), (12, 4), (30, 3)):
            for _ in range(60):
                d = tuple(rng.randrange(3) for _ in range(m * r))
                if not any(d):
                    continue
                a = k3_witness(d, m)
                for t in range(3):
                    self.assertTrue(in_k3(tuple((x + t * c) % 3 for x, c in zip(a, d)), m))

    def test_k3_is_kakeya_and_size_bound(self):
        for m, r in ((1, 3), (2, 2), (3, 2), (2, 3)):
            n = m * r
            K = [x for x in vectors(3, n) if in_k3(x, m)]
            self.assertTrue(is_kakeya(F3, n, K), (m, r))
            self.assertLessEqual(len(K) ** 3,
                                 (3 * m) ** (3 * r) * q3_peak(m) ** r * central(m) ** 2)
            self.assertLessEqual(math.log2(len(K)), k3_log2_bound(m, r) + 1e-9)

    def test_k3_numbers(self):
        self.assertLess(k3_base(300, 100), 2 ** 0.95)
        self.assertLess(k3_base(300, 100), 189 ** (1 / 30000) * 432 ** (1 / 9))
        self.assertLess(k3_base(3000, 3000), 2 ** 0.925)
        self.assertGreater(k3_base(3000, 3000), new_base(3))
        # The clean form (3m)^r * 4^(m/3) * (3 / 4^(1/3))^(rm) dominates the exact bound.
        for m, r in ((3, 2), (30, 10), (300, 100)):
            clean = r * math.log2(3 * m) + 2 * m / 3 + r * m * math.log2(3 / 4 ** (1 / 3))
            self.assertLessEqual(k3_log2_bound(m, r), clean + 1e-6)


class DirectionTests(unittest.TestCase):
    def test_direction_count(self):
        for q in (3, 4, 5):
            F = Field(q)
            for n in range(1, 4):
                self.assertEqual(sum(1 for _ in directions(F, n)), (q ** n - 1) // (q - 1))

    def test_split_and_composition(self):
        self.assertEqual(split((0, 1, 2, 2), 2), [(0, 1), (2, 2)])
        self.assertEqual(composition(F3, (2, 2, 0)), [1, 0, 2])


if __name__ == "__main__":
    unittest.main()
