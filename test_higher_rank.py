"""Tests for higher_rank.py (README section 10). Pure Python, a few seconds.
By MV2 of Munim, Inc.; researched and written with AI agents working in MV2's name.
Code Apache-2.0."""
import math
import random
import unittest

from higher_rank import (FIELD_SIZES, Field, asymptotic_window, entropy, flat_cost, klss_best,
                         klss_lower, klss_theorem10, norm_deficit, norm_witness,
                         one_coordinate_floor, phi, phi_best, phi_norm, phi_square, phi_zero,
                         planes, slice_counts, square_witness, translate, zero_witness)


class Fields(unittest.TestCase):
    def test_field_axioms(self):
        for q in FIELD_SIZES:
            F = Field(q)
            for a in range(q):
                self.assertEqual(F.add[a][0], a)
                self.assertEqual(F.mul[a][1], a)
                self.assertEqual(F.add[a][F.neg[a]], 0)
                if a:
                    self.assertEqual(sorted(F.mul[a]), list(range(q)))  # a is invertible
                for b in range(q):
                    self.assertEqual(F.add[a][b], F.add[b][a])
                    self.assertEqual(F.mul[a][b], F.mul[b][a])
            rng = random.Random(q)
            for _ in range(300):
                a, b, c = (rng.randrange(q) for _ in range(3))
                self.assertEqual(F.add[F.add[a][b]][c], F.add[a][F.add[b][c]])
                self.assertEqual(F.mul[F.mul[a][b]][c], F.mul[a][F.mul[b][c]])
                self.assertEqual(F.mul[a][F.add[b][c]], F.add[F.mul[a][b]][F.mul[a][c]])

    def test_entropy(self):
        self.assertAlmostEqual(entropy([1, 1]), 1.0, places=12)
        self.assertAlmostEqual(entropy([9, 0, 0]), 0.0, places=12)
        self.assertAlmostEqual(entropy([1, 4, 4]), 2 * math.log2(3) - 16 / 9, places=12)


class Witnesses(unittest.TestCase):
    def test_norm_form_slices(self):
        # N vanishes only at 0 and takes each nonzero value q + 1 times, and every slice
        # N(u) + <t, u> of the norm witness on F_q^2 is a translate of that law
        for q in FIELD_SIZES:
            F = Field(q)
            f = norm_witness(F)
            vecs = F.vectors(2)
            self.assertEqual([u for u in vecs if f(u) == 0], [(0, 0)])
            for t in vecs:
                self.assertEqual(sorted(slice_counts(F, f, vecs, t)), [1] + [q + 1] * (q - 1))

    def test_closed_forms(self):
        cases = ([(q, 1) for q in FIELD_SIZES] + [(q, 2) for q in FIELD_SIZES]
                 + [(q, 3) for q in (2, 3, 4, 5)])
        for q, r in cases:
            F = Field(q)
            self.assertAlmostEqual(phi(F, r, zero_witness(F)), phi_zero(q, r), places=9)
            self.assertAlmostEqual(phi(F, r, square_witness(F)), phi_square(q, r), places=9)
            if r >= 2:
                self.assertAlmostEqual(phi(F, r, norm_witness(F)), phi_norm(q, r), places=9)
        # rank 1: the square witness is Theorem 1's h_1 = log2 q - (q - 1)/q
        for q in FIELD_SIZES:
            self.assertAlmostEqual(phi_square(q, 1), math.log2(q) - (q - 1) / q, places=12)

    def test_floor_and_collisions(self):
        # Proposition 1: each pair of columns collides in exactly q^(r-1) slices, and no f goes
        # below the floor, which is the logarithm of the KLSS Theorem 1 bound
        rng = random.Random(7)
        for q, r in [(2, 2), (3, 2), (4, 2), (5, 2), (2, 3), (3, 3)]:
            F = Field(q)
            vecs = F.vectors(r)
            N = len(vecs)
            floor = one_coordinate_floor(q, r)
            self.assertAlmostEqual(2 ** floor, klss_lower(q, r), places=9)
            fs = [zero_witness(F), square_witness(F), norm_witness(F)]
            for _ in range(5):
                fs.append({u: rng.randrange(q) for u in vecs}.__getitem__)
            for f in fs:
                pairs = sum(c * (c - 1) // 2 for t in vecs for c in slice_counts(F, f, vecs, t))
                self.assertEqual(pairs, q ** (r - 1) * N * (N - 1) // 2)
                self.assertGreaterEqual(phi(F, r, f), floor - 1e-12)

    def test_some_translate_does_as_well_on_any_column_law(self):
        # proof of Theorem 5: averaged over the translates f(. - b), the cost on any column law
        # is at most Phi(f), by concavity
        rng = random.Random(3)
        for q, r in [(3, 2), (4, 2), (5, 2), (3, 3)]:
            F = Field(q)
            vecs = F.vectors(r)
            fs = [square_witness(F), norm_witness(F), {u: rng.randrange(q) for u in vecs}.__getitem__]
            for f in fs:
                bound = phi(F, r, f)
                for _ in range(3):
                    columns = [rng.choice(vecs) for _ in range(rng.randrange(1, 2 * len(vecs)))]
                    values = [phi(F, r, translate(F, f, b), columns) for b in vecs]
                    self.assertLessEqual(sum(values) / len(values), bound + 1e-9)
                    self.assertLessEqual(min(values), bound + 1e-9)


class Flats(unittest.TestCase):
    def test_every_plane_has_a_cheap_flat(self):
        """Theorem 5 with one block: for every 2-dimensional subspace D of F_q^n, some translate of
        the witness gives a flat a + D whose points have average log2 N at most n Phi(f)."""
        for q, n, count in [(3, 4, 130), (2, 5, 155), (4, 3, 21)]:
            F = Field(q)
            ps = planes(F, n)
            self.assertEqual(len(ps), count)  # Gaussian binomial coefficient
            for f in (square_witness(F), norm_witness(F)):
                bound = n * phi(F, 2, f)
                for basis in ps:
                    best = min(flat_cost(F, translate(F, f, b), basis) for b in F.vectors(2))
                    self.assertLessEqual(best, bound + 1e-9)


class QuotedNumbers(unittest.TestCase):
    def test_rank_two_table(self):
        # q: (KLSS lower bound, best KLSS upper bound, Theorem 5 with the best witness)
        table = {2: (1.6000, 1.6818, 1.6818), 3: (2.4545, 2.6553, 2.5717),
                 4: (3.3684, 3.6680, 3.5125), 5: (4.3103, 4.6883, 4.4751),
                 7: (6.2364, 6.7275, 6.3905), 8: (7.2113, 7.7442, 7.3595)}
        for q, (low, old, new) in table.items():
            self.assertAlmostEqual(klss_lower(q, 2), low, places=3)
            self.assertAlmostEqual(klss_best(q, 2), old, places=3)
            self.assertAlmostEqual(2 ** phi_best(q, 2), new, places=3)
        self.assertAlmostEqual(klss_lower(3, 3), 2.7931, places=3)
        self.assertAlmostEqual(klss_best(3, 3), 2.8804, places=3)
        self.assertAlmostEqual(2 ** phi_best(3, 3), 2.8499, places=3)
        self.assertAlmostEqual(norm_deficit(3), 1.735, places=3)
        self.assertAlmostEqual(norm_deficit(4), 2.83, places=2)
        self.assertAlmostEqual(norm_deficit(5), 3.99, places=2)
        self.assertAlmostEqual(norm_deficit(7), 6.440, places=3)
        self.assertAlmostEqual(phi_square(3, 2), math.log2(3) - 2 / 9, places=12)

    def test_proposition_2_numbers(self):
        # Delta = log2 3 - H for the count patterns of a slice of 9 points over F_3
        def delta(*counts):
            return math.log2(3) - entropy(list(counts))

        def excess(*counts):
            return sum(c * (c - 1) // 2 for c in counts) - 9

        self.assertAlmostEqual(delta(5, 4, 0), 0.5939, places=4)
        self.assertAlmostEqual(delta(6, 2, 1), 0.3606, places=4)
        self.assertAlmostEqual(delta(4, 3, 2), 0.0545, places=4)
        self.assertAlmostEqual(delta(4, 4, 1), 0.1928, places=4)
        case_ii = 2 * delta(5, 4, 0) + delta(6, 2, 1) + 6 * delta(4, 3, 2)
        self.assertAlmostEqual(case_ii, 1.8752, places=4)
        self.assertLess(case_ii, 2)
        full = [(4, 3, 2), (5, 2, 2), (4, 4, 1), (5, 3, 1), (6, 2, 1), (7, 1, 1)]
        ratios = {p: delta(*p) / excess(*p) for p in full}
        self.assertEqual(max(ratios, key=ratios.get), (4, 4, 1))
        best = ratios[(4, 4, 1)]
        self.assertAlmostEqual(best, 0.0643, places=4)
        self.assertAlmostEqual(27 * best, 1.7353, places=4)
        # the norm form: nine slices with counts {4, 4, 1}
        self.assertAlmostEqual(27 * best, 9 * (math.log2(3) - phi_norm(3, 2)), places=9)
        one_missing = [delta(*p) + best * (27 - excess(*p))
                       for p in [(5, 4, 0), (6, 3, 0), (7, 2, 0), (8, 1, 0), (9, 0, 0)]]
        self.assertAlmostEqual(max(one_missing), 1.8793, places=4)
        self.assertLess(max(one_missing), 2)
        # every count pattern of 9 points with all three values present is in `full` or {3,3,3}
        patterns = {tuple(sorted((a, b, 9 - a - b), reverse=True))
                    for a in range(1, 8) for b in range(1, 9 - a)}
        self.assertEqual(patterns, set(full) | {(3, 3, 3)})
        self.assertAlmostEqual(entropy([1, 3]), 0.8113, places=4)

    def test_which_witness_wins(self):
        for q in (3, 4, 5):
            self.assertLess(phi_square(q, 2), min(phi_norm(q, 2), phi_zero(q, 2)))
        for q in (7, 8, 9, 11, 13, 16, 25, 27, 32, 49, 64):
            self.assertLess(phi_norm(q, 2), min(phi_square(q, 2), phi_zero(q, 2)))
        self.assertAlmostEqual(phi_square(2, 2), phi_zero(2, 2), places=12)
        self.assertLess(phi_zero(2, 2), phi_norm(2, 2))

    def test_beats_klss_for_q_at_least_3(self):
        for q in (3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27, 32, 49, 64):
            for r in (2, 3, 4):
                new = 2 ** phi_best(q, r)
                self.assertLess(new, klss_best(q, r))
                self.assertGreater(new, klss_lower(q, r))
        for r in (2, 3, 4):
            # q = 2: the witnesses only match KLSS Theorem 10 (2^(3n/4) for r = 2)
            self.assertAlmostEqual(2 ** phi_best(2, r), klss_theorem10(2, r), places=12)

    def test_second_order_window(self):
        for q in (2, 3, 4, 5, 7, 8, 9, 16, 27, 32, 64):
            for r in (2, 3, 4):
                low, high = asymptotic_window(q, r)
                self.assertLessEqual(low, klss_lower(q, r) + 1e-12)
                self.assertLessEqual(2 ** phi_norm(q, r), high + 1e-12)
                self.assertLess(low, high)


if __name__ == "__main__":
    unittest.main()
