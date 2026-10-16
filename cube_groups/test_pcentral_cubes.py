# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests for pcentral_cubes.py. Only facts proved by hand are asserted exactly; the full
subgroup check of P(3) and the Q_16 exponents run in main()."""
import unittest

import pcentral_cubes as pc


class Structure(unittest.TestCase):
    def test_tables_are_groups_of_the_right_order(self):
        for T, n in ((pc.q8_z2(), 16), (pc.z4_z4(), 16), (pc.dihedral(4), 8),
                     (pc.quaternion16(), 16), (pc.p_group(3)[0], 243)):
            self.assertEqual(len(T), n)
            self.assertEqual(T[0], list(range(n)))
            for a in (1, n // 2, n - 1):
                for b in (2, n // 3, n - 2):
                    for c in (3, n - 3):
                        self.assertEqual(T[T[a][b]][c], T[a][T[b][c]])

    def test_hypotheses(self):
        self.assertEqual(pc.hypotheses(pc.q8_z2(), 2), (True, True, True))
        self.assertEqual(pc.hypotheses(pc.z4_z4(), 2), (True, True, True))
        self.assertEqual(pc.hypotheses(pc.p_group(3)[0], 3), (True, True, True))
        self.assertEqual(pc.hypotheses(pc.dihedral(4), 2), (True, True, False))
        self.assertFalse(pc.hypotheses(pc.quaternion16(), 2)[0])

    def test_centre_of_p_group(self):
        T, elems = pc.p_group(3)
        Z = pc.centre(T)
        self.assertEqual(len(Z), 27)
        self.assertTrue(all(elems[z][0] % 3 == 0 and elems[z][1] % 3 == 0 for z in Z))


class LemmaThirteen(unittest.TestCase):
    def test_every_subgroup_of_the_order_16_groups(self):
        for T in (pc.q8_z2(), pc.z4_z4()):
            s = pc.lemma_summary(T, pc.all_subgroups(T), 3)
            self.assertTrue(s["centre_bound_holds"])
            self.assertTrue(s["intersection_bound_holds"])

    def test_two_generated_subgroups_of_p3(self):
        T = pc.p_group(3)[0]
        Z = pc.centre(T)
        for L in pc.two_generated_subgroups(T):
            self.assertGreaterEqual(len(L & Z) ** 2, len(L))

    def test_half_is_attained(self):
        self.assertEqual(pc.p_group_example(3), (9, 3))
        self.assertEqual(pc.p_group_example(5), (25, 5))

    def test_non_central_prime_order_gives_lambda_zero_in_the_square(self):
        self.assertEqual(pc.diagonal_prime_order(pc.dihedral(3), 3, 1), (2, 1))
        self.assertEqual(pc.diagonal_prime_order(pc.dihedral(4), 4, 1), (2, 1))


class Powers(unittest.TestCase):
    def test_r2_never_breaks_at_lambda_half(self):
        for p in (3, 5, 7):
            self.assertIsNone(pc.least_power(p * p, p, 2))

    def test_r3_least_powers(self):
        # 2^24 < p^m: 3^15 = 14348907 <= 2^24 < 3^16, 5^10 <= 2^24 < 5^11, 7^8 <= 2^24 < 7^9.
        self.assertEqual(pc.least_power(9, 3, 3), 16)
        self.assertEqual(pc.least_power(25, 5, 3), 11)
        self.assertEqual(pc.least_power(49, 7, 3), 9)

    def test_lambda_zero_breaks_r2_from_p_m_above_256(self):
        # |L| = p, |I| = 1: 2^8 p^(8m) < p^(9m) iff p^m > 256.
        self.assertEqual(pc.least_power(2, 1, 2), 9)
        self.assertEqual(pc.least_power(3, 1, 2), 6)


if __name__ == "__main__":
    unittest.main()
