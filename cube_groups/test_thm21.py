# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import importlib.util
import unittest

import thm21


class TestHelpers(unittest.TestCase):
    def test_outer_pairs_to_bilinear_form(self):
        a, b = 3, 2
        for M in range(1 << (a * b)):
            for y in range(1, 1 << b):
                for x in range(1 << a):
                    self.assertEqual(thm21.parity(M & thm21.outer(y, x, a, b)),
                                     thm21.parity(y & thm21.apply(M, x, a, b)))

    def test_bases_of(self):
        self.assertEqual(len(thm21.bases_of(1)), 1)
        self.assertEqual(len(thm21.bases_of(2)), 3)
        self.assertEqual(len(thm21.bases_of(3)), 28)

    def test_max_subspace_in(self):
        self.assertEqual(thm21.max_subspace_in({0, 1, 2, 3, 4}, 3), {0, 1, 2, 3})
        self.assertEqual(thm21.max_subspace_in({0}, 2), {0})
        self.assertEqual(len(thm21.max_subspace_in(set(range(16)), 4)), 16)


class TestLemma19(unittest.TestCase):
    def test_slice_dims_match_definition(self):
        for a, b, cmax in [(2, 2, 4), (3, 2, 2), (2, 3, 2), (1, 3, 3)]:
            for c in range(cmax + 1):
                for cons in thm21.subspaces(a * b, c):
                    self.assertEqual(thm21.slice_dims(cons, a, b),
                                     thm21.slice_dims_direct(cons, a, b))

    def test_small_cases(self):
        for a, b, cmax in [(2, 1, 2), (3, 1, 2), (2, 2, 4), (3, 2, 4)]:
            rep = thm21.lemma19_report(a, b, cmax)
            self.assertTrue(thm21.lemma19_match(a, b, rep))
        rep = thm21.lemma19_report(3, 2, 4)
        self.assertEqual(rep[4]["all_d_ge_2"], 7)
        self.assertEqual(rep[3]["all_d_ge_2"], 0)

    def test_k_x_has_all_slices_two(self):
        a, b = 3, 2
        X = [0b001, 0b010]
        cons = [thm21.outer(y, x, a, b) for y in (0b01, 0b10) for x in X]
        self.assertEqual(thm21.slice_dims(cons, a, b), {1: 2, 2: 2, 3: 2})


class TestCaseBounds(unittest.TestCase):
    def test_settled_table(self):
        for a in range(1, 9):
            for b in range(0, 9):
                self.assertEqual(thm21.case_bounds(a, b)["settled"], thm21.settled_predicted(a, b),
                                 (a, b))

    def test_named_cases(self):
        self.assertTrue(thm21.case_bounds(3, 4)["settled"])
        self.assertTrue(thm21.case_bounds(4, 2)["settled"])
        self.assertEqual(thm21.case_bounds(5, 2)["open"], [[2, d, 6, 17] for d in range(2, 6)])
        self.assertEqual(thm21.case_bounds(4, 3)["open"], [[2, d, 6, 18] for d in range(2, 5)])
        self.assertFalse(thm21.case_bounds(6, 2)["settled"])


@unittest.skipUnless(importlib.util.find_spec("z4z2"), "needs cube_groups/z4z2.py")
class TestGroups(unittest.TestCase):
    def test_q8_times_z2(self):
        import z4z2
        name, (E, mul, A4, A2), control = z4z2.groups()[0]
        r = thm21.group_report(E, mul, A4, A2)
        self.assertFalse(control)
        self.assertTrue(r["coords_ok"] and r["action_ok"] and r["lemma18_ok"] and r["theorem21_ok"])
        self.assertEqual(r["lemma17_step_violations"], 0)
        self.assertEqual(r["squares_trivial_on_Y"], r["omega_order"])


if __name__ == "__main__":
    unittest.main()
