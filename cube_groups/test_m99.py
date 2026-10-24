# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m99.py: the hand count of Lemmas 83 and 101 against the pair counts that jobs
m27, m30 and m42 found by machine, and the kinds read off m42.invariants."""
import unittest

import m42
import m99


class TestM99(unittest.TestCase):
    def test_gaussian(self):
        self.assertEqual(m99.gaussian(8, 3), 97155)
        self.assertEqual(m99.gaussian(7, 4), 11811)
        self.assertEqual(m99.gaussian(6, 4), 651)
        self.assertEqual(m99.gaussian(7, 3), 11811)
        self.assertEqual(m99.gaussian(5, 3), 155)

    def test_hand_pairs_known(self):
        # m42.HAND_PAIRS: t = 2, 4 exact orbits; t = 6 jobs m27 and m30; t = 7 job m42a
        known = {(2, 1, 1): 3, (4, 3, 2): 7, (4, 2, 2): 19, (6, 5, 3): 11, (6, 4, 3): 39,
                 (7, 6, 3): 13, (7, 5, 3): 49}
        for (t, p, rho), n in known.items():
            self.assertEqual(m99.hand_pairs(t, p, rho), n, (t, p, rho))

    def test_hand_pairs_t8(self):
        self.assertEqual(m99.hand_pairs(8, 7, 3), 13)
        self.assertEqual(m99.hand_pairs(8, 6, 3), 51)

    def test_hand_by_x(self):
        self.assertEqual(m99.hand_by_x(7, 5, 3), {155: 20, 1240: 29})
        self.assertEqual(m99.hand_by_x(6, 4, 3), {35: 18, 120: 21})
        self.assertEqual(m99.hand_by_x(7, 6, 3), {1395: 13})
        self.assertEqual(m99.hand_by_x(8, 7, 3), m99.HAND_BY_X_T8[(8, 7)])
        self.assertEqual(m99.hand_by_x(8, 6, 3), m99.HAND_BY_X_T8[(8, 6)])

    def test_group_orders(self):
        for tp, n in m99.HAND_GROUP_T8.items():
            self.assertEqual(m42.group_order(*tp), n)

    def test_machine_pairs_t4(self):
        self.assertEqual(len(m42.pair_orbits(4, 3, 2)[0]), 7)
        self.assertEqual(len(m42.pair_orbits(4, 2, 2)[0]), 19)

    def test_machine_key(self):
        rr = m42.rref
        cases = [(rr([1, 2]), rr([2, 4]), "alpha_P"), (rr([1, 2]), rr([1, 2]), "alpha_L"),
                 (rr([1, 2]), rr([3, 4]), "alpha_graph"), (rr([1, 2]), rr([8, 2]), "alpha_out"),
                 (rr([1, 8]), rr([2, 4]), "beta_P")]
        for x1, r, want in cases:
            self.assertEqual(m99.machine_key(4, 2, {"x1": x1, "r": r}), want, (x1, r))


if __name__ == "__main__":
    unittest.main()
