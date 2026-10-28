# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m121.py (job m121, cube_groups/m121-predictions.md). Needs m120.py, m113.py and the
modules they import next to it. Expectations worked out by hand:

- cubes([5, 7]) is every sign pattern, in itertools.product order: [5, 7], [5, -7], [-5, 7],
  [-5, -7].
- A_(h_1) with variables [[1, 2], [3, 4]] and clauses [1], [2, 3], [-2, 3], [3, -4], [2, 5]: 1 is
  fixed by a unit clause; 2 and 3 occur three times each, 4 once, so K = 2 picks [2, 3]; 3 sits at
  row 1, column 0.
- verdict: all cubes UNSAT gives UNSAT, one SAT cube gives SAT, UNSAT with UNKNOWN gives OPEN, no
  cubes gives OPEN.
- pilot_cases takes the first case by name of each label present (label = name[20:]).
"""
import unittest

import m121

A = [None] * m121.H1 + [[[1, 2], [3, 4]]]
NAMES = (A,)
CLAUSES = [[1], [2, 3], [-2, 3], [3, -4], [2, 5]]


class TestM121(unittest.TestCase):
    def test_cubes(self):
        self.assertEqual(m121.cubes([5, 7]), [[5, 7], [5, -7], [-5, 7], [-5, -7]])
        self.assertEqual(len(m121.cubes([1, 2, 3])), 8)

    def test_cube_vars(self):
        self.assertEqual(m121.cube_vars(CLAUSES, NAMES, 2), [2, 3])
        self.assertEqual(m121.position(NAMES, 3), [1, 0])

    def test_verdict(self):
        u, s, k = {"status": "UNSAT"}, {"status": "SAT"}, {"status": "UNKNOWN"}
        self.assertEqual(m121.verdict([u, u]), "UNSAT")
        self.assertEqual(m121.verdict([u, s, k]), "SAT")
        self.assertEqual(m121.verdict([u, k]), "OPEN")
        self.assertEqual(m121.verdict([]), "OPEN")

    def test_pilot_cases(self):
        names = sorted(["r3b_t8_B7_o007_c001_t2_m026", "r3b_t8_B7_o001_c001_t2_m011",
                        "r3b_t8_B7_o000_c000_t2_m011"])
        self.assertEqual(m121.pilot_cases(names),
                         ["r3b_t8_B7_o000_c000_t2_m011", "r3b_t8_B7_o007_c001_t2_m026"])


if __name__ == "__main__":
    unittest.main()
