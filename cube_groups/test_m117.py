# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m117.py (job m117, cube_groups/m117-predictions.md). Needs m113.py and the modules
it imports next to it. The three cases, their clause counts and their pysat times are read by hand
from m112l's rows (compete-results m112l-b7-sweep-v1, 2026-10-27)."""
import unittest

import m117

A = "r3b_t8_B7_o007_c005_t2_m034"
B = "r3b_t8_B7_o009_c002_t3_m004_034"
C = "r3b_t8_B7_o010_c000_t2_m047"


class TestM117(unittest.TestCase):
    def test_cases_are_d1_and_caps(self):
        cases = m117.m113.d1_cases()
        self.assertEqual(sorted(m117.CASES), [A, B, C])
        for x in (A, B, C):
            spec, case = cases[x]
            self.assertEqual(spec["dmeet"], 1)
        self.assertEqual(cases[A][1]["kind"], "t2")
        self.assertEqual(cases[B][1]["kind"], "t3")
        self.assertEqual(cases[C][1]["kind"], "t2")
        self.assertEqual(m117.order(), [A, B, C])
        self.assertEqual(m117.CADICAL_CAP, 4 * m117.m113.CADICAL_CAP)
        self.assertGreater(m117.DRAT_CAP["sweep"], m117.m113.DRAT_CAP["sweep"])

    def test_grade_rows(self):
        def row(x, cert, clauses=None):
            return {"instance": x, "mode": "sweep", "cert": cert,
                    "clauses": clauses or m117.CASES[x][0], "cadical": {"seconds": 500.0},
                    "drat": {"seconds": 900.0}, "proof_bytes": 10, "wall_seconds": 1500.0}

        g, out = m117.grade_rows([row(A, "VERIFIED"), row(B, "VERIFIED"), row(C, "VERIFIED")])
        self.assertTrue(all(g.values()), g)
        self.assertEqual(out["verified"], 3)
        self.assertEqual(out["per_case"]["drat_over_cadical"], [1.8, 1.8, 1.8])
        g, _ = m117.grade_rows([row(A, "VERIFIED"), row(B, "UNKNOWN", 5),
                                {"instance": C, "mode": "sweep", "cert": "SKIPPED"}])
        self.assertFalse(g["all_verified"] or g["same_cnf"])
        self.assertTrue(g["all_accounted"] and g["no_sat"] and g["mode_sweep"])
        g, out = m117.grade_rows([row(A, "SAT")])
        self.assertFalse(g["all_accounted"] or g["no_sat"] or g["all_verified"])
        self.assertNotIn("per_case", out)


if __name__ == "__main__":
    unittest.main()
