# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m115.py (job m115, cube_groups/m115-predictions.md). Needs m113.py and the modules
it imports next to it. The two cases are read by hand from m113e's and m113d's cert files
(2026-10-27): both "n" CNFs, 546,161 and 545,153 clauses."""
import unittest

import m115

A = "r3b_t8_B7_o007_c001_t2_m026"
B = "r3b_t8_B7_o007_c009_t3_m011_017"


class TestM115(unittest.TestCase):
    def test_cases_are_d1_and_caps_doubled(self):
        cases = m115.m113.d1_cases()
        self.assertEqual(sorted(m115.CASES), [A, B])
        for x in (A, B):
            spec, case = cases[x]
            self.assertEqual(spec["dmeet"], 1)
        self.assertEqual(cases[A][1]["kind"], "t2")
        self.assertEqual(cases[B][1]["kind"], "t3")
        self.assertEqual(m115.CADICAL_CAP, 2 * m115.m113.CADICAL_CAP)
        self.assertEqual(m115.DRAT_CAP["n"], 2 * m115.m113.DRAT_CAP["n"])

    def test_grade_rows(self):
        def row(x, cert, sha=None):
            return {"instance": x, "mode": "n", "cert": cert,
                    "cnf_sha256": sha or m115.CASES[x][1], "cadical": {"seconds": 700.0},
                    "drat": {"seconds": 900.0}, "proof_bytes": 10}

        g, out = m115.grade_rows([row(A, "VERIFIED"), row(B, "VERIFIED")])
        self.assertTrue(all(g.values()), g)
        self.assertEqual(out["verified"], 2)
        g, _ = m115.grade_rows([row(A, "VERIFIED"), row(B, "UNKNOWN", "0" * 64)])
        self.assertFalse(g["all_verified"] or g["same_cnf"])
        self.assertTrue(g["all_accounted"] and g["no_sat"])
        g, _ = m115.grade_rows([row(A, "SAT")])
        self.assertFalse(g["all_accounted"] or g["no_sat"] or g["all_verified"])


if __name__ == "__main__":
    unittest.main()
