# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests of a6_casea.py (job m24). Pure Python: no SAT solver is needed."""
import json
import os
import tempfile
import unittest

import a6_casea as m
import case_a as ca
import sat_aniso as sa


class TestReps(unittest.TestCase):
    def test_reps(self):
        rs = m.reps()
        self.assertEqual(len(rs), 21)
        self.assertEqual(len({C for _, C in rs}), 21)
        self.assertTrue(all(m.is_candidate(C) for _, C in rs))
        self.assertEqual([ca.invariants(C, 6)[0] for _, C in rs], [1] * 11 + [2] * 10)

    def test_hand_counts(self):
        # rank-3 classes: 37,800 matrices x 64 maps c; rank-2 classes: 7,350 x 96
        self.assertEqual(sum(m.HAND_SIZES[:11]), 37800 * 64)
        self.assertEqual(sum(m.HAND_SIZES[11:]), 7350 * 96)
        self.assertEqual(sum(m.HAND_SIZES), m.CANDIDATES)
        self.assertEqual(m.CANDIDATES, 3124800)
        self.assertEqual(ca.group_order(6), 5160960)
        self.assertTrue(all(ca.group_order(6) % s == 0 for s in m.HAND_SIZES))

    def test_j4(self):
        # Cbar = J4: C is the chain e5 -> e4 -> e3 -> e2 -> e1 -> 0 with e0 -> 0
        C = m.reps()[0][1]
        self.assertEqual([sa.mat_apply(C, 1 << j, 6) for j in range(6)], [0, 0, 2, 4, 8, 16])

    def test_stabilisers_by_hand(self):
        rs = m.reps()
        for i, s in m.HAND_STAB.items():
            stab = m.transporters(rs[i][1], rs[i][1])
            self.assertEqual(len(stab), s)
            self.assertIn(sa.from_cols([1 << j for j in range(6)], 6), stab)

    def test_transporter(self):
        C = m.reps()[3][1]
        g = ca.generators(6)[0]
        self.assertIn(g, m.transporters(C, ca.conj(g, C, 6)))
        # J4 and J3+1 (different classes of Cbar) are not conjugate
        self.assertEqual(m.transporters(m.reps()[0][1], m.reps()[1][1], first=True), [])

    def test_selfcheck(self):
        st = m.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])


class TestGrade(unittest.TestCase):
    def write(self, d, name, res):
        with open(os.path.join(d, name + ".json"), "w") as f:
            json.dump(res, f)

    def test_grade_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "selfcheck.json"), "w") as f:
                json.dump({"graded": {"reps": True}}, f)
            for t, n in m.CONTROL_COUNTS.items():
                for i in range(n):
                    name = ca.instance_name(t, i)
                    self.write(d, name, {"status": "UNSAT", "name": name, "t": t})
            name = ca.instance_name(6, 0)
            self.write(d, name, {"status": "UNKNOWN", "name": name, "t": 6,
                                 "wall_seconds": 360.0})
            out = m.grade(d)
            self.assertTrue(all(out["graded"].values()), out["graded"])
            self.assertEqual(len(out["graded"]), 1 + 1 + 3 + 9)
            self.assertEqual(out["ungraded"], {})
            self.assertEqual(out["counts_6"], {"UNKNOWN": 1, "missing": 20})
            self.assertFalse(out["all_unsat_6"])
            self.assertFalse(out["any_sat_6"])
            # an unverified SAT answer fails the grade
            name2 = ca.instance_name(6, 1)
            self.write(d, name2, {"status": "SAT", "name": name2, "t": 6, "verified": False,
                                  "facts": {"max_rank": 4}})
            out = m.grade(d)
            self.assertFalse(out["graded"][name2 + "_verified"])
            self.assertTrue(out["graded"][name2 + "_ranks"])
            self.assertTrue(out["any_sat_6"])

    def test_grade_missing(self):
        with tempfile.TemporaryDirectory() as d:
            out = m.grade(d)
            self.assertEqual(out["ungraded"]["selfcheck"], "missing")
            self.assertEqual(out["counts_6"], {"missing": 21})


if __name__ == "__main__":
    unittest.main()
