# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests of a6_r4.py (job m23). Pure Python: no SAT solver is needed."""
import json
import os
import tempfile
import unittest

import a6_r4
import shape_c as sc


class TestInstances(unittest.TestCase):
    def test_selfcheck(self):
        st = a6_r4.selfcheck()
        self.assertTrue(all(st["graded"].values()), st)

    def test_reps(self):
        full = a6_r4.reps(6, 2, skip_by_hand=False)
        kept = a6_r4.reps(6, 2)
        self.assertEqual(len(full), 34)
        self.assertEqual(len(kept), 32)
        ident = sc.identity(4)
        self.assertTrue(all(len(Ms) == 1 and Ms[0] not in (0, ident) for _, Ms in kept))
        self.assertEqual(sorted({Ms[0] for _, Ms in full} - {Ms[0] for _, Ms in kept}),
                         [0, ident])
        self.assertEqual(len({idx for idx, _ in kept}), 32)
        # the indices are those of shape_c.orbits, so the instance names agree with shape_c
        orb = sc.orbits(4, 1)
        self.assertTrue(all(orb[idx][0] == Ms for idx, Ms in kept))

    def test_controls_run_every_class(self):
        self.assertEqual(len(a6_r4.reps(3, 2, skip_by_hand=False)), 2)
        self.assertEqual(len(a6_r4.reps(4, 2, skip_by_hand=False)), 6)


class TestGrade(unittest.TestCase):
    def write(self, d, name, res):
        with open(os.path.join(d, name + ".json"), "w") as f:
            json.dump(res, f)

    def test_grade_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "selfcheck.json"), "w") as f:
                json.dump(a6_r4.selfcheck(), f)
            for t, k in a6_r4.CONTROLS:
                for idx, Ms in a6_r4.reps(t, k, skip_by_hand=False):
                    name = sc.instance_name(t, k, idx)
                    self.write(d, name, {"status": "UNSAT", "name": name, "t": t, "k": k})
            idx, Ms = a6_r4.reps(6, 2)[0]
            name = sc.instance_name(6, 2, idx)
            self.write(d, name, {"status": "UNKNOWN", "name": name, "t": 6, "k": 2,
                                 "wall_seconds": 300.0})
            out = a6_r4.grade(d)
            self.assertTrue(all(out["graded"].values()), out["graded"])
            self.assertEqual(len(out["graded"]), 1 + 2 + 6)
            self.assertEqual(out["ungraded"], {})
            self.assertEqual(out["counts_6_2"], {"UNKNOWN": 1, "missing": 31})
            self.assertFalse(out["all_unsat_6_2"])
            self.assertFalse(out["any_sat_6_2"])
            # an unverified SAT answer fails the grade
            idx2, _ = a6_r4.reps(6, 2)[1]
            name2 = sc.instance_name(6, 2, idx2)
            self.write(d, name2, {"status": "SAT", "name": name2, "t": 6, "k": 2,
                                  "verified": False, "facts": {"max_rank": 4}})
            out = a6_r4.grade(d)
            self.assertFalse(out["graded"][name2 + "_verified"])
            self.assertTrue(out["graded"][name2 + "_ranks"])
            self.assertTrue(out["any_sat_6_2"])

    def test_grade_missing(self):
        with tempfile.TemporaryDirectory() as d:
            out = a6_r4.grade(d)
            self.assertEqual(out["ungraded"]["selfcheck"], "missing")
            self.assertEqual(out["counts_6_2"], {"missing": 32})


if __name__ == "__main__":
    unittest.main()
