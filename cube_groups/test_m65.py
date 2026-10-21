# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m65.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m61
import m65


class TestM65(unittest.TestCase):
    def test_lists_disjoint(self):
        lists = (m65.UNSAT_M61B, m65.OPEN_M61B, m65.SKIPPED_M61B, m65.D0_M47)
        names = [n for p in lists for n in p]
        self.assertEqual(len(names), len(set(names)))
        self.assertTrue(set(names) <= set(m61.OPEN_M47))

    def test_names_parse(self):
        for n in m65.GROUP_OF:
            self.assertEqual(n, "r3b_t7_B6_o%03d_c%03d" % m.pair_cls(n))

    def test_plan(self):
        p = m65.plan()
        self.assertEqual(len(p), len(m65.SKIPPED_M61B) + len(m65.D0_M47))
        self.assertTrue(all(e[1] == "cadical" and e[2] == m61.CLASS_CAP and e[3] == "full"
                            for e in p))
        self.assertTrue(all(e[0]["au"] == m61.OPEN_M47[e[0]["name"]] for e in p))

    def test_plan_fits(self):
        # Every entry runs to its cap and still the last one fits in the default 152 minutes.
        self.assertLessEqual(len(m65.plan()) * m61.CLASS_CAP, 152 * 60)

    def test_grade_without_check(self):
        with tempfile.TemporaryDirectory() as d:
            out = m65.grade(d)
            self.assertIn("check", out["ungraded"])
            self.assertFalse(out["any_sat_7"])
            self.assertEqual(out["b6_unsat"], [])

    def test_grade_counts(self):
        with tempfile.TemporaryDirectory() as d:
            p = m65.plan()
            for i, (spec, arm, _, _) in enumerate(p):
                s = ("UNSAT", "UNKNOWN", "SKIPPED")[i % 3]
                with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                    json.dump({"status": s, "wall_seconds": 1.0, "budget_seconds": 900.0}, f)
            out = m65.grade(d)
            self.assertEqual(len(out["b6_unsat"]) + len(out["b6_open"]) + len(out["b6_skipped"]),
                             len(p))
            self.assertEqual(out["b6_unsat"], [e[0]["name"] for e in p[0::3]])
            self.assertEqual(sum(sum(v.values()) for v in out["by"].values()), len(p))


if __name__ == "__main__":
    unittest.main()
