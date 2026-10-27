# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m118.py (job m118, cube_groups/m118-predictions.md). Needs m113.py, the modules it
imports and the grade files m110{a..j}_grade.json next to it. The counts are read by hand from
m110i_grade.json (cube_groups/results/m110i, 2026-10-27): "n" UNSAT 332, sweep UNSAT 1."""
import unittest

import m111
import m113
import m118


class TestM118(unittest.TestCase):
    def test_items(self):
        items = m113.decided(m111.m110_parts("i"))
        self.assertEqual(len(items), m118.TOTAL)
        self.assertEqual(sum(m == "n" for _, m in items), 332)
        self.assertEqual([m for _, m in items if m != "n"], ["sweep"])
        cases = m113.d1_cases()
        self.assertTrue(all(x in cases for x, _ in items))
        done = {x for x, _ in m113.decided(m111.m110_parts(m113.M110_DONE))}
        self.assertEqual(len(done), 3075)
        self.assertFalse(done & {x for x, _ in items})

    def test_grade_rows(self):
        mine = [["r3b_x_a", "n"], ["r3b_x_b", "sweep"]]
        rows = [{"instance": "r3b_x_a", "name": "r3b_x", "kind": "t2", "mode": "n",
                 "cert": "VERIFIED", "clauses": 5, "cadical": {"seconds": 1.0},
                 "drat": {"seconds": 2.0}},
                {"instance": "r3b_x_b", "name": "r3b_x", "mode": "sweep", "cert": "SKIPPED"}]
        g, out = m113.grade_rows(rows, mine)
        self.assertTrue(g["all_accounted"] and g["no_sat"] and g["all_verified"])
        self.assertEqual(out["skipped"], ["r3b_x_b"])
        rows[0]["cert"] = "UNKNOWN"
        g, _ = m113.grade_rows(rows, mine)
        self.assertFalse(g["all_verified"])


if __name__ == "__main__":
    unittest.main()
