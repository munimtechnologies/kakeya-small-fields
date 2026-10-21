# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m61.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m61


class TestM61(unittest.TestCase):
    def test_l_au(self):
        # A_u = e_4 -> e_2, e_5 -> e_1, e_6 -> e_0.
        self.assertEqual([m.column(m61.L_AU, c) for c in range(m61.T)], [0, 0, 0, 0, 4, 2, 1])

    def test_l_index_of_unit_maps(self):
        # m59's index 512 is A e_4 = e_2 (coordinate 1 of the e_4 field), 2560 is A e_4 = e_2 + e_0.
        self.assertEqual(m61.l_index(1 << (7 * 2 + 4)), 512)
        self.assertEqual(m61.l_index((1 << (7 * 2 + 4)) | (1 << 4)), 2560)

    def test_l_open_rows(self):
        ks = [row[0] for row in m61.L_OPEN]
        self.assertEqual(ks, sorted(set(ks)))
        for k, idx, rk, a1, size in m61.L_OPEN:
            self.assertTrue(m61.admissible_l(a1))
            self.assertEqual(m.rank_on_x1(a1), rk)
            self.assertEqual(m61.l_index(a1), idx)
            self.assertGreater(size, 0)

    def test_l_spec_name(self):
        sp = m61.l_spec(*m61.L_OPEN[0])
        self.assertEqual(sp["name"], "r3l_t7_B6_o000_a031")
        self.assertEqual((sp["p"], sp["pair"], sp["au"]), (6, 0, m61.L_AU))

    def test_classes_split_by_group(self):
        a = {s["name"] for s in m61.classes_with_d(2)}
        b = {s["name"] for s in m61.classes_with_d(1)}
        c = {s["name"] for s in m61.classes_with_d(0)}
        self.assertFalse(a & b or a & c or b & c)
        self.assertEqual(a | b | c, set(m61.OPEN_M47))

    def test_plan(self):
        pa, pb = m61.plan("a"), m61.plan("b")
        named = pa[:2 * len(m61.L_OPEN)]
        for i in range(0, len(named), 2):
            self.assertEqual(named[i][0]["name"], named[i + 1][0]["name"])
            self.assertEqual((named[i][1], named[i + 1][1]), ("cadical", "xor"))
            self.assertEqual((named[i][3], named[i + 1][3]), (None, "open"))
            self.assertEqual(named[i][2], m61.L_CAP)
        rest = pa[2 * len(m61.L_OPEN):]
        for p, d in ((rest, 2), (pb, 1)):
            self.assertTrue(all(e[1] == "cadical" and e[2] == m61.CLASS_CAP and e[3] == "full"
                                for e in p))
            self.assertTrue(all(m.meet_d(e[0]) == d for e in p))

    def test_grade_without_check(self):
        with tempfile.TemporaryDirectory() as d:
            out = m61.grade("b", d)
            self.assertIn("check", out["ungraded"])
            self.assertFalse(out["any_sat_7"])
            self.assertEqual(out["b6_unsat"], [])

    def test_grade_counts(self):
        with tempfile.TemporaryDirectory() as d:
            plan = m61.plan("a")
            classes = [e for e in plan if e[3] == "full"]
            for spec, arm, _, cond in plan:
                if cond == "open":
                    continue
                s = "SKIPPED" if spec is classes[-1][0] else "UNSAT"
                with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                    json.dump({"status": s, "wall_seconds": 1.0, "budget_seconds": 300.0}, f)
            out = m61.grade("a", d)
            self.assertTrue(out["kind_l_empty"])
            self.assertEqual(out["l_unsat_of_308"], 308)
            self.assertEqual(len(out["b6_unsat"]), len(classes) - 1)
            self.assertEqual(out["b6_skipped"], [classes[-1][0]["name"]])
            self.assertEqual(out["b6_open"], [])


if __name__ == "__main__":
    unittest.main()
