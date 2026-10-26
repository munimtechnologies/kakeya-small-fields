# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m110.py (job m110, notes/a102.md). Needs m42.py, sat_aniso.py and m100.py to
m106.py next to it. The class counts are checked against job m104a's count (copied by hand from
m104_count.json), and the pass-2 rule and the grading against small tables worked out by hand."""
import os
import tempfile
import unittest

import m100
import m102
import m110


class TestStatic(unittest.TestCase):
    def test_counts(self):
        self.assertEqual(sum(m110.D1_LE4.values()), 3876)
        self.assertEqual(len(m110.D1_LE4), 34)
        self.assertEqual(sum(m110.SIZE.values()), m110.TOTAL)
        got = {}
        for i in range(m110.TOTAL):
            got[m110.shard_of(i)] = got.get(m110.shard_of(i), 0) + 1
        self.assertEqual(got, m110.SIZE)

    def test_followups_and_final(self):
        rows = [{"part": "n", "instance": "a", "status": "UNSAT"},
                {"part": "n", "instance": "b", "status": "SAT"},
                {"part": "n", "instance": "c", "status": "UNKNOWN"},
                {"part": "sweep", "instance": "b", "status": "UNSAT"}]
        self.assertEqual(m110.followups(rows), ["b", "c"])
        self.assertEqual(m110.final_status({"n": "UNSAT"}), "UNSAT")
        self.assertEqual(m110.final_status({"n": "SAT", "sweep": "UNSAT"}), "UNSAT")
        self.assertEqual(m110.final_status({"n": "UNKNOWN", "sweep": "UNKNOWN"}), "UNKNOWN")
        self.assertEqual(m110.final_status({"n": "SAT"}), "SAT")

    def test_grade_on_a_table(self):
        # shard j (387 cases): 385 UNSAT at "n"; b SAT at "n" then UNSAT at the sweep; c UNKNOWN at
        # "n" and its sweep skipped for time. Nothing skipped at "n".
        rows = [{"part": "n", "instance": f"x{i:03d}", "tag": f"x{i:03d}_n", "status": "UNSAT",
                 "name": "r3b_t8_B7_o007_c000", "type": "irr", "wall_seconds": 10.0}
                for i in range(385)]
        rows.append({"part": "n", "instance": "b", "tag": "b_n", "status": "SAT", "verified": True,
                     "check": {"anisotropic": False}, "name": "r3b_t8_B7_o007_c008",
                     "type": "nil3", "wall_seconds": 3.0})
        rows.append({"part": "n", "instance": "c", "tag": "c_n", "status": "UNKNOWN",
                     "name": "r3b_t8_B7_o007_c008", "type": "F8", "wall_seconds": 60.0})
        rows.append({"part": "sweep", "instance": "b", "tag": "b_sweep", "status": "UNSAT",
                     "name": "r3b_t8_B7_o007_c008", "type": "nil3", "wall_seconds": 50.0})
        with tempfile.TemporaryDirectory() as d:
            m110.save(d, "m110j_rows.json", rows)
            m110.save(d, "m110j_skipped.json", ["c_sweep"])
            out = m110.grade("j", d)
            g = out["graded"]
            self.assertTrue(g["n_ran"] and g["sweep_rule"] and g["no_error"] and g["verified_b_n"])
            self.assertFalse(g["check_ran"] or g["controls_ran"])
            self.assertEqual(out["unsat"], 386)
            self.assertEqual(out["open"], ["c"])
            self.assertEqual(out["sat_n"], ["b"])
            self.assertEqual(out["full_models"], [])
            self.assertEqual(out["by_class"], {"o007_c000": {"UNSAT": 385},
                                               "o007_c008": {"UNSAT": 1, "UNKNOWN": 1}})
            # a sweep that ran on a case UNSAT at "n" breaks the rule; a model anisotropic on all
            # of V is flagged
            rows.append({"part": "sweep", "instance": "x000", "tag": "x000_sweep", "status": "SAT",
                         "verified": True, "check": {"anisotropic": True},
                         "name": "r3b_t8_B7_o007_c000", "type": "irr", "wall_seconds": 5.0})
            m110.save(d, "m110j_rows.json", rows)
            out = m110.grade("j", d)
            self.assertFalse(out["graded"]["sweep_rule"])
            self.assertEqual(out["full_models"], ["x000_sweep"])
            # the case stays UNSAT: the "n" CNF is implied by the sweep CNF
            self.assertEqual(out["unsat"], 386)
            self.assertFalse(os.path.exists(os.path.join(d, "m110j_grade.json")))


class TestCases(unittest.TestCase):
    """The 3,876 cases rebuilt from m100 and m102, against job m104a's count by class."""

    @classmethod
    def setUpClass(cls):
        cls.cases = m110.sweep_cases()
        cls.names = [m102.inst_name(s, c) for s, c in cls.cases]

    def test_by_class(self):
        by_class = {}
        for s, _ in self.cases:
            by_class[s["name"]] = by_class.get(s["name"], 0) + 1
        self.assertEqual(by_class, m110.D1_LE4)
        self.assertEqual(len(set(self.names)), 3876)
        self.assertTrue(all(s["dmeet"] == 1 for s, _ in self.cases))

    def test_m106b_cases_and_controls(self):
        for x in (m110.M106B_SAT,) + m110.M106B_UNKNOWN:
            self.assertIn(x, self.names)
        ctrl = [m102.inst_name(s, c) for s, c in m110.control_cases()]
        self.assertEqual(ctrl, list(m110.CONTROLS))
        self.assertEqual([s["dmeet"] for s, _ in m110.control_cases()], [3, 0, 1])

    def test_shards(self):
        parts = [m110.shard_cases(s) for s in m110.SHARDS]
        self.assertEqual([len(p) for p in parts], [m110.SIZE[s] for s in m110.SHARDS])
        seen = [m102.inst_name(s, c) for p in parts for s, c in p]
        self.assertEqual(sorted(seen), sorted(self.names))


if __name__ == "__main__":
    unittest.main()
