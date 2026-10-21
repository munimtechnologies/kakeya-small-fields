# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m78.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m55
import m60
import m74
import m75
import m78


def fake_reps():
    """m55-shaped reps whose ranks follow the GATE counts of o005_c005 and o004_c001."""
    out = {}
    for name in (m78.O5, m78.O4):
        by = m75.GATE[name]["by_rank"]
        out[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                     for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    return out


class TestM78(unittest.TestCase):
    def setUp(self):
        m78.install()

    def test_installed(self):
        self.assertIs(m55.CLASSES, m74.CLASSES)
        self.assertEqual(m75.TAIL, m78.TAILS)
        self.assertIs(m75.plan, m78.first_arms)
        self.assertEqual(m75.REPS_FILE, "m78_reps.json")
        self.assertEqual(m75.SWEEP[m78.O5], "UNSAT")
        self.assertEqual(m75.GATE[m78.O5]["order"], m74.HAND_ORDER[m78.O5])
        self.assertEqual(m75.planned(m78.O5), m78.HALF)
        self.assertEqual(m75.planned(m78.O4), 1)

    def test_gate(self):
        g = m78.GATE_O5
        self.assertEqual(sum(g["by_rank"].values()), g["orbits"])
        self.assertGreaterEqual(g["orbits"], m74.HAND_LOWER[m78.O5])
        self.assertEqual(g["by_rank"]["1"] + g["by_rank"]["2"], 2 * m78.HALF)
        self.assertEqual(m78.REOPEN[0], m75.O4)

    def test_halves(self):
        reps = fake_reps()
        a = m78.plan("a", reps)
        b = m78.plan("b", reps)
        self.assertEqual((len(a), len(b)), (m78.HALF, m78.HALF))
        names = [e[0]["name"] for e in a + b]
        self.assertEqual(len(set(names)), 2 * m78.HALF)
        idx = {e[0]["m55_index"] for e in a + b}
        self.assertEqual(idx, {x["index"] for x in reps[m78.O5] if x["rank_x1"] > 0})
        for g, p in (("a", a), ("b", b)):
            ranks = [e[0]["rank_x1"] for e in p]
            self.assertEqual({r: ranks.count(r) for r in (2, 1)}, m78.half_ranks(g))
            self.assertEqual(ranks, sorted(ranks, reverse=True))
            self.assertTrue(all(e[1] == "cadical" and e[2] == m75.SPLIT_CAP and e[3] is None
                                and not e[4] for e in p))
            self.assertTrue(all(e[0]["parent"] == m78.O5 and e[0]["p"] == 5 for e in p))
        self.assertEqual(a[0][0]["rank_x1"], 2)
        self.assertEqual(b[-1][0]["rank_x1"], 1)
        self.assertEqual(m78.first_arms("a", reps), a)

    def test_rerun_plan(self):
        reps = fake_reps()
        p = m78.plan("r", reps)
        self.assertEqual([(e[1], e[2], e[3], e[4]) for e in p],
                         [("cadical", 300.0, None, True), ("xor", 300.0, "open", True)])
        self.assertEqual(p[0][0], p[1][0])
        self.assertIsNot(p[0][0], p[1][0])
        self.assertEqual(p[0][0]["name"], "r3s_t7_B5_o004_c001_a1240")
        self.assertEqual(p[0][0]["m55_index"], reps[m78.O4][1240]["index"])
        self.assertEqual(len(m78.first_arms("r", reps)), 1)

    def test_units(self):
        reps = fake_reps()
        for g in ("a", "r"):
            sp = m78.plan(g, reps)[0][0]
            for arm in ("cadical", "xor"):
                c, _, h, u = m.build(dict(sp), arm)
                self.assertEqual((h, u), (m.HAND_HINTS["B5"], m78.T * m78.T))
                self.assertTrue(m.units_consistent(c))

    def write_run(self, d, group, reps, statuses):
        """statuses: one status per plan entry (None: no file)."""
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m75.REPS_FILE), "w") as f:
            json.dump(reps, f)
        for (spec, arm, _, _, _), s in zip(m78.plan(group, reps), statuses):
            if s is not None:
                with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                    json.dump({"status": s, "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade_halves(self):
        reps = fake_reps()
        for g in ("a", "b"):
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, ["UNSAT"] * m78.HALF)
                out = m78.grade(g, d)
                self.assertTrue(out["part"]["all_unsat"])
                self.assertEqual(out["part"]["unsat"], m78.HALF)
                self.assertEqual(out["part"]["median_unsat_wall"], 1.0)
                self.assertEqual(len(out["part"]["slowest_ten_m55_index"]), 10)
                self.assertFalse(out["any_sat_7"])
                self.assertIn("SUMMARY grade", m78.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, ["UNSAT"] * (m78.HALF - 2) + ["UNKNOWN", None])
                out = m78.grade(g, d)
                self.assertFalse(out["part"]["all_unsat"])
                self.assertEqual(len(out["part"]["open"]), 2)
                self.assertEqual(out["part"]["skipped"], 1)

    def test_grade_rerun(self):
        reps = fake_reps()
        for statuses, ok in ((["UNSAT", None], True), (["UNKNOWN", "UNSAT"], True),
                             (["UNKNOWN", "UNKNOWN"], False), ([None, None], False)):
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, "r", reps, statuses)
                out = m78.grade("r", d)
                self.assertEqual(out["part"]["all_unsat"], ok, statuses)
                self.assertEqual(out["part"]["planned"], 1)
        with tempfile.TemporaryDirectory() as d:
            out = m78.grade("r", d)
            self.assertEqual(out["ungraded"], {"check": "missing"})
            self.assertIn("SUMMARY grade", m78.summary_line(out))

    def test_solve_skips_decided_xor(self):
        reps = fake_reps()
        calls = []
        real = m.solve_one
        try:
            for first in ("UNSAT", "UNKNOWN"):
                calls.clear()
                m.solve_one = lambda spec, arm, budget, out_dir, s=first: (
                    calls.append((arm, budget)) or {"status": s if arm == "cadical" else "UNSAT"})
                with tempfile.TemporaryDirectory() as d:
                    self.write_run(d, "r", reps, [None, None])
                    m78.run_solve("r", 150 * 60, d)
                want = [("cadical", 300.0)] if first == "UNSAT" else [("cadical", 300.0),
                                                                      ("xor", 300.0)]
                self.assertEqual(calls, want)
        finally:
            m.solve_one = real

    def test_rank_functions_agree(self):
        for a1 in (0, 1 << 1, (1 << 1) | (1 << 9), m78.REOPEN[4]):
            self.assertEqual(m60.rank_on(a1, m55.ALPHA), m.rank_on_x1(a1))


if __name__ == "__main__":
    unittest.main()
