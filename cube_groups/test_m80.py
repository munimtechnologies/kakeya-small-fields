# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m80.py. Hand counts are not tested here; the check part grades them."""
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
import m80


def fake_reps():
    """m55-shaped reps whose ranks follow the GATE counts of o005_c005."""
    by = m78.GATE_O5["by_rank"]
    return {m80.O5: [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                     for i, r in enumerate(r for r in "012" for _ in range(by[r]))]}


class TestM80(unittest.TestCase):
    def setUp(self):
        m80.install()

    def test_installed(self):
        self.assertIs(m55.CLASSES, m74.CLASSES)
        self.assertEqual(m75.TAIL, {"r": m80.O5})
        self.assertEqual(m78.TAILS, {"r": m80.O5})
        self.assertIs(m78.plan, m80.plan)
        self.assertIs(m75.plan, m78.first_arms)
        self.assertEqual(m75.REPS_FILE, "m80_reps.json")
        self.assertEqual(m75.SWEEP[m80.O5], "UNSAT")
        self.assertEqual(m75.planned(m80.O5), 7)
        self.assertEqual(m78.PLANNED, {"r": 7})

    def test_reopen(self):
        ks = [r[0] for r in m80.REOPEN]
        self.assertEqual(len(set(ks)), 7)
        self.assertEqual(ks, sorted(ks))
        self.assertEqual(len({r[1] for r in m80.REOPEN}), 7)
        self.assertEqual(len({r[3] for r in m80.REOPEN}), 7)
        self.assertTrue(all(r[2] == 1 for r in m80.REOPEN))
        self.assertTrue(all(0 <= k < m78.GATE_O5["orbits"] for k in ks))
        for _, _, rk, a1 in m80.REOPEN:
            self.assertEqual(m60.rank_on(a1, m55.ALPHA), rk)
            self.assertEqual(m.rank_on_x1(a1), rk)

    def test_rerun_plan(self):
        reps = fake_reps()
        p = m80.plan("r", reps)
        self.assertEqual(len(p), 14)
        for i, (k, _, _, _) in enumerate(m80.REOPEN):
            c, x = p[2 * i], p[2 * i + 1]
            self.assertEqual((c[1], c[2], c[3], c[4]), ("cadical", 300.0, None, True))
            self.assertEqual((x[1], x[2], x[3], x[4]), ("xor", 300.0, "open", True))
            self.assertEqual(c[0], x[0])
            self.assertIsNot(c[0], x[0])
            self.assertEqual(c[0]["name"], f"r3s_t7_B5_o005_c005_a{k:03d}")
            self.assertEqual(c[0]["m55_index"], reps[m80.O5][k]["index"])
            self.assertEqual(c[0]["parent"], m80.O5)
            self.assertEqual(c[0]["p"], 5)
        first = m78.first_arms("r", reps)
        self.assertEqual(len(first), 7)
        self.assertTrue(all(e[1] == "cadical" for e in first))
        ranks = [e[0]["rank_x1"] for e in first]
        self.assertEqual(ranks, sorted(ranks, reverse=True))

    def test_units(self):
        sp = m80.plan("r", fake_reps())[0][0]
        for arm in ("cadical", "xor"):
            c, _, h, u = m.build(dict(sp), arm)
            self.assertEqual((h, u), (m.HAND_HINTS["B5"], m80.T * m80.T))
            self.assertTrue(m.units_consistent(c))

    def write_run(self, d, reps, statuses):
        """statuses: one status per plan entry (None: no file)."""
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m75.REPS_FILE), "w") as f:
            json.dump(reps, f)
        for (spec, arm, _, _, _), s in zip(m80.plan("r", reps), statuses):
            if s is not None:
                with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                    json.dump({"status": s, "wall_seconds": 1.0, "budget_seconds": 300.0}, f)

    def test_grade(self):
        reps = fake_reps()
        cases = ((["UNSAT", None] * 7, True, 0),
                 (["UNKNOWN", "UNSAT"] * 7, True, 0),
                 (["UNSAT", None] * 6 + ["UNKNOWN", "UNKNOWN"], False, 1),
                 (["UNSAT", None] * 6 + [None, None], False, 1))
        for statuses, ok, n_open in cases:
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, reps, statuses)
                out = m80.grade("r", d)
                self.assertEqual(out["part"]["all_unsat"], ok, statuses)
                self.assertEqual(out["part"]["planned"], 7)
                self.assertEqual(out["part"]["name"], m80.O5)
                self.assertEqual(len(out["part"]["open"]), n_open)
                self.assertFalse(out["any_sat_7"])
                self.assertIn("SUMMARY grade", m78.summary_line(out))
        with tempfile.TemporaryDirectory() as d:
            out = m80.grade("r", d)
            self.assertEqual(out["ungraded"], {"check": "missing"})

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
                    self.write_run(d, reps, [None] * 14)
                    m78.run_solve("r", 75 * 60, d)
                want = ([("cadical", 300.0)] if first == "UNSAT"
                        else [("cadical", 300.0), ("xor", 300.0)]) * 7
                self.assertEqual(calls, want)
        finally:
            m.solve_one = real


if __name__ == "__main__":
    unittest.main()
