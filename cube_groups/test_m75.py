# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m75.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m55
import m60
import m74
import m75


def fake_reps(group):
    """m55-shaped reps whose ranks follow the GATE counts of the group's class."""
    name = m75.TAIL[group]
    by = m75.GATE[name]["by_rank"]
    return {name: [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                   for i, r in enumerate(r for r in "012" for _ in range(by[r]))]}


class TestM75(unittest.TestCase):
    def test_installed(self):
        m75.install()
        self.assertIs(m55.CLASSES, m74.CLASSES)
        self.assertIs(m55.HAND_ORDER, m74.HAND_ORDER)
        for name in m75.TAIL.values():
            self.assertIn(name, m55.CLASSES)
        self.assertIn(m75.O5, m55.CLASSES)
        self.assertEqual(m75.REPS_FILE, "m75_reps.json")

    def test_lists(self):
        tails = set(m75.TAIL.values())
        self.assertEqual(len(tails), 2)
        self.assertNotIn(m75.O5, tails)
        self.assertEqual(tails, set(m75.GATE))
        self.assertEqual(tails, set(m75.SWEEP))
        self.assertTrue(all(v == "UNSAT" for v in m75.SWEEP.values()))
        for name in tails:
            gate = m75.GATE[name]
            self.assertEqual(sum(gate["by_rank"].values()), gate["orbits"])
            self.assertEqual(gate["order"], m74.HAND_ORDER[name])
            self.assertGreaterEqual(gate["orbits"], m74.HAND_LOWER[name])
            self.assertEqual(m75.planned(name), gate["by_rank"]["1"] + gate["by_rank"]["2"])
            self.assertEqual(m.pair_cls(name), (int(name[11:14]), int(name[16:19])))
        self.assertEqual(m75.ADM, m55.HAND_VALID[m55.ALPHA])

    def test_plan(self):
        for g in ("a", "b"):
            name = m75.TAIL[g]
            p = m75.plan(g, fake_reps(g))
            specs = [e[0] for e in p]
            self.assertEqual(len(specs), m75.planned(name))
            self.assertFalse(any(e[4] for e in p))
            self.assertTrue(all(e[1] == "cadical" and e[2] == m75.SPLIT_CAP for e in p))
            self.assertTrue(all(s["rank_x1"] > 0 and not s.get("lemma93") for s in specs))
            self.assertEqual(len({s["name"] for s in specs}), len(specs))
            self.assertTrue(all(s["parent"] == name and s["p"] == 5 and s["kind"] == "main"
                                for s in specs))
            self.assertEqual(specs[0]["rank_x1"], 2)
            self.assertEqual(specs[-1]["rank_x1"], 1)
            self.assertTrue(specs[0]["name"].startswith("r3s_t7_B5_" + name[10:] + "_a"))
            au, x1, rb = m55.CLASSES[name]
            self.assertEqual((specs[0]["au"], specs[0]["x1"], specs[0]["r"]),
                             (au, list(x1), list(rb)))

    def test_units(self):
        for g in ("a", "b"):
            sp = m75.plan(g, fake_reps(g))[0][0]
            for arm in ("cadical", "xor"):
                c, _, h, u = m.build(dict(sp), arm)
                self.assertEqual((h, u), (m.HAND_HINTS["B5"], m75.T * m75.T))
                self.assertTrue(m.units_consistent(c))

    def test_rank_functions_agree(self):
        x1 = m55.ALPHA
        for a1 in (0, 1 << 1, (1 << 1) | (1 << 9), (1 << 1) | (1 << 9) | (1 << 17), 1 << 5):
            self.assertEqual(m60.rank_on(a1, x1), m.rank_on_x1(a1))

    def write_run(self, d, group, reps, skip=0):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m75.REPS_FILE), "w") as f:
            json.dump(reps, f)
        p = m75.plan(group, reps)
        for spec, arm, _, _, _ in p[:len(p) - skip]:
            with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade(self):
        for g in ("a", "b"):
            name = m75.TAIL[g]
            reps = fake_reps(g)
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps)
                out = m75.grade(g, d)
                self.assertEqual(out["b5_closed"], [name])
                self.assertTrue(out["tail"]["empty"])
                self.assertFalse(out["any_sat_7"])
                self.assertEqual(out["tail"]["median_unsat_wall"], 1.0)
                self.assertEqual(len(out["tail"]["slowest_ten_m55_index"]), 10)
                self.assertEqual(out["tail"]["unsat"], m75.planned(name))
                self.assertIn("SUMMARY grade", m75.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, skip=1)
                out = m75.grade(g, d)
                self.assertFalse(out["tail"]["empty"])
                self.assertEqual(out["tail"]["skipped"], 1)
                self.assertEqual(out["b5_closed"], [])
                self.assertEqual(len(out["tail"]["open"]), 1)
                self.assertIn("SUMMARY grade", m75.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                out = m75.grade(g, d)
                self.assertEqual(out["ungraded"], {"check": "missing"})
                self.assertEqual(out["b5_closed"], [])


if __name__ == "__main__":
    unittest.main()
