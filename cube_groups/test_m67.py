# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m67.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m55
import m57 as m
import m60
import m62
import m63
import m67


def fake_reps(group):
    """m55-shaped reps: the named rows where m55 has them, and a tail class whose ranks follow
    its GATE counts (rank 0 first, as m55's order does not matter to the plan)."""
    reps = {}
    for name, k, idx, rk, a1 in m67.REOPEN[group]:
        reps.setdefault(name, [None] * 2000)[k] = {"a1": a1, "rank_x1": rk, "index": idx,
                                                  "size": 1}
    tail = m67.TAIL[group]
    by = m67.GATE[tail]["by_rank"]
    reps[tail] = [{"a1": 0, "rank_x1": int(r), "index": i, "size": 1}
                  for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    return reps


class TestM67(unittest.TestCase):
    def test_installed(self):
        m67.install()
        self.assertIs(m.build_plain, m63.build_plain93)
        self.assertIs(m60.REOPEN, m67.REOPEN)
        self.assertIs(m60.GATE, m67.GATE)
        self.assertEqual(m60.REPS_FILE, "m67_reps.json")

    def test_lists(self):
        self.assertEqual(m67.REOPEN["a"], tuple(m63.TAIL_PLAIN["b"]))
        self.assertEqual(len(m67.REOPEN["b"]), 7)
        self.assertTrue(all(r[0] == m62.O0 and r[3] == 0 for r in m67.REOPEN["b"]))
        self.assertEqual(m67.M_BEFORE[m62.C2], (1827, 1822))
        for name, g in m67.GATE.items():
            self.assertEqual(sum(g["by_rank"].values()), g["orbits"])
            self.assertIn(name, m55.CLASSES)
        self.assertEqual(m67.planned_tail("a"), 1615)
        self.assertEqual(m67.planned_tail("b"), 1908)
        self.assertTrue(m67.drop_rank0("a"))
        self.assertFalse(m67.drop_rank0("b"))

    def test_named_ranks(self):
        for g in "ab":
            for name, k, idx, rk, a1 in m67.REOPEN[g]:
                self.assertEqual(m60.rank_on(a1, m55.CLASSES[name][1]), rk)

    def test_plan(self):
        for g in "ab":
            p = m67.plan(g, fake_reps(g))
            named = [e for e in p if e[4]]
            tail = [e[0] for e in p if not e[4]]
            self.assertEqual(len(named), 2 * len(m67.REOPEN[g]))
            self.assertTrue(all(e[4] for e in p[:len(named)]))
            self.assertEqual([e[1] for e in named[:2]], ["cadical", "xor"])
            self.assertTrue(all(bool(e[0].get("lemma93")) == (g == "b") for e in named))
            self.assertEqual(len(tail), m67.planned_tail(g))
            self.assertTrue(all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail))
            self.assertEqual(tail[0]["rank_x1"], 2)
            if g == "a":
                self.assertTrue(all(s["rank_x1"] > 0 for s in tail))
                self.assertTrue(all(s["name"].startswith("r3s_t7_B5_o020_c000_") for s in tail))
            else:
                self.assertEqual(sum(1 for s in tail if s.get("lemma93")), 251)
                self.assertTrue(tail[-1]["name"].startswith("r3l_t7_B5_o002_c001_"))
            self.assertEqual(len({s["name"] for s in tail}), len(tail))

    def test_speed(self):
        sp = m67.speed({})
        self.assertEqual(sp["controls"], 6)
        self.assertEqual(len(sp["ratios"]), 5)
        self.assertEqual(sp["median"], 0.337)
        self.assertEqual(sp["rule"], "adopt")
        slow = m67.speed({"r3l_t7_B5_o000_c000_a123": ("UNKNOWN", 300.0)})
        self.assertIn("r3l_t7_B5_o000_c000_a123", slow["slower_2x"])
        self.assertEqual(slow["rule"], "fact_only")

    def test_units(self):
        rep = {"a1": 262144, "rank_x1": 0, "index": 0, "size": 1}
        sp = m63.spec93(m67.O21, 0, rep)
        self.assertEqual(m63.lemma93_units(sp), 42)
        _, _, h, u = m.build(sp, "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B5"], 49 + 42))
        plain = m60.split_spec(m67.O20, 0, dict(rep, rank_x1=1))
        _, _, h, u = m.build(plain, "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B5"], 49))

    def write_run(self, d, g, reps, skip=0):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m67.REPS_FILE), "w") as f:
            json.dump(reps, f)
        p = [e for e in m67.plan(g, reps) if e[1] == "cadical"]
        for spec, arm, _, _, _ in p[:len(p) - skip]:
            with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade(self):
        for g in "ab":
            reps = fake_reps(g)
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps)
                out = m67.grade(g, d)
                self.assertTrue(out["tail"]["empty"])
                self.assertEqual(out["tail"]["open"], [])
                self.assertEqual(out["named_unsat"], len(m67.REOPEN[g]))
                self.assertFalse(out["any_sat_7"])
                self.assertIn(m67.TAIL[g], out["b5_closed"])
                if g == "a":
                    self.assertTrue(out["c2"]["empty"])
                    self.assertIn(m62.C2, out["b5_closed"])
                else:
                    self.assertEqual(out["speed"]["controls"], 13)
                    self.assertEqual(len(out["speed"]["ratios"]), 12)
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, skip=1)
                out = m67.grade(g, d)
                self.assertFalse(out["tail"]["empty"])
                self.assertEqual(out["tail"]["skipped"], 1)


if __name__ == "__main__":
    unittest.main()
