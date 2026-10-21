# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m81.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69
import m81


def fake_reps(group):
    """m66-shaped reps whose ranks follow the GATE counts of the group's classes."""
    reps = {}
    for name in m81.TAILS[group]:
        by = m81.GATE[name]["by_rank"]
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                      for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    return reps


class TestM81(unittest.TestCase):
    def test_installed(self):
        m81.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertEqual(m69.NAMED, {"a": (), "b": ()})
        self.assertIs(m69.TAILS, m81.TAILS)
        self.assertIs(m69.GATE, m81.GATE)
        self.assertIs(m69.SWEEP, m81.SWEEP)
        self.assertEqual(m69.REPS_FILE, "m81_reps.json")

    def test_lists(self):
        cl = m66.classes()
        tails = set(m81.TAILS["a"]) | set(m81.TAILS["b"])
        self.assertFalse(set(m81.TAILS["a"]) & set(m81.TAILS["b"]))
        self.assertEqual(tails, set(m81.GATE))
        self.assertEqual(tails, set(m81.SWEEP))
        self.assertEqual(len(set(m81.CLOSED_SPLIT)), 27)
        self.assertEqual(len(set(m81.QUEUED_SPLIT)), 3)
        self.assertFalse(set(m81.CLOSED_SPLIT) & set(m81.QUEUED_SPLIT))
        self.assertFalse(tails & (set(m81.CLOSED_SPLIT) | set(m81.QUEUED_SPLIT)))
        self.assertFalse(tails & (set(m58.CLOSED_KNOWN) | set(m69.CLOSED_M61B)))
        self.assertTrue(set(m81.CLOSED_SPLIT) | set(m81.QUEUED_SPLIT) <= set(cl))
        for name in tails:
            self.assertIn(name, cl)
            gate = m81.GATE[name]
            self.assertEqual(sum(gate["by_rank"].values()), gate["orbits"])
            self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], gate["d"])
            self.assertEqual(m66.HAND_ORDER[name], gate["order"])
            self.assertEqual(m66.HAND_ADM[gate["d"]], gate["valid"])
            self.assertEqual(m66.HAND_ORBITS_D0.get(name, gate["orbits"]), gate["orbits"])
        self.assertFalse(any(m69.drop_rank0(n) for n in tails))

    def test_plan(self):
        for g in ("a", "b"):
            reps = fake_reps(g)
            p = m69.plan(g, reps)
            self.assertFalse(any(e[4] for e in p))
            tail = [e[0] for e in p]
            self.assertTrue(all(e[1] == "cadical" and e[2] == m69.SPLIT_CAP for e in p))
            self.assertEqual(len(tail), sum(m69.planned(n) for n in m81.TAILS[g]))
            self.assertEqual(len(tail), 3839)
            self.assertEqual(sum(1 for s in tail if s.get("lemma93")), 255)
            self.assertTrue(all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail))
            self.assertTrue(all(s["name"].startswith("r3l_") == (s["rank_x1"] == 0) for s in tail))
            self.assertEqual(len({s["name"] for s in tail}), len(tail))
            self.assertEqual(tail[0]["parent"], m81.TAILS[g][0])
            self.assertEqual(tail[0]["rank_x1"], 2)
            self.assertEqual(tail[-1]["rank_x1"], 0)

    def test_units(self):
        for g in ("a", "b"):
            p = m69.plan(g, fake_reps(g))
            sp = p[0][0]
            _, _, h, u = m.build(dict(sp), "cadical")
            self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49))
            sl = p[-1][0]
            self.assertTrue(sl.get("lemma93"))
            self.assertEqual(m69.lemma93_units(sl), 21)
            _, _, h, u = m.build(dict(sl), "cadical")
            self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49 + 21))

    def write_run(self, d, group, reps, skip=0):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m69.REPS_FILE), "w") as f:
            json.dump(reps, f)
        p = m69.plan(group, reps)
        for spec, arm, _, _, _ in p[:len(p) - skip]:
            with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade(self):
        for g in ("a", "b"):
            reps = fake_reps(g)
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps)
                out = m81.grade(g, d)
                self.assertEqual(out["b6_closed"], list(m81.TAILS[g]))
                self.assertFalse(out["any_sat_7"])
                for key in ("o020", "b5_closed", "named", "named_unsat"):
                    self.assertNotIn(key, out)
                self.assertTrue(all(c["median_unsat_wall"] == 1.0 for c in out["classes"].values()))
                self.assertIn("SUMMARY grade", m81.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, skip=1)
                out = m81.grade(g, d)
                last = m81.TAILS[g][-1]
                self.assertFalse(out["classes"][last]["empty"])
                self.assertEqual(out["classes"][last]["skipped"], 1)
                self.assertNotIn(last, out["b6_closed"])
                self.assertIn("SUMMARY grade", m81.summary_line(out))


if __name__ == "__main__":
    unittest.main()
