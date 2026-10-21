# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m77.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69
import m77


def fake_reps(group):
    """m66-shaped reps whose ranks follow the GATE counts of the group's classes."""
    reps = {}
    for name in m77.TAILS[group]:
        by = m77.GATE[name]["by_rank"]
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                      for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    return reps


class TestM77(unittest.TestCase):
    def test_installed(self):
        m77.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertEqual(m69.NAMED, {"a": (), "b": ()})
        self.assertIs(m69.TAILS, m77.TAILS)
        self.assertIs(m69.GATE, m77.GATE)
        self.assertIs(m69.SWEEP, m77.SWEEP)
        self.assertEqual(m69.REPS_FILE, "m77_reps.json")

    def test_lists(self):
        cl = m66.classes()
        tails = set(m77.TAILS["a"]) | set(m77.TAILS["b"])
        self.assertFalse(set(m77.TAILS["a"]) & set(m77.TAILS["b"]))
        self.assertEqual(tails, set(m77.GATE))
        self.assertEqual(tails, set(m77.SWEEP))
        self.assertEqual(len(m77.CLOSED_SPLIT), 18)
        self.assertEqual(len(m77.SPLIT_ELSEWHERE), 7)
        before = set(m77.CLOSED_SPLIT) | set(m77.SPLIT_ELSEWHERE)
        self.assertEqual(len(before), 25)
        self.assertFalse(tails & before)
        self.assertFalse(tails & (set(m58.CLOSED_KNOWN) | set(m69.CLOSED_M61B)))
        self.assertTrue(before <= set(cl))
        for name in tails:
            self.assertIn(name, cl)
            gate = m77.GATE[name]
            self.assertEqual(sum(gate["by_rank"].values()), gate["orbits"])
            self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], gate["d"])
            self.assertEqual(m66.HAND_ORDER[name], gate["order"])
            self.assertEqual(m66.HAND_ADM[gate["d"]], gate["valid"])
            self.assertEqual(m66.HAND_ORBITS_D0.get(name, gate["orbits"]), gate["orbits"])
        self.assertTrue(all(m69.drop_rank0(n) for n in tails))

    def test_plan(self):
        for g, tail_len in (("a", 3584), ("b", 3584)):
            reps = fake_reps(g)
            p = m69.plan(g, reps)
            self.assertFalse(any(e[4] for e in p))
            tail = [e[0] for e in p]
            self.assertTrue(all(e[1] == "cadical" and e[2] == m69.SPLIT_CAP for e in p))
            self.assertEqual(len(tail), sum(m69.planned(n) for n in m77.TAILS[g]))
            self.assertEqual(len(tail), tail_len)
            self.assertTrue(all(s["rank_x1"] > 0 and not s.get("lemma93") for s in tail))
            self.assertEqual(len({s["name"] for s in tail}), len(tail))
            self.assertEqual(tail[0]["parent"], m77.TAILS[g][0])
            self.assertEqual(tail[0]["rank_x1"], 2)
            self.assertEqual(tail[-1]["parent"], m77.TAILS[g][-1])
            self.assertEqual(tail[-1]["rank_x1"], 1)

    def test_units(self):
        for g in ("a", "b"):
            sp = m69.plan(g, fake_reps(g))[0][0]
            _, _, h, u = m.build(dict(sp), "cadical")
            self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49))

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
                out = m77.grade(g, d)
                self.assertEqual(out["b6_closed"], list(m77.TAILS[g]))
                self.assertFalse(out["any_sat_7"])
                for key in ("o020", "b5_closed", "named", "named_unsat"):
                    self.assertNotIn(key, out)
                self.assertTrue(all(c["median_unsat_wall"] == 1.0 for c in out["classes"].values()))
                self.assertIn("SUMMARY grade", m77.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, skip=1)
                out = m77.grade(g, d)
                last = m77.TAILS[g][-1]
                self.assertFalse(out["classes"][last]["empty"])
                self.assertEqual(out["classes"][last]["skipped"], 1)
                self.assertNotIn(last, out["b6_closed"])
                self.assertIn("SUMMARY grade", m77.summary_line(out))


if __name__ == "__main__":
    unittest.main()
