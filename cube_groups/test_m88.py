# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m88.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69
import m88


def fake_reps():
    """m66-shaped reps whose ranks follow the class's GATE counts."""
    name = m88.TAILS["a"][0]
    by = m88.GATE[name]["by_rank"]
    return {name: [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                   for i, r in enumerate(r for r in "012" for _ in range(by[r]))]}


class TestM88(unittest.TestCase):
    def test_installed(self):
        m88.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertEqual(m69.NAMED, {"a": (), "b": ()})
        self.assertIs(m69.TAILS, m88.TAILS)
        self.assertIs(m69.GATE, m88.GATE)
        self.assertIs(m69.SWEEP, m88.SWEEP)
        self.assertIs(m69.plan, m88._plan69)
        self.assertEqual(m69.REPS_FILE, "m88_reps.json")

    def test_lists(self):
        cl = m66.classes()
        tails = set(m88.TAILS["a"]) | set(m88.TAILS["b"])
        self.assertEqual(len(tails), 1)
        self.assertEqual(tails, set(m88.GATE))
        self.assertEqual(tails, set(m88.SWEEP))
        self.assertEqual(len(set(m88.CLOSED_SPLIT)), 39)
        self.assertEqual(len(m88.CLOSED_SPLIT), 39)
        self.assertEqual(len(set(m88.SPLIT_ELSEWHERE)), 7)
        self.assertFalse(set(m88.CLOSED_SPLIT) & set(m88.SPLIT_ELSEWHERE))
        self.assertFalse(tails & (set(m88.CLOSED_SPLIT) | set(m88.SPLIT_ELSEWHERE)))
        self.assertFalse(tails & (set(m58.CLOSED_KNOWN) | set(m69.CLOSED_M61B)))
        self.assertTrue(set(m88.CLOSED_SPLIT) | set(m88.SPLIT_ELSEWHERE) | tails <= set(cl))
        for name in tails:
            gate = m88.GATE[name]
            self.assertEqual(sum(gate["by_rank"].values()), gate["orbits"])
            self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], gate["d"])
            self.assertEqual(m66.HAND_ORDER[name], gate["order"])
            self.assertEqual(m66.HAND_ADM[gate["d"]], gate["valid"])
        self.assertFalse(any(m69.drop_rank0(n) for n in tails))

    def test_plan(self):
        reps = fake_reps()
        p = m69.plan("a", reps)
        gate = m88.GATE[m88.TAILS["a"][0]]
        self.assertFalse(any(e[4] for e in p))
        tail = [e[0] for e in p]
        self.assertEqual(len(tail), gate["orbits"])
        self.assertEqual(sum(1 for s in tail if s.get("lemma93")), gate["by_rank"]["0"])
        self.assertTrue(all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail))
        self.assertEqual(len({s["name"] for s in tail}), len(tail))
        self.assertEqual(tail[0]["rank_x1"], 2)
        self.assertEqual(tail[-1]["rank_x1"], 0)
        sp = next(s for s in tail if s.get("lemma93"))
        self.assertEqual(m69.lemma93_units(sp), 21)

    def write_run(self, d, reps, skip=0):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m69.REPS_FILE), "w") as f:
            json.dump(reps, f)
        p = m69.plan("a", reps)
        for spec, arm, _, _, _ in p[:len(p) - skip]:
            with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade(self):
        reps = fake_reps()
        name = m88.TAILS["a"][0]
        with tempfile.TemporaryDirectory() as d:
            self.write_run(d, reps)
            out = m88.grade("a", d)
            self.assertEqual(out["b6_closed"], [name])
            self.assertFalse(out["any_sat_7"])
            self.assertNotIn("o020", out)
            self.assertNotIn("b5_closed", out)
            self.assertIn("SUMMARY grade", m88.summary_line(out))
        with tempfile.TemporaryDirectory() as d:
            self.write_run(d, reps, skip=1)
            out = m88.grade("a", d)
            self.assertFalse(out["classes"][name]["empty"])
            self.assertEqual(out["classes"][name]["skipped"], 1)
            self.assertEqual(out["b6_closed"], [])


if __name__ == "__main__":
    unittest.main()
