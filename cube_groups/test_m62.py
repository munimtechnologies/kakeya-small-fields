# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m62.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import random
import tempfile
import unittest

import m55
import m57 as m
import m60
import m62


class TestM62(unittest.TestCase):
    def test_installed(self):
        m62.install()
        self.assertIs(m60.REOPEN, m62.REOPEN)
        self.assertIs(m60.M59B, m62.M60)
        self.assertIs(m60.TAIL, m62.TAIL)
        self.assertIs(m60.GATE, m62.GATE)
        self.assertEqual(m60.REPS_FILE, m62.REPS_FILE)

    def test_reopen_lists(self):
        a, b = m62.REOPEN["a"], m62.REOPEN["b"]
        self.assertEqual(len(a), len(b))
        keys = [(n, k) for n, k, *_ in a + b]
        self.assertEqual(len(set(keys)), len(keys))
        for name, (total, unsat) in m62.M60.items():
            self.assertEqual(sum(1 for n, *_ in a + b if n == name), total - unsat)
        for name, k, idx, rk, a1 in a + b:
            au, x1, rb = m55.CLASSES[name]
            self.assertTrue(m60.admissible(a1, au, x1, rb))
            self.assertEqual(m60.rank_on(a1, x1), rk)
            self.assertEqual(m55.Maps(x1, rb).index(m55.cols_of(a1)), idx)
            self.assertLess(k, m62.GATE[name]["orbits"])

    def test_gate_sums(self):
        for name, g in m62.GATE.items():
            self.assertIn(name, m55.CLASSES)
            self.assertEqual(sum(g["by_rank"].values()), g["orbits"])

    def test_classes_of(self):
        m62.install()
        self.assertEqual(m60.classes_of("a"), [m62.O32, m62.O0, m62.C1])
        self.assertEqual(m60.classes_of("b"), [m62.O0, m62.C2])

    def test_split_spec(self):
        rep = {"a1": 1 << 48, "rank_x1": 1, "index": 2097152, "size": 1}
        sp = m60.split_spec(m62.O32, 574, rep)
        self.assertEqual(sp["name"], "r3s_t7_B5_o032_c000_a574")
        self.assertEqual((sp["pair"], sp["cls"], sp["parent"]), (32, 0, m62.O32))
        self.assertEqual(sp["x1"], list(m55.BETA))

    def fake_reps(self, group):
        rng = random.Random(4)
        return {name: [{"a1": k + 1, "rank_x1": rng.randrange(3), "index": k, "size": 1}
                       for k in range(600)] for name in m60.classes_of(group)}

    def test_plan(self):
        m62.install()
        for g in "ab":
            reps = self.fake_reps(g)
            p = m60.plan(g, reps)
            named = [e for e in p if e[4]]
            self.assertEqual(len(named), 2 * len(m62.REOPEN[g]))
            self.assertEqual(p[:len(named)], named)
            tail = [e for e in p if not e[4]]
            self.assertEqual(len(tail), 600)
            self.assertTrue(all(e[0]["parent"] == m62.TAIL[g] for e in tail))

    def test_grade_counts(self):
        m62.install()
        with tempfile.TemporaryDirectory() as d:
            reps = self.fake_reps("a")
            with open(os.path.join(d, m62.REPS_FILE), "w") as f:
                json.dump(reps, f)
            for spec, arm, _, _, named in m60.plan("a", reps):
                if arm == "xor":
                    continue
                with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                    json.dump({"status": "UNSAT", "wall_seconds": 1.0}, f)
            out = m60.grade("a", d)
            self.assertEqual(out["reopen_unsat"], 7)
            self.assertTrue(out["class_unsat"][m62.O32]["empty"])
            self.assertEqual(out["class_unsat"][m62.O0]["unsat"], 664)
            self.assertFalse(out["class_unsat"][m62.O0]["empty"])
            self.assertEqual(out["tail"]["unsat"], 600)
            self.assertFalse(out["tail"]["empty"])
            self.assertEqual(out["b5_closed"], [m62.O32])


if __name__ == "__main__":
    unittest.main()
