# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m60.py. Hand counts are not tested here; the check part grades them."""
import os
import random
import tempfile
import unittest

import m55
import m57 as m
import m60


class TestM60(unittest.TestCase):
    def test_mask_round_trip(self):
        rng = random.Random(1)
        for _ in range(200):
            cols = tuple(rng.randrange(128) for _ in range(m60.T))
            self.assertEqual(m55.cols_of(m60.mask_of(cols)), cols)

    def test_rank_on_alpha_is_m57(self):
        rng = random.Random(2)
        for _ in range(300):
            a = rng.getrandbits(49)
            self.assertEqual(m60.rank_on(a, m55.ALPHA), m.rank_on_x1(a))

    def test_rank_on_beta_uses_e6(self):
        # A e_6 = e_3 has rank 1 on span(e_0, e_1, e_2, e_6) and 0 on columns 0 to 3; A e_3 = e_4
        # the other way round.
        a = m60.mask_of((0, 0, 0, 0, 0, 0, 8))
        self.assertEqual(m60.rank_on(a, m55.BETA), 1)
        self.assertEqual(m.rank_on_x1(a), 0)
        b = m60.mask_of((0, 0, 0, 16, 0, 0, 0))
        self.assertEqual(m60.rank_on(b, m55.BETA), 0)
        self.assertEqual(m.rank_on_x1(b), 1)

    def test_rank_on_matches_m55_maps(self):
        rng = random.Random(3)
        for name in (m60.TAIL["a"], m60.TAIL["b"], m60.O1):
            _, x1, rb = m55.CLASSES[name]
            mp = m55.Maps(x1, rb)
            for _ in range(200):
                idx = rng.randrange(1 << m55.NBITS)
                self.assertEqual(m60.rank_on(m60.mask_of(mp.cols(idx)), x1), mp.rank_x1(idx))

    def test_reopen_lists(self):
        a, b = m60.REOPEN["a"], m60.REOPEN["b"]
        self.assertEqual(len(a), len(b))
        keys = [(n, k) for n, k, *_ in a + b]
        self.assertEqual(len(set(keys)), len(keys))
        for name, (total, unsat) in m60.M59B.items():
            self.assertEqual(sum(1 for n, *_ in a + b if n == name), total - unsat)
        for name, k, idx, rk, a1 in a + b:
            au, x1, rb = m55.CLASSES[name]
            self.assertTrue(m60.admissible(a1, au, x1, rb))
            self.assertEqual(m60.rank_on(a1, x1), rk)
            self.assertEqual(m55.Maps(x1, rb).index(m55.cols_of(a1)), idx)

    def test_classes_of(self):
        self.assertEqual(m60.classes_of("a"), [m60.O1, m60.O2, m60.TAIL["a"]])
        self.assertEqual(m60.classes_of("b"), [m60.O2, m60.TAIL["b"]])
        for g in "ab":
            for name in m60.classes_of(g):
                self.assertIn(name, m60.GATE)
                self.assertIn(name, m55.CLASSES)

    def test_split_spec(self):
        rep = {"a1": 64, "rank_x1": 0, "index": 32768, "size": 2}
        sp = m60.split_spec(m60.O2, 161, rep)
        self.assertEqual(sp["name"], "r3s_t7_B5_o002_c000_a161")
        self.assertEqual((sp["p"], sp["pair"], sp["cls"], sp["parent"]), (5, 2, 0, m60.O2))
        self.assertEqual(sp["au"], m55.CLASSES[m60.O2][0])

    def fake_reps(self, group):
        rng = random.Random(4)
        reps = {}
        for name in m60.classes_of(group):
            reps[name] = [{"a1": k + 1, "rank_x1": rng.randrange(3), "index": k, "size": 1}
                          for k in range(400)]
        return reps

    def test_plan(self):
        for g in "ab":
            reps = self.fake_reps(g)
            p = m60.plan(g, reps)
            named = [e for e in p if e[4]]
            self.assertEqual(len(named), 2 * len(m60.REOPEN[g]))
            self.assertTrue(all(e[2] == m60.NAMED_CAP for e in named))
            for i in range(0, len(named), 2):
                self.assertEqual(named[i][0]["name"], named[i + 1][0]["name"])
                self.assertEqual((named[i][1], named[i + 1][1]), ("cadical", "xor"))
                self.assertEqual(named[i + 1][3], "open")
            self.assertEqual(p[:len(named)], named)
            tail = [e for e in p if not e[4]]
            self.assertEqual(len(tail), len(reps[m60.TAIL[g]]))
            ranks = [e[0]["rank_x1"] for e in tail]
            self.assertEqual(ranks, sorted(ranks, reverse=True))
            self.assertTrue(all(e[1] == "cadical" and e[2] == m60.SPLIT_CAP for e in tail))

    def test_grade_without_check(self):
        with tempfile.TemporaryDirectory() as d:
            out = m60.grade("a", d)
            self.assertIn("check", out["ungraded"])
            self.assertIn("reps", out["ungraded"])
            self.assertFalse(out["any_sat_7"])

    def test_grade_counts(self):
        import json
        with tempfile.TemporaryDirectory() as d:
            reps = self.fake_reps("a")
            with open(os.path.join(d, m60.REPS_FILE), "w") as f:
                json.dump(reps, f)
            for spec, arm, _, _, named in m60.plan("a", reps):
                if arm == "xor":
                    continue
                with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                    json.dump({"status": "UNSAT", "wall_seconds": 1.0}, f)
            out = m60.grade("a", d)
            self.assertEqual(out["reopen_unsat"], len(m60.REOPEN["a"]))
            self.assertEqual(out["reopen_open"], [])
            self.assertTrue(out["class_unsat"][m60.O1]["empty"])
            self.assertFalse(out["class_unsat"][m60.O2]["empty"])
            self.assertEqual(out["tail"]["unsat"], 400)
            self.assertFalse(out["tail"]["empty"])


if __name__ == "__main__":
    unittest.main()
