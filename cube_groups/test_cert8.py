# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert8.py that need neither CaDiCaL nor drat-trim; the check part runs cert1's
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert8
import m57 as m
import m69
import m83


def fake_reps(group):
    """m66-shaped roots of the group's classes: rank 2 except at m83's rows, which carry their
    values."""
    reps = {}
    for name in cert8.classes(group):
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(m83.NAMED_GATE[name]["orbits"])]
    for name, k, rk, index, size, a1 in cert8.rows(group):
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert8(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_groups(self):
        self.assertTrue(cert8.groups_ok())
        self.assertEqual([len(cert8.rows(g)) for g in ("a", "b")], [26, 27])
        self.assertEqual(cert8.classes("a"), ["r3b_t7_B6_o009_c005", "r3b_t7_B6_o010_c003"])
        self.assertEqual(cert8.classes("b"), ["r3b_t7_B6_o009_c006", "r3b_t7_B6_o010_c005"])
        self.assertEqual(cert8.per_class("a"),
                         {"r3b_t7_B6_o009_c005": 11, "r3b_t7_B6_o010_c003": 15})
        self.assertEqual(cert8.per_class("b"),
                         {"r3b_t7_B6_o009_c006": 16, "r3b_t7_B6_o010_c005": 11})
        self.assertEqual(sorted(cert8.M83_PROBES), ["a", "b"])
        self.assertEqual(sorted(cert8.M83_PROBES["a"]), ["l"])
        self.assertEqual(sorted(cert8.M83_PROBES["b"]), ["l", "s"])

    def test_specs(self):
        for g in ("a", "b"):
            specs = cert8.group_specs(g, fake_reps(g))
            self.assertTrue(cert8.specs_ok(g, specs))
            self.assertFalse(cert8.specs_ok(g, specs[:-1]))
            self.assertEqual(sum(bool(sp.get("lemma93")) for sp in specs),
                             m83.NAMED_RANKS[g][0])
        a = cert8.group_specs("a", fake_reps("a"))
        self.assertTrue(all(sp.get("lemma93") for sp in a))
        self.assertEqual((a[0]["name"], a[-1]["name"]),
                         ("r3l_t7_B6_o009_c005_a1160", "r3l_t7_B6_o010_c003_a1973"))
        bb = cert8.group_specs("b", fake_reps("b"))
        self.assertEqual((bb[0]["name"], bb[-1]["name"]),
                         ("r3s_t7_B6_o009_c006_a0003", "r3l_t7_B6_o010_c005_a1974"))
        self.assertEqual([sp["name"] for sp in bb if not sp.get("lemma93")],
                         ["r3s_t7_B6_o009_c006_a0003", "r3s_t7_B6_o009_c006_a3209"])
        bad = fake_reps("b")
        row = bad["r3b_t7_B6_o010_c005"][1974]
        bad["r3b_t7_B6_o010_c005"][1974] = dict(row, a1=row["a1"] ^ 2)
        self.assertFalse(cert8.specs_ok("b", cert8.group_specs("b", bad)))

    def test_grade(self):
        specs = cert8.group_specs("b", fake_reps("b"))
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert8.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                row = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                       "cadical": {"status": "UNSAT", "seconds": 5.0 if i == 3 else 1.0},
                       "drat": {"verified": True, "seconds": 50.0 if i == 4 else 2.0},
                       "proof_bytes": 100 + i, "cnf_sha256": "0" * 64}
                with open(os.path.join(d, f"cert8_{sp['name']}.json"), "w") as f:
                    json.dump(row, f)
            out = cert8.grade("b", d)
            self.assertEqual(out["instances"], 27)
            self.assertEqual(out["verified"], 26)
            self.assertEqual(out["not_verified"], ["r3s_t7_B6_o009_c006_a0003"])
            self.assertEqual(out["counts"], {"VERIFIED": 26, "MISSING": 1})
            self.assertEqual(out["by_class"],
                             {"r3b_t7_B6_o009_c006": {"instances": 16, "verified": 15},
                              "r3b_t7_B6_o010_c005": {"instances": 11, "verified": 11}})
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (30.0, 100.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 125])
            self.assertEqual(out["slowest"], [specs[4]["name"], 5.0, 2.0])
            self.assertEqual(len(out["rows"]), 27)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade group b", cert8.summary_line(out))


if __name__ == "__main__":
    unittest.main()
