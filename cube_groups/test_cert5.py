# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert5.py that need neither CaDiCaL nor drat-trim; the check part runs cert1's
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert5
import m57 as m
import m69
import m87


def fake_reps(group):
    """m66-shaped roots of the group's classes: rank 2 except at m87's rows, which carry their
    values."""
    reps = {}
    for name in cert5.classes(group):
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(m87.NAMED_GATE[name]["orbits"])]
    for name, k, rk, index, size, a1 in cert5.rows(group):
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert5(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_groups(self):
        self.assertTrue(cert5.groups_ok())
        self.assertEqual([len(cert5.rows(g)) for g in ("a", "b")], [20, 25])
        self.assertEqual(cert5.classes("a"), ["r3b_t7_B6_o010_c001"])
        self.assertEqual(cert5.classes("b"), ["r3b_t7_B6_o010_c008", "r3b_t7_B6_o005_c002"])
        self.assertEqual(cert5.per_class("b"),
                         {"r3b_t7_B6_o010_c008": 15, "r3b_t7_B6_o005_c002": 10})
        self.assertEqual(sorted(cert5.M87_PROBES), ["a", "b"])
        self.assertEqual(sorted(cert5.M87_PROBES["a"]), ["l", "s"])
        self.assertEqual(sorted(cert5.M87_PROBES["b"]), ["l"])

    def test_specs(self):
        for g in ("a", "b"):
            specs = cert5.group_specs(g, fake_reps(g))
            self.assertTrue(cert5.specs_ok(g, specs))
            self.assertFalse(cert5.specs_ok(g, specs[:-1]))
            self.assertEqual(sum(bool(sp.get("lemma93")) for sp in specs),
                             m87.NAMED_RANKS[g][0])
        a = cert5.group_specs("a", fake_reps("a"))
        self.assertEqual((a[0]["name"], a[-1]["name"]),
                         ("r3l_t7_B6_o010_c001_a0042", "r3l_t7_B6_o010_c001_a3720"))
        self.assertEqual([sp["name"] for sp in a if not sp.get("lemma93")],
                         ["r3s_t7_B6_o010_c001_a0152"])
        bb = cert5.group_specs("b", fake_reps("b"))
        self.assertTrue(all(sp.get("lemma93") for sp in bb))
        self.assertEqual((bb[0]["name"], bb[-1]["name"]),
                         ("r3l_t7_B6_o010_c008_a0166", "r3l_t7_B6_o005_c002_a1065"))
        bad = fake_reps("b")
        row = bad["r3b_t7_B6_o005_c002"][1065]
        bad["r3b_t7_B6_o005_c002"][1065] = dict(row, a1=row["a1"] ^ 2)
        self.assertFalse(cert5.specs_ok("b", cert5.group_specs("b", bad)))

    def test_grade(self):
        specs = cert5.group_specs("b", fake_reps("b"))
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert5.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                row = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                       "cadical": {"status": "UNSAT", "seconds": 1.0},
                       "drat": {"verified": True, "seconds": 2.0}, "proof_bytes": 100 + i,
                       "cnf_sha256": "0" * 64}
                with open(os.path.join(d, f"cert5_{sp['name']}.json"), "w") as f:
                    json.dump(row, f)
            out = cert5.grade("b", d)
            self.assertEqual(out["instances"], 25)
            self.assertEqual(out["verified"], 24)
            self.assertEqual(out["not_verified"], [specs[0]["name"]])
            self.assertEqual(out["counts"], {"VERIFIED": 24, "MISSING": 1})
            self.assertEqual(out["by_class"],
                             {"r3b_t7_B6_o010_c008": {"instances": 15, "verified": 14},
                              "r3b_t7_B6_o005_c002": {"instances": 10, "verified": 10}})
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (24.0, 48.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 123])
            self.assertEqual(len(out["rows"]), 25)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade group b", cert5.summary_line(out))


if __name__ == "__main__":
    unittest.main()
