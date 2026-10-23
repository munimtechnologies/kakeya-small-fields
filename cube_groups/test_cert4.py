# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert4.py that need neither CaDiCaL nor drat-trim; the check part runs cert1's
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert4
import m57 as m
import m69
import m89


def fake_reps(group):
    """m66-shaped roots of the group's classes: rank 2 except at m89's rows, which carry their
    values."""
    reps = {}
    for name in cert4.classes(group):
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(m89.NAMED_GATE[name]["orbits"])]
    for name, k, rk, index, size, a1 in cert4.rows(group):
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert4(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_groups(self):
        self.assertTrue(cert4.groups_ok())
        self.assertEqual([len(cert4.rows(g)) for g in ("a", "b")], [25, 24])
        self.assertEqual(cert4.classes("a"), ["r3b_t7_B6_o003_c001", "r3b_t7_B6_o005_c001"])
        self.assertEqual(cert4.classes("b"), cert4.classes("a"))
        self.assertEqual(sorted(cert4.M89_PROBES), ["a", "b"])
        self.assertEqual(sorted(cert4.M89_PROBES["a"]), ["l", "s"])
        self.assertEqual(sorted(cert4.M89_PROBES["b"]), ["l"])

    def test_specs(self):
        for g in ("a", "b"):
            specs = cert4.group_specs(g, fake_reps(g))
            self.assertTrue(cert4.specs_ok(g, specs))
            self.assertFalse(cert4.specs_ok(g, specs[:-1]))
            self.assertEqual(sum(bool(sp.get("lemma93")) for sp in specs),
                             m89.NAMED_RANKS[g][0])
        a = cert4.group_specs("a", fake_reps("a"))
        self.assertEqual((a[0]["name"], a[-1]["name"]),
                         ("r3l_t7_B6_o003_c001_a0042", "r3l_t7_B6_o005_c001_a1214"))
        self.assertEqual([sp["name"] for sp in a if not sp.get("lemma93")],
                         ["r3s_t7_B6_o005_c001_a0042"])
        bb = cert4.group_specs("b", fake_reps("b"))
        self.assertTrue(all(sp.get("lemma93") for sp in bb))
        self.assertEqual((bb[0]["name"], bb[-1]["name"]),
                         ("r3l_t7_B6_o003_c001_a0823", "r3l_t7_B6_o005_c001_a1905"))
        bad = fake_reps("b")
        row = bad["r3b_t7_B6_o005_c001"][1905]
        bad["r3b_t7_B6_o005_c001"][1905] = dict(row, a1=row["a1"] ^ 2)
        self.assertFalse(cert4.specs_ok("b", cert4.group_specs("b", bad)))

    def test_grade(self):
        specs = cert4.group_specs("b", fake_reps("b"))
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert4.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                row = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                       "cadical": {"status": "UNSAT", "seconds": 1.0},
                       "drat": {"verified": True, "seconds": 2.0}, "proof_bytes": 100 + i,
                       "cnf_sha256": "0" * 64}
                with open(os.path.join(d, f"cert4_{sp['name']}.json"), "w") as f:
                    json.dump(row, f)
            out = cert4.grade("b", d)
            self.assertEqual(out["instances"], 24)
            self.assertEqual(out["verified"], 23)
            self.assertEqual(out["not_verified"], [specs[0]["name"]])
            self.assertEqual(out["counts"], {"VERIFIED": 23, "MISSING": 1})
            self.assertEqual(out["by_class"],
                             {"r3b_t7_B6_o003_c001": {"instances": 16, "verified": 15},
                              "r3b_t7_B6_o005_c001": {"instances": 8, "verified": 8}})
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (23.0, 46.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 122])
            self.assertEqual(len(out["rows"]), 24)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade group b", cert4.summary_line(out))


if __name__ == "__main__":
    unittest.main()
