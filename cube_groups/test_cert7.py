# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert7.py that need neither CaDiCaL nor drat-trim; the check part runs cert1's
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert7
import m57 as m
import m69
import m85


def fake_reps(group):
    """m66-shaped roots of the group's classes: rank 2 except at m85's rows, which carry their
    values."""
    reps = {}
    for name in cert7.classes(group):
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(m85.NAMED_GATE[name]["orbits"])]
    for name, k, rk, index, size, a1 in cert7.rows(group):
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert7(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_groups(self):
        self.assertTrue(cert7.groups_ok())
        self.assertEqual([len(cert7.rows(g)) for g in ("a", "b")], [12, 12])
        self.assertEqual(cert7.classes("a"), ["r3b_t7_B6_o010_c004"])
        self.assertEqual(cert7.classes("b"), ["r3b_t7_B6_o010_c006"])
        self.assertEqual(cert7.per_class("a"), {"r3b_t7_B6_o010_c004": 12})
        self.assertEqual(cert7.per_class("b"), {"r3b_t7_B6_o010_c006": 12})
        self.assertEqual(sorted(cert7.M85_PROBES), ["a", "b"])
        self.assertEqual(sorted(cert7.M85_PROBES["a"]), ["l"])
        self.assertEqual(sorted(cert7.M85_PROBES["b"]), ["l"])

    def test_specs(self):
        for g in ("a", "b"):
            specs = cert7.group_specs(g, fake_reps(g))
            self.assertTrue(cert7.specs_ok(g, specs))
            self.assertFalse(cert7.specs_ok(g, specs[:-1]))
            self.assertTrue(all(sp.get("lemma93") for sp in specs))
            self.assertEqual(sum(bool(sp.get("lemma93")) for sp in specs),
                             m85.NAMED_RANKS[g][0])
        a = cert7.group_specs("a", fake_reps("a"))
        self.assertEqual((a[0]["name"], a[-1]["name"]),
                         ("r3l_t7_B6_o010_c004_a0028", "r3l_t7_B6_o010_c004_a1326"))
        bb = cert7.group_specs("b", fake_reps("b"))
        self.assertEqual((bb[0]["name"], bb[-1]["name"]),
                         ("r3l_t7_B6_o010_c006_a0165", "r3l_t7_B6_o010_c006_a1973"))
        bad = fake_reps("b")
        row = bad["r3b_t7_B6_o010_c006"][1973]
        bad["r3b_t7_B6_o010_c006"][1973] = dict(row, a1=row["a1"] ^ 2)
        self.assertFalse(cert7.specs_ok("b", cert7.group_specs("b", bad)))

    def test_grade(self):
        specs = cert7.group_specs("b", fake_reps("b"))
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert7.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                row = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                       "cadical": {"status": "UNSAT", "seconds": 5.0 if i == 3 else 1.0},
                       "drat": {"verified": True, "seconds": 50.0 if i == 4 else 2.0},
                       "proof_bytes": 100 + i, "cnf_sha256": "0" * 64}
                with open(os.path.join(d, f"cert7_{sp['name']}.json"), "w") as f:
                    json.dump(row, f)
            out = cert7.grade("b", d)
            self.assertEqual(out["instances"], 12)
            self.assertEqual(out["verified"], 11)
            self.assertEqual(out["not_verified"], [specs[0]["name"]])
            self.assertEqual(out["counts"], {"VERIFIED": 11, "MISSING": 1})
            self.assertEqual(out["by_class"],
                             {"r3b_t7_B6_o010_c006": {"instances": 12, "verified": 11}})
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (15.0, 70.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 110])
            self.assertEqual(out["slowest"], [specs[4]["name"], 5.0, 2.0])
            self.assertEqual(len(out["rows"]), 12)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade group b", cert7.summary_line(out))


if __name__ == "__main__":
    unittest.main()
