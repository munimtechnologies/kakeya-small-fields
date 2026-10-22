# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert1.py that need neither CaDiCaL nor drat-trim; the check part runs the
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert1
import m57 as m
import m69
import m90


def fake_reps():
    """m66-shaped roots of the class: rank 2 except at m90's re-runs, which carry their rows."""
    reps = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
            for i in range(m90.NAMED_GATE[cert1.NAME]["orbits"])]
    for _, k, rk, index, size, a1 in cert1.rerun_rows().values():
        reps[k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert1(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_sample(self):
        self.assertEqual(len(cert1.SAMPLE), 99)
        self.assertEqual((cert1.SAMPLE[0], cert1.SAMPLE[-1]), (0, 1960))
        rows = cert1.rerun_rows()
        self.assertEqual(len(rows), 32)
        self.assertEqual(tuple(sorted(k for k in rows if k in cert1.SAMPLE)),
                         cert1.RERUN_IN_SAMPLE)
        self.assertEqual([rows[k][2] for k in cert1.RERUN_IN_SAMPLE], [1, 0, 0])
        specs = cert1.sample_specs(fake_reps())
        self.assertTrue(cert1.sample_ok(specs))
        self.assertFalse(cert1.sample_ok(specs[:-1]))
        bad = fake_reps()
        bad[240] = dict(bad[240], a1=bad[240]["a1"] ^ 2)
        self.assertFalse(cert1.sample_ok(cert1.sample_specs(bad)))

    def test_builds(self):
        specs = {int(sp["name"][-4:]): sp for sp in cert1.sample_specs(fake_reps())}
        for k, units in ((240, 49 + 21), (60, 49), (1960, 49 + 21)):
            c, _, h, u = m.build(dict(specs[k]), "cadical")
            self.assertEqual((h, u), (m.HAND_HINTS["B6"], units))
            with tempfile.TemporaryDirectory() as d:
                p = os.path.join(d, "x.cnf")
                nv = cert1.write_dimacs(c.clauses, c.nv, p)
                self.assertEqual(nv, c.nv)
                self.assertEqual(cert1.read_dimacs(p), (nv, [list(x) for x in c.clauses]))

    def test_dimacs_and_parsers(self):
        nv, cls = cert1.php(6, 5)
        self.assertEqual((nv, len(cls)), (30, 6 + 5 * 15))
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "php.cnf")
            self.assertEqual(cert1.write_dimacs(cls + [[]], nv, p), 30)
            self.assertEqual(cert1.read_dimacs(p), (30, cls + [[]]))
        self.assertTrue(cert1.is_verified("c parsing\ns VERIFIED\n"))
        self.assertFalse(cert1.is_verified("c x\ns NOT VERIFIED\n"))
        self.assertFalse(cert1.is_verified(""))
        model = cert1.model_of("s SATISFIABLE\nv 1 -2 3\nv -4 0\n")
        self.assertEqual(model, [1, -2, 3, -4])
        self.assertTrue(cert1.satisfied([[1, 2], [-2, -4]], model))
        self.assertFalse(cert1.satisfied([[2, 4]], model))

    def test_grade(self):
        specs = cert1.sample_specs(fake_reps())
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert1.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                with open(os.path.join(d, f"cert1_{sp['name']}.json"), "w") as f:
                    json.dump({"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                               "cadical": {"status": "UNSAT", "seconds": 1.0},
                               "drat": {"verified": True, "seconds": 2.0},
                               "proof_bytes": 100 + i}, f)
            out = cert1.grade(d)
            self.assertEqual(out["verified"], 98)
            self.assertEqual(out["not_verified"], [specs[0]["name"]])
            self.assertEqual(out["status"][specs[0]["name"]], "MISSING")
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (98.0, 196.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 197])
            self.assertEqual(len(out["reruns"]), 3)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade", cert1.summary_line(out))


if __name__ == "__main__":
    unittest.main()
