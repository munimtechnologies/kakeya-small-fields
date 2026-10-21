# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for a6_r12.py (job m28). Pure Python; the expected values are worked out by hand in
m28/predictions.md."""
import json
import os
import tempfile
import unittest

import a6_r12 as r12
import a6_r3 as r3


class TestLemma68(unittest.TestCase):
    def test_shapes(self):
        self.assertEqual(r12.lemma68_shapes(1), (("A", 3), ("B", 2)))
        self.assertEqual(r12.lemma68_shapes(2), (("A", 4), ("B", 3)))
        # Rank 3: exactly the shapes A5 and B4 that job m27 searches.
        self.assertEqual(set(r12.lemma68_shapes(3)), {r3.SHAPES["A5"], r3.SHAPES["B4"]})

    def test_table(self):
        for key, (s, p, rho) in r12.SHAPES.items():
            self.assertEqual(key, f"{s}{p}")
            self.assertIn((s, p), r12.lemma68_shapes(rho))
        for name, keys in r12.KILLS.items():
            rhos = {r12.SHAPES[k][2] for k in keys}
            self.assertEqual(len(rhos), 1, name)
            self.assertEqual({r12.SHAPES[k][:2] for k in keys},
                             set(r12.lemma68_shapes(rhos.pop())))


class TestSubspaces(unittest.TestCase):
    def test_fast_matches(self):
        for t, k, c in ((2, 1, 0), (2, 1, 1), (4, 1, 0), (4, 2, 0), (4, 2, 1), (4, 3, 1),
                        (4, 3, 0)):
            self.assertEqual(r12.subspaces_fast(t, k, c), r3.subspaces(t, k, c), (t, k, c))

    def test_counts(self):
        for (t, k, c), n in r12.HAND_SUBSPACES.items():
            self.assertEqual(len(r12.subspaces_fast(t, k, c)), n, (t, k, c))


class TestGroups(unittest.TestCase):
    def test_orders_and_generators(self):
        for key, (s, p, rho) in r12.SHAPES.items():
            self.assertEqual(r3.group_order(6, s, p), r12.HAND_GROUP[key], key)
            gens = r3.generators(6, s, p)
            self.assertEqual(len(gens), r12.HAND_GENS[key], key)
            self.assertTrue(all(r3.in_group(g, 6, s, p) for g in gens), key)


class TestOrbits(unittest.TestCase):
    def test_same_as_a6_r3(self):
        for t, d, rho, s, p in r3.CONTROLS:
            self.assertEqual(r12.orbits(t, s, p, rho), r3.orbits(t, s, p, rho), (t, s, p))
        self.assertEqual(sorted(o[2] for o in r12.orbits(4, "B", 3, 2)),
                         r3.HAND_ORBITS[(4, "B", 3)])

    def test_rank1_t6(self):
        for s, p in (("A", 3), ("B", 2)):
            orb = r12.orbits(6, s, p, 1)
            self.assertEqual(sum(o[2] for o in orb), r12.HAND_TOTALS[1])
            self.assertTrue(all(r3.group_order(6, s, p) % o[2] == 0 for o in orb))
            ds = [r3.dim_meet(o[0], o[1]) for o in orb]
            self.assertEqual(ds, sorted(ds, reverse=True))
            self.assertTrue(all(len(o[0]) == 5 and len(o[1]) == 1 and r3.in_span(o[0], 1)
                                for o in orb))

    def test_rank2_t6_total(self):
        orb = r12.orbits(6, "B", 3, 2)
        self.assertEqual(sum(o[2] for o in orb), r12.HAND_TOTALS[2])
        self.assertTrue(all(r3.group_order(6, "B", 3) % o[2] == 0 for o in orb))

    def test_specs(self):
        sps = r12.specs(6, 7, 1, "B", 2)
        self.assertEqual(sps[0]["name"], "r1_t6_B2_o000")
        self.assertTrue(all(sp["d"] == 7 and sp["rho"] == 1 for sp in sps))
        self.assertEqual(len({sp["name"] for sp in sps}), len(sps))


class TestGrade(unittest.TestCase):
    def test_grade_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            rows = [{"name": "r1_t2_B1_o000", "t": 2, "rho": 1, "shape": "B", "p": 1, "r": [2],
                     "status": "SAT", "verified": True},
                    {"name": "r2_t4_A3_o000", "t": 4, "rho": 2, "shape": "A", "p": 3,
                     "r": [2, 1], "status": "UNSAT"},
                    {"name": "r1_t6_A3_o000", "t": 6, "rho": 1, "shape": "A", "p": 3, "r": [2],
                     "status": "UNSAT"},
                    {"name": "r1_t6_B2_o000", "t": 6, "rho": 1, "shape": "B", "p": 2, "r": [2],
                     "status": "UNSAT"},
                    {"name": "r2_t6_A4_o000", "t": 6, "rho": 2, "shape": "A", "p": 4,
                     "r": [2, 1], "status": "UNKNOWN"},
                    {"name": "r2_t6_B3_o000", "t": 6, "rho": 2, "shape": "B", "p": 3,
                     "r": [2, 1], "status": "UNSAT"}]
            for row in rows:
                with open(os.path.join(d, row["name"] + ".json"), "w") as f:
                    json.dump(row, f)
            with open(os.path.join(d, "r1_t6_A3_o000.spec.json"), "w") as f:
                json.dump({"junk": 1}, f)
            with open(os.path.join(d, "r3_t6_A5_o000.json"), "w") as f:
                json.dump({"name": "r3_t6_A5_o000", "t": 6, "status": "SAT"}, f)
            g = r12.grade(d)
            self.assertEqual(g["ungraded"], {"selfcheck": "missing"})
            self.assertTrue(all(g["graded"].values()))
            self.assertEqual(g["ruled_out"], {"q2_t6_i07": True, "q2_t6_i119": False,
                                              "q2_t6_i120": False})
            self.assertEqual(g["per_shape"]["A4"]["undecided"], ["r2_t6_A4_o000"])
            self.assertFalse(g["any_sat_6"])


if __name__ == "__main__":
    unittest.main()
