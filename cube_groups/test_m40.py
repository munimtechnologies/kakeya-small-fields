# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m40.py (job m40). The census of case_b_shapes and the t = 7 CNFs of every form are
in --part selfcheck, which the job runs as its own step."""
import unittest

import case_b_shapes as csh
import m40 as m
import sat_aniso as sa


class TestM40(unittest.TestCase):
    def test_planes(self):
        self.assertEqual(len(m.planes()), 7)
        self.assertEqual(sorted(len(o) for o in m.plane_orbits()), [1, 3, 3])
        self.assertEqual(len(m.gl2_on_y()), 6)
        for g in m.gl2_on_y():
            self.assertEqual(m.apply_y(g, 1), 1)
            self.assertEqual(sa.rank_f2([m.apply_y(g, 2), m.apply_y(g, 4)]), 2)

    def test_reps(self):
        orbs = m.plane_orbits()
        seen = set()
        for q, (a, b) in m.Q_REPS.items():
            self.assertEqual(sa.rank_f2([a, b]), 2)
            self.assertEqual((a | b) >> 3, 0)
            i = next(i for i, o in enumerate(orbs) if m.rep_plane(q) in o)
            self.assertEqual(len(orbs[i]), m.Q_ORBIT_SIZES[q])
            seen.add(i)
        self.assertEqual(len(seen), 3)
        self.assertIn(1, m.rep_plane("cX"))
        self.assertNotIn(1, m.rep_plane("cG"))

    def test_counts(self):
        self.assertEqual(m.CASE_B_UNITS, 84)
        for shape in csh.SHAPES:
            self.assertEqual(csh.unit_count(7, 3, shape), m.SHAPE_UNITS)

    def test_parse(self):
        self.assertEqual(m.parse("cb_t2_k1"), ("cb", 2, 1, None))
        self.assertEqual(m.parse("sh_t6_k3_d2c1"), ("sh", 6, 3, "d2c1"))
        self.assertEqual(m.parse("sh_t7_k3_c_cG"), ("cq", 7, 3, "cG"))
        for name in list(m.CONTROLS) + list(m.EXPLORATORY):
            kind, t, k, extra = m.parse(name)
            self.assertIn(kind, ("cb", "sh", "cq"))
            if kind == "sh":
                self.assertEqual(csh.instance_name(t, k, extra), name)

    def test_cq_units(self):
        n_base = len(sa.encode(7, 9, echelon=False)[0].clauses)
        cnf = m.encode_cq("cX")[0]
        self.assertEqual(len(cnf.clauses) - n_base, 84 + 63 + 14)
        self.assertTrue(m.units_consistent(cnf))


if __name__ == "__main__":
    unittest.main()
