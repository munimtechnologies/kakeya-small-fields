# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m103.py (job m103, notes/a95.md). Needs m42.py, sat_aniso.py, m100.py, m101.py,
m102.py and python-sat next to it. Every expected value below was worked out by hand (notes/a95.md,
Lemma 108); matrix bit 3 r + c is entry (r, c), and column c is the image of q_c."""
import unittest

import m102
import m103

I3 = m102.I3


class TestM103(unittest.TestCase):
    def test_subspaces(self):
        self.assertEqual(len(m103.SUBS), 16)
        self.assertEqual(sorted(len(u) for u in m103.SUBS), [1] + [2] * 7 + [4] * 7 + [8])

    def test_span_and_space(self):
        self.assertEqual(m103.span_of([I3, 1, 16]), (0, 1, 16, 17, 256, 257, 272, 273))
        self.assertEqual(m103.space_of(m102.case_t2(5)), (0, 5, 273, 276))
        self.assertEqual(m103.space_of(m102.case_t3(1, 16)), m103.span_of([I3, 1, 16]))
        self.assertEqual(m103.space_of(m102.case_t1()), (0, I3))
        self.assertEqual(m103.describe(m102.case_t1()), (16, "scalar"))

    def test_dim2(self):
        # E00 (projection), E01 (nilpotent of rank 1), E02 + E10 (q2 -> q0 -> q1 -> 0),
        # E00 + E01 + E10 (x(x^2 + x + 1)), the companion matrix of x^3 + x + 1
        # (q0 -> q1 -> q2 -> q0 + q1), E01 + E10 (swap q0, q1; q2 -> 0)
        for m, name, inv, size in [(1, "proj", 10, 28), (2, "nil1", 8, 21), (12, "nil3", 4, 42),
                                   (11, "x(x2+x+1)", 4, 56), (172, "irr", 2, 24),
                                   (10, "x2(x+1)", 6, 84)]:
            s = m103.span_of([I3, m])
            self.assertEqual(m103.orbit_size(s), size, m)
            self.assertEqual(m103.alg_type(s), name, m)
            self.assertEqual(m103.inv_count(s), inv, m)

    def test_dim3(self):
        for gens, name, inv in [([1, 16], "F2^3", 8), ([2, 4], "rad2_image", 6),
                                ([2, 128], "rad2_kernel", 6), ([4, 34], "F2[x]/x3", 4),
                                ([11, 17], "F2xF4", 4), ([106, 157], "F8", 2),
                                ([1, 128], "F2xF2[x]/x2", 6)]:
            s = m103.span_of([I3] + gens)
            self.assertEqual(len(s), 8)
            self.assertTrue(all(m102.mm3(a, b) == m102.mm3(b, a) for a in s for b in s), gens)
            self.assertEqual(m103.alg_type(s), name, gens)
            self.assertEqual(m103.inv_count(s), inv, gens)
        # A = E01 + E10 + E12 + E20 has A^2 = E00 + E02 + E10 + E11 + E21 = 157
        self.assertEqual(m102.mm3(106, 106), 157)
        self.assertEqual(m103.orbit_size(m103.span_of([I3, 2, 4])), 7)
        self.assertEqual(m103.orbit_size(m103.span_of([I3, 106, 157])), 8)

    def test_pilot_data(self):
        o000 = m103.M102_PILOT["r3b_t8_B7_o000_c000"]
        o011 = m103.M102_PILOT["r3b_t8_B7_o011_c000"]
        self.assertEqual((len(o000["UNSAT"]), len(o000["UNKNOWN"])), (30, 38))
        self.assertEqual((len(o011["UNSAT"]), len(o011["UNKNOWN"])), (1, 53))
        for st in (o000, o011):
            labels = st["UNSAT"] + st["UNKNOWN"]
            self.assertEqual(len(set(labels)), len(labels))
        self.assertEqual(set(m103.DEEP) <= set(o000["UNKNOWN"]), True)


if __name__ == "__main__":
    unittest.main()
