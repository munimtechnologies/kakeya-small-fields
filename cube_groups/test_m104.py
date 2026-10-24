# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m104.py (job m104, notes/a96.md). Needs m42.py, sat_aniso.py, m100.py, m101.py,
m102.py, m103.py and python-sat next to it, but not the two programs. Every expected value below
was worked out by hand."""
import os
import tempfile
import unittest

import m100
import m103
import m104


class TestM104(unittest.TestCase):
    def test_dimacs_and_answers(self):
        nv, cls = m104.php(6, 5)
        self.assertEqual((nv, len(cls)), (30, 6 + 5 * 15))
        with tempfile.TemporaryDirectory() as tmp:
            p = os.path.join(tmp, "x.cnf")
            self.assertEqual(m104.write_dimacs([[1, -3], [2]], 0, p), 3)
            with open(p) as f:
                self.assertEqual(f.read(), "p cnf 3 2\n1 -3 0\n2 0\n")
        self.assertTrue(m104.is_verified("c x\ns VERIFIED\n"))
        self.assertFalse(m104.is_verified("s NOT VERIFIED\n"))
        self.assertEqual(m104.model_of("v 1 -2\nv 3 0\nc x\n"), [1, -2, 3])
        self.assertTrue(m104.satisfied([[1, 2], [-2, 3]], [1, -2, 3]))
        self.assertFalse(m104.satisfied([[2]], [1, -2]))

    def test_shards(self):
        counts = {}
        for i in range(57):
            counts[m104.shard_of(i)] = counts.get(m104.shard_of(i), 0) + 1
        self.assertEqual(counts, {"a": 19, "b": 19, "c": 19})

    def test_known_unsat(self):
        self.assertEqual([len(m104.M103A_UNSAT[n]) for n in sorted(m104.M103A_UNSAT)], [22, 6, 16])
        # m102's pilot answered 30 cases of o000_c000 UNSAT, m103a 22 others
        self.assertEqual(len(m104.known_unsat("r3b_t8_B7_o000_c000")), 52)
        for pi, ci, lab in m104.CORE:
            self.assertIn(lab, m104.known_unsat(m100.spec_of(pi, ci)["name"]))
        self.assertEqual(sum(m104.CERT_BY_CLASS.values()), 57)

    def test_hand_counts(self):
        self.assertEqual(m104.TRIVIAL_LE4, 24 + 42 + 56 + 8 + 28 + 21)
        self.assertEqual(sum(m103.HAND_SIZE3[x] for x in ("F8", "F2xF4", "F2[x]/x3")), 57)
        self.assertEqual(sum(m104.A95_ORDERS.values()), 68)

    def test_subspaces_of_v(self):
        self.assertEqual(len(m104.w_masks([0, 1, 2, 3])), 15)
        self.assertEqual(len(m104.w_masks([0, 1, 2, 3, 8, 9, 10])), 127)
        self.assertTrue(all(0 < h < 1 << 11 for h in m104.w_masks(range(11))))
        spec = m100.spec_of(0, 0)
        # m42.phis_for(11, 7): phi(e_(3 + j)) = e_j for j = 1..7, and X_1 = span(e_0..e_4)
        self.assertEqual(m104.h_split(spec), ([8, 9, 10], [4, 5, 6, 7]))
        self.assertEqual(m104.level_idx(spec, "out3_in1"), [0, 1, 2, 3, 8, 9, 10, 4])
        self.assertEqual(m104.level_idx(spec, "in4"), [0, 1, 2, 3, 4, 5, 6, 7])


if __name__ == "__main__":
    unittest.main()
