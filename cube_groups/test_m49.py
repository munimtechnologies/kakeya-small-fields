# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m49.py (job m49). The full check (m45.py's classification of (B6), the real
instance and the planted control solved) is --part check, which the job runs as its own step."""
import unittest

import m42
import m45
import m49 as m
import sat_aniso as sa


class TestM49(unittest.TestCase):
    def test_tables(self):
        self.assertEqual(len(m.BATCHES["a"]), 13)
        self.assertEqual(len(m.BATCHES["b"]), 10)
        self.assertFalse(set(m.BATCHES["a"]) & set(m.BATCHES["b"]))
        for name in m.CONTROL:
            self.assertIn(name, m45.OPEN)
        # The d = 0 classes are left out (Corollary 60 needs d >= 1), and so is m45b's UNSAT.
        for name in ("r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c001", "r3b_t7_B6_o007_c005"):
            self.assertNotIn(name, m.CONTROL)

    def test_d(self):
        for name in m.CONTROL:
            pi, _ = m45.pair_cls(name)
            self.assertEqual(m.d_of(m45.OPEN[name]), m.D_OF_PAIR[pi])
            self.assertGreaterEqual(m.D_OF_PAIR[pi], 1)

    def test_counts(self):
        for kd, want in m.HAND_COR60.items():
            cnf = sa.CNF()
            A = [[[cnf.new() for c in range(7)] for r in range(7)] for i in range(kd)]
            self.assertEqual(m.add_cor60(cnf, (A, None, None), 7, kd, m45.OPEN["r3b_t7_B6_o000_c000"]),
                             want)
            self.assertEqual(len(m.maps_on_n([0] * kd, kd)), want[0])

    def test_semantic(self):
        for kd in (3, 4):
            sem = m.semantic_check(7, kd, m45.OPEN["r3b_t7_B6_o008_c002"], 120, kd)
            self.assertTrue(sem["agree"])
            self.assertTrue(sem["both_outcomes"])

    def test_small_cases(self):
        # A_(h_1) = 0, A_(h_1) = A_u, A_(h_1) = A_(h_2): each must violate the clauses.
        au = m45.OPEN["r3b_t7_B6_o000_c000"]
        cnf = sa.CNF()
        A = [[[cnf.new() for c in range(7)] for r in range(7)] for i in range(3)]
        m.add_cor60(cnf, (A, None, None), 7, 3, au)
        x = 1 << 30
        for As, ok in (([au, 0, x], False), ([au, au, x], False), ([au, x, x], False),
                       ([au, x, x ^ au], False), ([au, x, 1 << 3], True)):
            val = {A[i][r][c]: bool((As[i] >> (7 * r + c)) & 1)
                   for i in range(3) for r in range(7) for c in range(7)}
            self.assertEqual(sa.satisfies(cnf, m.extend(cnf, val)), ok)

    def test_planted(self):
        As, ss, B = m42.planted()
        self.assertTrue(all(m.maps_on_n(As, 3)))


if __name__ == "__main__":
    unittest.main()
