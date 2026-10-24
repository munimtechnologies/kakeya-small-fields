# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m98.py (job m98). The space in test_invertible_beyond_cap is the case m97 missed:
its first 12 basis vectors span only matrices with row 3 zero, and the 13th is E_33."""
import time
import unittest

import m95
import m97
import m98 as m


class TestM98(unittest.TestCase):
    def test_inverse_rows(self):
        self.assertEqual(m.inverse_rows([1, 2], 2), [1, 2])
        self.assertEqual(m.inverse_rows([3, 2], 2), [3, 2])        # [[1,1],[0,1]] is its own inverse
        self.assertIsNone(m.inverse_rows([3, 3], 2))
        rows = [0b0011, 0b0110, 0b1100, 0b1001 ^ 0b0001]
        inv = m.inverse_rows(rows, 4)
        for c in range(4):
            self.assertEqual(m.apply_rows(rows, m.apply_rows(inv, 1 << c)), 1 << c)

    def test_rows_of_cols(self):
        self.assertEqual(m.rows_of_cols([0b01, 0b11], 2), [0b11, 0b10])

    def test_invertible_beyond_cap(self):
        basis = [1 << (r * 4 + c) for r in range(3) for c in range(4)] + [1 << 15]
        self.assertEqual(m.CAPPED(basis, 4), (None, False))
        S, complete = m.invertible_full(basis, 4)
        self.assertTrue(complete)
        self.assertEqual(m.sa.rank_f2(m97.s_rows(S, 4)), 4)
        self.assertEqual(m.invertible_full([1, 2], 2), (None, True))
        self.assertEqual(m.invertible_full([], 2), (None, True))

    def test_check_solution_witness(self):
        for name in ("t4_N", "t4_E", "t6_e00e11", "t6_e00e12"):
            Ms = m97.SMALL[name][2]
            res = m97.reduced(Ms)
            self.assertEqual(res["status"], "SAT", name)
            chk = m.check_solution(Ms, res["G"], res["S_rows"])
            self.assertTrue(chk["relax_ok"], name)
            bad = [0] + list(res["S_rows"][1:])
            self.assertFalse(m.check_solution(Ms, res["G"], bad)["relax_ok"], name)
        Ms = m97.SMALL["t4_E"][2]
        res = m97.reduced(Ms)
        self.assertFalse(m.check_solution(Ms, res["G"], res["S_rows"])["aniso1"])

    def test_relax_prefix_t4(self):
        Ms = m97.SMALL["t4_N"][2]
        a, _, info = m95.encode_rank4(4, 2, Ms)
        b, _, _ = m95.encode_rank4(4, 2, Ms)
        self.assertEqual(m95.relax(a, 4), 31)
        self.assertEqual(m.relax_prefix(b, 4, info["start"]), 31)
        self.assertEqual(a.clauses, b.clauses)
        self.assertEqual(m95.hyperplanes(Ms), [1])
        c, _, info = m95.encode_rank4(4, 2, Ms, 1)
        e, _, _ = m95.encode_rank4(4, 2, Ms, 1)
        self.assertEqual(m.relax_prefix(c, 4, info["start"]), 31)
        # m95.relax would also drop the one-to-one clause of the two columns (length t)
        self.assertGreaterEqual(m95.relax(e, 4), 32)

    def test_model_solution_t4(self):
        Ms = m97.SMALL["t4_N"][2]
        status, _, _, models = m97.solve_models(4, 2, Ms, 2, 30, time.time() + 60)
        self.assertEqual(status, "SAT")
        for As, ss, B in models:
            out = m.model_solution(As, ss, B, 4, 2, Ms)
            self.assertTrue(out["identities_ok"])
            self.assertTrue(out["T_invertible"] and out["T_into_X1"])
            # solution_ok is graded in part consistent, not asserted here, so that a failure is
            # reported with the other answers instead of stopping the job
            self.assertIn("solution_ok", out)

    def test_tables(self):
        names = [x[0] for x in m97.instances()]
        self.assertEqual(sorted(names), sorted(m.M97_REDUCED))
        self.assertTrue(set(m.CONSISTENT) <= set(names))
        self.assertTrue(all(len(v) == 3 and set(v) <= set("SU?") for v in m.M97_REDUCED.values()))


if __name__ == "__main__":
    unittest.main()
