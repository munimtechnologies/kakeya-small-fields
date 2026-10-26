# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m109.py (job m109, notes/a101.md). Needs m42.py, sat_aniso.py, m100.py to m108.py
and python-sat next to it. Every expected value below was worked out by hand. The equation checks
are tested against what the equations state: Example 1 of finite-groups.md satisfies every one,
and a one-entry change breaks exactly the equations that contain that entry."""
import unittest

import m100
import m106
import m108
import m109
import sat_aniso as sa


class TestStatic(unittest.TestCase):
    def test_orders(self):
        self.assertEqual(sorted(m109.IDX_DROP), list(range(11)))
        self.assertEqual(sorted(m109.ROW_DROP), list(range(8)))
        self.assertEqual(sorted(i for s in m109.SHARDS.values() for i in s), list(range(10)))
        # 121 (L) pairs and 55 * 9 (Q) triples
        self.assertEqual(len(m109.equations()), 121 + 495)

    def test_counts_by_hand(self):
        self.assertEqual(m109.count_sub(8, 11, m108.STAR, m109.ALL_IDX, m109.ALL_ROWS),
                         m108.STAR_COUNTS)
        self.assertEqual(m109.count_sub(8, 11, m108.STAR, m109.SUB_IDX, m109.SUB_ROWS),
                         m109.SUB_COUNTS)
        # 6 indices: 36 (L) pairs and 20 three-sets three times, 3 rows
        self.assertEqual(sum(m109.SUB_COUNTS.values()), (36 + 60) * 3)

    def test_small_full_is_encode_star(self):
        ref, _, _ = m108.encode_star(3, 3, m108.STAR)
        cnf, _, counts = m109.encode_sub(3, 3, m108.STAR, range(3), range(3))
        self.assertEqual((m100.clause_hash(cnf), len(cnf.clauses), cnf.nv),
                         (m100.clause_hash(ref), len(ref.clauses), ref.nv))
        ref, _, _ = m108.encode_star(3, 3, ["L_vv", "Q_uvv"])
        cnf, _, _ = m109.encode_sub(3, 3, ["L_vv", "Q_uvv"], range(3), range(3))
        self.assertEqual(m100.clause_hash(cnf), m100.clause_hash(ref))

    def test_small_restricted(self):
        # t = 3, d = 3 (u, v, v); indices 0, 1 and rows 0, 2: one pair of each kind, no 3-set
        _, _, counts = m109.encode_sub(3, 3, m108.STAR, [0, 1], [0, 2])
        want = {g: 0 for g in m108.STAR}
        want.update({"L_uu": 2, "L_uv": 2, "L_vu": 2, "L_vv": 2})
        self.assertEqual(counts, want)
        self.assertEqual(m109.count_sub(3, 3, m108.STAR, [0, 1], [0, 2]), want)
        full, _, _ = m109.encode_sub(3, 3, m108.STAR, range(3), range(3))
        part, _, _ = m109.encode_sub(3, 3, m108.STAR, [0, 1], [0, 2])
        self.assertLess(len(part.clauses), len(full.clauses))
        # the names of A, s and b are made first, so they are the same in both
        self.assertGreaterEqual(part.nv, 3 * 9 + 3 * 3 + 3 * 3)

    def test_example1(self):
        # A_0 = E_11, A_1 = E_12 + E_13 + E_21 + E_22, s_0 = e_2 + e_3, s_1 = e_1 + e_2 + e_3,
        # b(0, 1) = e_2 (1-based; row r is bit r - 1)
        As, ss, B = sa.example1()
        self.assertEqual(m109.failures(As, ss, B, 3, 2), [])
        # s_1 loses e_1: A_0 s_1 = 0 (was e_1: row 1) and A_1 s_1 = e_2 (was 0: row 2)
        fails = m109.failures(As, [ss[0], ss[1] ^ 1], B, 3, 2)
        self.assertEqual(fails, [("L_vu", (1, 0), 1), ("L_vv", (1, 1), 2)])
        self.assertFalse(m109.holds(fails, m108.STAR, [0, 1], [0]))
        self.assertFalse(m109.holds(fails, m108.STAR, [0, 1], [1]))
        self.assertTrue(m109.holds(fails, m108.STAR, [0, 1], [2]))
        self.assertTrue(m109.holds(fails, m108.STAR, [0], [0, 1, 2]))
        self.assertTrue(m109.holds(fails, ["L_uu", "L_uv"], [0, 1], [0, 1, 2]))
        # b(0, 1) gains e_1: (L) for (1, 0) has b + A_1 b = e_2 against A_0 s_1 = e_1 (rows 1, 2)
        fails = m109.failures(As, ss, {(0, 1): B[(0, 1)] ^ 1}, 3, 2)
        self.assertEqual(fails, [("L_vu", (1, 0), 3)])
        ok = m108.star_checks(As, ss, {(0, 1): B[(0, 1)] ^ 1}, 3, 2)
        self.assertEqual({g for g, _, _ in fails}, {g for g in m108.STAR if not ok[g]})

    def test_reduce_item(self):
        calls = []

        def solve(idx, rows, groups):
            calls.append((idx, rows, groups))
            hit = {2, 3, 9} <= set(idx) and 6 in rows and "L_hv" in groups
            return "UNSAT" if hit else "SAT"

        e = m109.reduce_item(solve)
        # indices: 4..8 go, 9 stays, 10 and 1 go, 3 and 2 stay, 0 goes; rows: all but 6 go; live
        # groups of {v_2, v_3, h_6} on row 6 in STAR_DROP order: L_hh, Q_vvh, L_hv, L_vh, L_vv
        self.assertEqual(e["kept_idx"], [2, 3, 9])
        self.assertEqual(e["kept_rows"], [6])
        self.assertEqual(e["kept_groups"], ["L_hv"])
        self.assertEqual(e["why"], {"idx": {"9": "SAT", "3": "SAT", "2": "SAT"},
                                    "rows": {"6": "SAT"}, "groups": {"L_hv": "SAT"}})
        # 1 + 11 index solves, 8 row solves, 5 group solves; the first solve of the row and group
        # passes is the last UNSAT of the pass before
        self.assertEqual(len(calls), 25)
        self.assertEqual(e["solves"], 25)
        self.assertEqual(e["equations"], 2)
        self.assertTrue(m109.proven(e))
        self.assertEqual(e["log"][0][3], "UNSAT")
        none = m109.reduce_item(lambda idx, rows, groups: "UNKNOWN")
        self.assertIsNone(none["kept_idx"])
        self.assertFalse(m109.proven(none))


class TestControl(unittest.TestCase):
    """o000_c000, t2 with M = J (the positive control of m102 to m108): with everything kept the CNF
    is m108's, and it is SAT."""

    @classmethod
    def setUpClass(cls):
        from pysat.solvers import Solver
        cls.spec, cls.case = m106.transfer_controls()[0]
        cnf, names, cls.counts = m109.build_sub(cls.spec, cls.case, m108.STAR, m109.ALL_IDX,
                                                m109.ALL_ROWS)
        cls.hash, cls.n, cls.nv = m100.clause_hash(cnf), len(cnf.clauses), cnf.nv
        s = Solver(name="cadical195", bootstrap_with=cnf.clauses)
        cls.sat = s.solve()
        cls.As, cls.ss, cls.B = sa.decode(s.get_model(), names, m109.T, m109.D)
        s.delete()
        del cnf

    def test_same_as_m108(self):
        ref, _, _ = m108.build_star(self.spec, self.case, m108.STAR)
        self.assertEqual((m100.clause_hash(ref), len(ref.clauses), ref.nv),
                         (self.hash, self.n, self.nv))
        self.assertEqual(self.counts["M"], 128)

    def test_model_and_one_change(self):
        self.assertTrue(self.sat)
        self.assertEqual(m109.failures(self.As, self.ss, self.B, 8, 11), [])
        # s_(v_1) gains e_5 (bit 5, outside ker A_u = span(e_0..e_4)): A_u s_(v_1) changes by
        # A_u e_5 != 0, so (L) for (v_1, u) breaks on exactly those rows, and every broken
        # equation contains v_1 (index 1)
        ss = list(self.ss)
        ss[1] ^= 1 << 5
        fails = m109.failures(self.As, ss, self.B, 8, 11)
        col = sa.mat_apply(self.As[0], 1 << 5, 8)
        self.assertNotEqual(col, 0)
        self.assertIn(("L_vu", (1, 0), col), fails)
        self.assertTrue(all(1 in ix for _, ix, _ in fails))
        self.assertTrue(m109.holds(fails, m108.STAR, [i for i in range(11) if i != 1],
                                   m109.ALL_ROWS))
        self.assertFalse(m109.holds(fails, ["L_vu"], [0, 1], m109.ALL_ROWS))


if __name__ == "__main__":
    unittest.main()
