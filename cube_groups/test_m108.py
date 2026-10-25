# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m108.py (job m108, notes/a100.md). Needs m42.py, sat_aniso.py, m100.py to m107.py
and python-sat next to it. Every expected value below was worked out by hand. The checks of (*) are
tested against what each group states: Example 1 of finite-groups.md satisfies every equation, and a
one-entry change breaks exactly the groups whose equations contain that entry."""
import unittest

import m100
import m106
import m107
import m108
import sat_aniso as sa

# m107f's four k = 6 items (compete-results/m107f-b7-groups-v1)
K6_ITEMS = ("r3b_t8_B7_o000_c000_t3_m001_128", "r3b_t8_B7_o000_c000_t3_m002_004",
            "r3b_t8_B7_o000_c000_t3_m002_128", "r3b_t8_B7_o000_c000_t3_m005_130")


class TestStatic(unittest.TestCase):
    def test_groups(self):
        self.assertEqual(m108.KIND, "uvvvhhhhhhh")
        self.assertEqual(m108.l_group(1, 0), "L_vu")
        self.assertEqual(m108.l_group(9, 3), "L_hv")
        self.assertEqual(m108.q_group(4, 7, 0), "Q_uhh")
        self.assertEqual(m108.q_group(2, 3, 1), "Q_vvv")
        self.assertEqual(sorted(m108.STAR_DROP), sorted(m108.STAR))
        self.assertEqual(len(set(m108.STAR)), 16)

    def test_counts_by_hand(self):
        c = m108.STAR_COUNTS
        # 11 * 11 pairs (i, j) and 55 pairs {i, k} times 9 choices of j, 8 rows each
        self.assertEqual(sum(c[g] for g in m108.STAR if g[0] == "L"), 121 * 8)
        self.assertEqual(sum(c[g] for g in m108.STAR if g[0] == "Q"), 55 * 9 * 8)
        self.assertEqual(m108.count_groups(), c)

    def test_small_encode_is_sat_aniso(self):
        ref, _ = sa.encode(3, 3, aniso=False, echelon=False)
        cnf, _, counts = m108.encode_star(3, 3, m108.STAR)
        self.assertEqual((m100.clause_hash(cnf), len(cnf.clauses), cnf.nv),
                         (m100.clause_hash(ref), len(ref.clauses), ref.nv))
        # t = 3, d = 3 (u, v, v): (L) 1, 2, 2, 4 pairs, (Q) the one 3-set three times
        want = {g: 0 for g in m108.STAR}
        want.update({"L_uu": 3, "L_uv": 6, "L_vu": 6, "L_vv": 12, "Q_uvv": 9})
        self.assertEqual(counts, want)

    def test_drop_one_group(self):
        full, _, _ = m108.encode_star(3, 3, m108.STAR)
        keep = [g for g in m108.STAR if g != "Q_uvv"]
        cnf, _, counts = m108.encode_star(3, 3, keep)
        self.assertNotIn("Q_uvv", counts)
        self.assertEqual(counts["L_vv"], 12)
        self.assertLess(len(cnf.clauses), len(full.clauses))

    def test_example1(self):
        # A_0 = E_11, A_1 = E_12 + E_13 + E_21 + E_22, s_0 = e_2 + e_3, s_1 = e_1 + e_2 + e_3,
        # b(0, 1) = e_2 (1-based); index 0 is u and index 1 is v
        As, ss, B = sa.example1()
        ok = m108.star_checks(As, ss, B, 3, 2)
        self.assertEqual([g for g in m108.STAR if not ok[g]], [])
        # s_1 loses e_1: A_0 s_1 becomes 0 (was e_1) and A_1 s_1 becomes e_2 (was 0)
        ok = m108.star_checks(As, [ss[0], ss[1] ^ 1], B, 3, 2)
        self.assertEqual([g for g in m108.STAR if not ok[g]], ["L_vu", "L_vv"])
        # b(0, 1) gains e_1: (L) for (i, j) = (0, 1) still holds (A_0 e_1 = e_1 cancels it), for
        # (1, 0) the right side becomes e_2 against A_0 s_1 = e_1
        ok = m108.star_checks(As, ss, {(0, 1): B[(0, 1)] ^ 1}, 3, 2)
        self.assertEqual([g for g in m108.STAR if not ok[g]], ["L_vu"])

    def test_minimize(self):
        def oracle(s):
            return "UNSAT" if "L_vv" in s and ("Q_vvv" in s or "L_uv" in s) else "SAT"
        kept, why, log = m108.minimize(oracle, m108.STAR_DROP)
        # everything before Q_vvv goes; Q_vvv goes (L_uv still there); L_vv stays; L_vu goes;
        # L_uv stays (only L_vv left would be SAT); L_uu goes
        self.assertEqual(kept, ["L_vv", "L_uv"])
        self.assertEqual(why, {"L_vv": "SAT", "L_uv": "SAT"})
        self.assertEqual(len(log), 17)
        self.assertIsNone(m108.minimize(lambda s: "UNKNOWN", m108.STAR_DROP)[0])

    def test_shards_and_modes(self):
        sizes = {}
        for i in range(m108.CERT_TOTAL):
            sizes[m108.shard_of(i)] = sizes.get(m108.shard_of(i), 0) + 1
        self.assertEqual(sizes, {"a": 279, "b": 279, "c": 279, "d": 278})
        self.assertEqual(sizes, m108.CERT_SIZE)
        self.assertEqual([m108.mode_of(x) for x in m107.OPEN_D2], ["n"] * 4)
        self.assertEqual(m108.mode_of("r3b_t8_B7_o005_c003_t3_m004_034"), "sweep")
        self.assertEqual(len(set(m108.M_ONLY)), 12)
        self.assertFalse(set(m108.M_ONLY) & set(K6_ITEMS))


class TestControl(unittest.TestCase):
    """o000_c000, t2 with M = J (the positive control of m102 to m107): with the normal form and M
    only, the CNF is m107's "M only" CNF, and it is SAT."""

    @classmethod
    def setUpClass(cls):
        from pysat.solvers import Solver
        cls.spec, cls.case = m106.transfer_controls()[0]
        cnf, names, cls.counts = m108.build_star(cls.spec, cls.case, m108.STAR)
        cls.hash, cls.n, cls.nv = m100.clause_hash(cnf), len(cnf.clauses), cnf.nv
        s = Solver(name="cadical195", bootstrap_with=cnf.clauses)
        cls.sat = s.solve()
        cls.As, cls.ss, cls.B = sa.decode(s.get_model(), names, m108.T, m108.D)
        s.delete()
        del cnf

    def test_same_as_m107_m_only(self):
        ref, _, _ = m107.build_groups(self.spec, self.case, ["M"])
        self.assertEqual((m100.clause_hash(ref), len(ref.clauses), ref.nv),
                         (self.hash, self.n, self.nv))
        self.assertEqual(self.counts["M"], 128)

    def test_model_meets_every_group(self):
        self.assertTrue(self.sat)
        ok = m108.star_checks(self.As, self.ss, self.B, m108.T, m108.D)
        self.assertEqual([g for g in m108.STAR if not ok[g]], [])
        res = {"A": self.As, "s": self.ss, "B": [[i, k, v] for (i, k), v in sorted(self.B.items())]}
        chk = m100.check_model(self.spec, res)
        self.assertTrue(chk["system"] and chk["normal_form"])


if __name__ == "__main__":
    unittest.main()
