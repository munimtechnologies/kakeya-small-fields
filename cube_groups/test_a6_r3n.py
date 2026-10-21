# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for a6_r3n.py (pure Python; no SAT solver). Expected values worked out by hand in
m35/predictions.md."""
import unittest

import a6_r3 as r3
import a6_r3m as m
import a6_r3n as n
import m32
import sat_aniso as sa


class TestCandidates(unittest.TestCase):
    def test_s_choices(self):
        self.assertEqual(n.s_choices(6, (4, 2, 1)), [2, 4, 6])
        self.assertEqual(n.s_choices(4, (2, 1)), [2])
        self.assertEqual(n.s_choices(4, (8, 1)), [8])
        self.assertEqual(n.s_choices(2, (1,)), [])

    def test_b5_count(self):
        """(B5) at t = 6: X_1 = R = span(e_0, e_1, e_2), s = e_1: 8^4 matrices."""
        ms = n.candidate_matrices(6, "B", 5, (4, 2, 1), (4, 2, 1), 2)
        self.assertEqual(len(ms), 4096)
        self.assertEqual(len(set(ms)), 4096)
        for N in ms[::97]:
            self.assertTrue(n.satisfies_conditions(6, "B", 5, (4, 2, 1), 2, N))
        self.assertEqual(ms[0], 0)

    def test_t4_exact(self):
        """t = 4, shape ("B", 3), X_1 = span(e_0, e_1), R = span(e_2, e_3), s = e_1: the built set
        equals the brute force over all 2^16 matrices."""
        built = n.candidate_matrices(4, "B", 3, (2, 1), (8, 4), 2)
        brute = sorted(N for N in range(1 << 16) if n.satisfies_conditions(4, "B", 3, (8, 4), 2, N))
        self.assertEqual(built, brute)
        self.assertEqual(len(built), 16)          # 2 middle vectors (e_2, e_3) with images in R

    def test_normalise_and_act(self):
        ident = m.identity(6)
        self.assertEqual(n.normalise(49, 128, 2113664), (48, 2113536))
        self.assertEqual(n.normalise(48, 2113536, 2113664), (48, 2113536))
        self.assertEqual(n.act(ident, ident, 49, 128, 2113664, 6), (48, 2113536))


class TestStabiliser(unittest.TestCase):
    def test_t2_trivial(self):
        """t = 2: with A_u = E_11, R = span(e_1) and X_1 = span(e_0) only the identity remains."""
        self.assertEqual(n.stabiliser(2, "B", 1, (1,), (2,), 8), [m.identity(2)])
        self.assertEqual(n.stabiliser(2, "A", 1, (1,), (2,), 8), [m.identity(2)])

    def test_t4_brute_force(self):
        t, s, p, rho = 4, "B", 3, 2
        G = m.group_elements(t, s, p)
        self.assertEqual(len(G), 168)
        x1, r, size = r3.orbits(t, s, p, rho)[0]
        rep, mem = m.classes(t, s, p, x1, r, seed=f"m30-{t}-{s}{p}-0")[0]
        X1, R = r3.rref(list(x1)), r3.rref(list(r))
        brute = sorted(g for g in G if r3.image(g, X1, t) == X1 and r3.image(g, R, t) == R
                       and m.conj(g, rep, t) == rep)
        HA = n.stabiliser(t, s, p, x1, r, rep)
        self.assertEqual(HA, brute)
        self.assertEqual(len(HA) * len(mem) * size, 168)

    def test_constraints_commute(self):
        """Every element found commutes with A and fixes e_0."""
        t, s, p = 4, "A", 3
        x1, r, _ = r3.orbits(t, s, p, 2)[0]
        rep = m.classes(t, s, p, x1, r, seed=f"m30-{t}-{s}{p}-0")[0][0]
        for g in n.stabiliser(t, s, p, x1, r, rep):
            self.assertEqual(sa.mat_apply(g, 1, t), 1)
            self.assertEqual(sa.mat_mul(g, rep, t), sa.mat_mul(rep, g, t))
            self.assertTrue(r3.in_group(g, t, s, p))


class TestControls(unittest.TestCase):
    def test_hand_values(self):
        As, ss, B, x1, r, au = m32.direct_sum_control(False)
        self.assertEqual((ss[1], As[1], au), (49, 128, 2113664))
        self.assertTrue(n.satisfies_conditions(6, "B", 3, r, 49, 128))
        As, ss, B, x1, r, au = m32.direct_sum_control(True)
        self.assertEqual((ss[1], As[1], au), (51, 1152, 2114688))
        self.assertTrue(n.satisfies_conditions(6, "B", 3, r, 51, 1152))
        self.assertNotEqual(m32.transpose(1152, 6), 1152)
        self.assertEqual(m32.transpose(1152, 6), 33554560)
        self.assertEqual(sa.mat_apply(33554560, 51, 6), 2 + 16)      # e_1 + e_4 != 0
        self.assertEqual(128 ^ 2113664, 2113536)

    def test_control_specs(self):
        sps = n.control6n_specs()
        self.assertEqual([sp["name"] for sp in sps],
                         ["ctl6n_diag", "ctl6n_diag_shift", "ctl6n_skew", "ctl6n_skew_transposed"])
        self.assertEqual([sp["expect"] for sp in sps], ["SAT", "SAT", "SAT", "UNSAT"])
        self.assertEqual([sp["au"] for sp in sps], [2113664, 2113664, 2114688, 2114688])

    def test_hand_checks(self):
        st = n.control6n_hand()
        for name, row in st.items():
            for k, v in row.items():
                if k != "a1_symmetric":
                    self.assertTrue(v, f"{name}: {k}")
        self.assertFalse(st["ctl6n_skew"]["a1_symmetric"])
        self.assertTrue(st["ctl6n_diag"]["a1_symmetric"])


class TestEncoding(unittest.TestCase):
    def test_unit_clause_bits(self):
        """The unit clauses for A_(h_1) = 1152 (entries (1, 1), (1, 4)) and sigma(h_1) = 51."""
        As, ss, B, x1, r, au = m32.direct_sum_control(True)
        cnf, names = n.encode_r3n(6, 6, "B", 3, 3, x1, r, au, 51, 1152)
        A, S = names[0], names[1]
        self.assertIn([A[1][1][4]], cnf.clauses)
        self.assertIn([-A[1][4][1]], cnf.clauses)
        self.assertIn([A[1][1][1]], cnf.clauses)
        self.assertIn([-A[1][0][0]], cnf.clauses)
        self.assertIn([S[1][0]], cnf.clauses)
        self.assertIn([S[1][1]], cnf.clauses)
        self.assertIn([-S[1][2]], cnf.clauses)
        self.assertIn([S[1][5]], cnf.clauses)


class TestProbe(unittest.TestCase):
    def test_targets_match_m32(self):
        for key, idx, cls, au, minutes, group in n.PROBE:
            self.assertEqual(m32.EXPECTED_AU[f"r3m_t6_r3_{key}_o{idx:03d}_m{cls:03d}"], au)
            self.assertEqual(sa.rank_f2(sa.rows_of(au, 6)), 3)
            self.assertLessEqual(minutes, group)

    def test_hand_orders(self):
        go = r3.group_order(6, "B", 5)
        self.assertEqual(go, 9999360)
        for (idx, cls), order in n.HAND_H_ORDER.items():
            self.assertEqual(go // n.HAND_ORBIT_SIZES[idx] // n.HAND_CLASS_SIZES[(idx, cls)], order)
            self.assertEqual(go % n.HAND_ORBIT_SIZES[idx], 0)
            self.assertEqual((go // n.HAND_ORBIT_SIZES[idx]) % n.HAND_CLASS_SIZES[(idx, cls)], 0)

    def test_names(self):
        self.assertEqual(n.instance_name(6, 3, "B", 5, 9, 5, 12), "r3n_t6_r3_B5_o009_m005_n012")
        self.assertTrue(n.instance_name(6, 3, "B", 5, 9, 5, 12).startswith(
            n.class_prefix(6, 3, "B", 5, 9, 5)))

    def test_budget(self):
        self.assertLessEqual(sum(g for _, _, _, _, _, g in n.PROBE), 110)


if __name__ == "__main__":
    unittest.main()
