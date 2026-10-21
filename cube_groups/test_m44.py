# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m44.py (job m44). The classification at t = 6 and t = 7 and the hand counts of
Lemma 85 are in --part selfcheck, which the job runs as its own step."""
import unittest

import m44 as m
import sat_aniso as sa

# A nilpotent 3 x 3 matrix N (N[l][j], column j = image of basis vector j) and N^2: I, N, N^2 span a
# commutative space of dimension 3 in which every non-zero element is non-zero (Corollary 51's form).
N1 = [[0, 0, 0], [1, 0, 0], [0, 1, 0]]
N2 = [[0, 0, 0], [0, 0, 0], [1, 0, 0]]
E00 = [[1, 0, 0], [0, 0, 0], [0, 0, 0]]
AU6 = (0, 0, 0, 1, 2, 4)                        # t = 6: A_u e_3 = e_0, e_4 = e_1, e_5 = e_2


def a_cols(t, au, M):
    n = t - m.K
    cols = [0] * m.K
    for j in range(n):
        x = 0
        for l in range(n):
            if M[l][j]:
                x ^= au[m.K + l]
        cols.append(x)
    return cols


def b_vals(t, M1, M2):
    out = {}
    for i, M in ((1, M1), (2, M2)):
        for j in range(1, t):
            v = 5
            if j >= m.K:
                v |= sum(M[l][j - m.K] << (m.K + l) for l in range(t - m.K))
            out[(i, 2 + j)] = v
    return out


def hints_hold(t, au, M1, M2, A1=None, A2=None):
    """Do the hint clauses of encode_class hold on data (A_(v_1), A_(v_2), beta(v_i, v_(2+j)),
    M_1, M_2)? A_(v_i) default to the matrices that (S) asks for."""
    cnf, names, info = m.encode_class(t, au)
    A, Bv = names[0], names[2]
    A1 = a_cols(t, au, M1) if A1 is None else A1
    A2 = a_cols(t, au, M2) if A2 is None else A2
    val = {}
    for i, cols in ((1, A1), (2, A2)):
        for r in range(t):
            for c in range(t):
                val[A[i][r][c]] = bool((cols[c] >> r) & 1)
    for key, v in b_vals(t, M1, M2).items():
        for r in range(t):
            val[Bv[key][r]] = bool((v >> r) & 1)
    for i, M in ((1, M1), (2, M2)):
        for l in range(t - m.K):
            for j in range(t - m.K):
                val[info["M"][i][l][j]] = bool(M[l][j])
    for v in sorted(cnf.defs):
        if v < info["first_var"]:
            continue
        kind = cnf.defs[v]
        if kind[0] == "and":
            val[v] = val[kind[1]] and val[kind[2]]
        else:
            val[v] = sum(val[x] for x in kind[1]) % 2 == 1
    return all(any(val[x] if x > 0 else not val[-x] for x in cl) for cl in cnf.clauses[info["start"]:])


class TestM44(unittest.TestCase):
    def test_group_order(self):
        for t, n in m.HAND_K.items():
            self.assertEqual(m.group_order(t), n)
        self.assertEqual(len(m.group_elements(5)), 576)

    def test_generators(self):
        self.assertEqual(len(m.generators(7)), 22)
        self.assertEqual(len(m.generators(5)), 8)
        self.assertTrue(all(m.in_group(g, 7) for g in m.generators(7)))
        # e_1 -> e_1 + e_3 leaves W, e_3 -> e_3 + e_0 and e_1 -> e_1 + e_0 leave P: none is in K.
        self.assertFalse(m.in_group(m.identity(7) ^ (1 << (7 * 3 + 1)), 7))
        self.assertFalse(m.in_group(m.identity(7) ^ (1 << (7 * 0 + 3)), 7))
        self.assertFalse(m.in_group(m.identity(7) ^ (1 << (7 * 0 + 1)), 7))

    def test_candidates(self):
        self.assertEqual(len(m.candidates(7)), 995)
        self.assertEqual(len(m.candidates(6)), 99)
        self.assertEqual(len(m.candidates(5)), 7)

    def test_r_orbit_totals(self):
        for t in (5, 6, 7):
            orbs = m.r_orbits(t)
            self.assertEqual(sum(s for _, s in orbs), m.HAND_R[t])
            self.assertTrue(all(m.group_order(t) % s == 0 for _, s in orbs))
            self.assertTrue(all(m.r_type(t, r) is not None for r, _ in orbs))

    def test_matrices(self):
        r = m.rref([1, 2, 4, 8])
        mats = m.matrices(7, r)
        self.assertEqual(len(mats), 20160)
        self.assertTrue(all(A[:3] == (0, 0, 0) and m.rref(list(A)) == r for A in mats[:500]))
        self.assertEqual(len(m.matrices(6, m.rref([1, 2, 4]))), 168)
        self.assertEqual(len(m.matrices(5, m.rref([2, 4]))), 6)

    def test_conj(self):
        t = 7
        g = m.generators(t)[-1]
        A = m.matrices(t, m.rref([1, 2, 4, 8]))[123]
        want = sa.mat_mul(sa.mat_mul(g, sa.from_cols(list(A), t), t), sa.mat_inv(g, t), t)
        self.assertEqual(m.conj(m.unit_pair(g, t), A), tuple(m.cols_of(want, t)))
        self.assertEqual(m.conj(m.unit_pair(m.identity(t), t), A), A)

    def test_units(self):
        r = m.rref([2, 4, 8, 16])
        units, st = m.random_units(7, m.stab_subs(7, r), 8, 5)
        self.assertEqual(len(units), 8)
        self.assertTrue(all(m.in_group(g, 7, (r,)) for g in units))

    def test_exact_t5(self):
        ex = m.exact_check(5)
        self.assertEqual(ex["group"], 576)
        self.assertTrue(ex["stabilisers"] and ex["classes_exact"])

    def test_encoding_t5(self):
        info = m.hint_info(5, m.classify(5)[0])
        self.assertEqual(info["lin"], m.HAND_LIN[5])
        self.assertEqual(info["nonzero"], m.NONZERO)
        self.assertEqual(info["units"], m.AU_UNITS[5])
        self.assertTrue(info["consistent"])

    def test_hints_on_data(self):
        self.assertTrue(hints_hold(6, AU6, N1, N2))
        # M_2 = M_1: M_(v_1 + v_2) = 0, against Corollary 51.
        self.assertFalse(hints_hold(6, AU6, N1, N1))
        # N1 and E00 do not commute.
        self.assertFalse(hints_hold(6, AU6, N1, E00))
        # A_(v_1) taken from N^2 while M_1 = N1: (S) fails.
        self.assertFalse(hints_hold(6, AU6, N1, N2, A1=a_cols(6, AU6, N2)))


if __name__ == "__main__":
    unittest.main()
