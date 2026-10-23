# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m94.py (job m94). The selfchecks of case_b and case_b_shapes, the pilot's orbit
against m93.py and the counts at (8, 4) are in --part selfcheck, which the job runs as its own
step."""
import unittest

import m94 as m
import sat_aniso as sa

N1, N2 = m.SHIFT, m.SHIFT2
E00 = [[1, 0, 0], [0, 0, 0], [0, 0, 0]]
I3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
AU6 = (0, 0, 0, 1, 2, 4)                        # t = 6: [e_3] -> e_0, [e_4] -> e_1, [e_5] -> e_2


def a_cols(t, k, au, M):
    """The columns of A_(v_i) that (S) asks for."""
    n = t - k
    cols = [0] * k
    for j in range(n):
        x = 0
        for l in range(n):
            if M[l][j]:
                x ^= au[k + l]
        cols.append(x)
    return cols


def b_vals(t, k, Ms):
    """beta(v_i, v_(k-1+j)) as (a) asks for in rows k to t - 1, with e_0 + e_2 below."""
    out = {}
    for i, M in enumerate(Ms, 1):
        for j in range(1, t):
            v = 5
            if j >= k:
                v |= sum(M[l][j - k] << (k + l) for l in range(t - k))
            out[(i, k - 1 + j)] = v
    return out


def hints_hold(t, k, Ms, au, As=None, Bs=None):
    """Do the clauses that encode_n4 adds hold on the data (A_u, A_(v_i), beta(v_i, .))?"""
    cnf, names, info = m.encode_n4(t, k, Ms)
    A, Bv = names[0], names[2]
    As = [list(au)] + [a_cols(t, k, au, M) for M in Ms] if As is None else As
    Bs = b_vals(t, k, Ms) if Bs is None else Bs
    val = {}
    for i, cols in enumerate(As):
        for r in range(t):
            for c in range(t):
                val[A[i][r][c]] = bool((cols[c] >> r) & 1)
    for key, v in Bs.items():
        for r in range(t):
            val[Bv[key][r]] = bool((v >> r) & 1)
    for v in sorted(cnf.defs):
        if v < info["first_var"]:
            continue
        kind = cnf.defs[v]
        if kind[0] == "and":
            val[v] = val[kind[1]] and val[kind[2]]
        else:
            val[v] = sum(val[x] for x in kind[1]) % 2 == 1
    return all(any(val[x] if x > 0 else not val[-x] for x in cl)
               for cl in cnf.clauses[info["start"]:])


class TestM94(unittest.TestCase):
    def test_m_of(self):
        self.assertEqual(m.m_of(1, 4)[0], [1, 0, 0, 0])
        self.assertEqual(m.m_of(64, 4), [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
        self.assertEqual(m.m_of(1056, 4),
                         [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]])
        self.assertEqual(m.flat(m.m_of(1056, 4)), 1056)

    def test_tuples(self):
        self.assertTrue(m.check_tuple(m.pilot_ms()))
        self.assertTrue(m.check_tuple([N1, N2]))
        self.assertFalse(m.check_tuple([N1, E00]))      # they do not commute
        self.assertFalse(m.check_tuple([N1, N1]))       # dependent
        self.assertFalse(m.check_tuple([I3, N1]))       # I in the span

    def test_pilot_singular(self):
        Ms = m.pilot_ms()
        for c in range(1, 8):
            x = [[0] * 4 for _ in range(4)]
            for i in range(3):
                if (c >> i) & 1:
                    x = m.add(x, Ms[i])
            rows = [sum(v << j for j, v in enumerate(row)) for row in x]
            self.assertTrue(0 < sa.rank_f2(rows) < 4)

    def test_rejects(self):
        with self.assertRaises(ValueError):
            m.encode_n4(8, 3, m.pilot_ms())
        with self.assertRaises(ValueError):
            m.encode_n4(6, 3, [N1])
        with self.assertRaises(ValueError):
            m.encode_n4(6, 3, [N1, E00])

    def test_counts_t6(self):
        info = m.hint_info(6, 3, [N1, N2])
        for key, want in m.HAND[(6, 3)].items():
            self.assertEqual(info[key], want)
        self.assertTrue(info["consistent"])

    def test_hints_on_data(self):
        self.assertTrue(hints_hold(6, 3, [N1, N2], AU6))
        # A_(v_1) taken from N^2 while M_1 = N: (S) fails.
        As = [list(AU6), a_cols(6, 3, AU6, N2), a_cols(6, 3, AU6, N2)]
        self.assertFalse(hints_hold(6, 3, [N1, N2], AU6, As=As))
        # T singular ([e_5] -> e_0 + e_1): the one-to-one clauses fail.
        au = (0, 0, 0, 1, 2, 3)
        self.assertFalse(hints_hold(6, 3, [N1, N2], au))
        # A_u e_3 = e_0 + e_3 leaves ker A_u: (N4) fails.
        au = (0, 0, 0, 9, 2, 4)
        self.assertFalse(hints_hold(6, 3, [N1, N2], au))
        # beta(v_i, .) built from the other matrix: (a) fails.
        self.assertFalse(hints_hold(6, 3, [N1, N2], AU6, Bs=b_vals(6, 3, [N2, N1])))

    def test_fixed_ok(self):
        Ms = [N1, N2]
        As = [sa.from_cols(list(AU6), 6)] + [sa.from_cols(a_cols(6, 3, AU6, M), 6) for M in Ms]
        self.assertTrue(m.fixed_ok(As, b_vals(6, 3, Ms), 6, 3, Ms))
        self.assertFalse(m.fixed_ok(As, b_vals(6, 3, [N2, N1]), 6, 3, Ms))
        As[1] = sa.from_cols(a_cols(6, 3, AU6, N2), 6)
        self.assertFalse(m.fixed_ok(As, b_vals(6, 3, Ms), 6, 3, Ms))


if __name__ == "__main__":
    unittest.main()
