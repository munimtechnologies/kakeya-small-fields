# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m95.py (job m95). m93's orbits, the encodings at (8, 4) against m94's and the
anisotropy count at (8, 4) are in --part selfcheck, which the job runs as its own step."""
import unittest

import m94
import m95 as m
import sat_aniso as sa

N1, N2 = m94.SHIFT, m94.SHIFT2
AU6 = (0, 0, 0, 8, 1, 2)            # t = 6, f = 1: [e_3] -> e_3 (outside X_1), [e_4] -> e_0, [e_5] -> e_1


def a_cols(t, k, au, M):
    """The columns of A_(v_i) that (S) asks for (as in test_m94.py)."""
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


def new_clauses_hold(t, k, Ms, f, au, Bs=None):
    """Do the clauses that encode_rank4 adds hold on the data (A_u, A_(v_i), beta(v_i, .))?"""
    cnf, names, info = m.encode_rank4(t, k, Ms, f)
    A, Bv = names[0], names[2]
    As = [list(au)] + [a_cols(t, k, au, M) for M in Ms]
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


class TestM95(unittest.TestCase):
    def test_hyperplanes_pilot(self):
        # W = span(E_00, E_12, E_11 + E_22): rows 0, 2 and 3 give invariant hyperplanes.
        self.assertEqual(m.hyperplanes(m94.pilot_ms()), [1, 4, 8])
        self.assertTrue(m.invariant(m94.pilot_ms(), 8))
        self.assertFalse(m.invariant(m94.pilot_ms(), 2))
        self.assertEqual(m.hyperplanes([N1, N2]), [1])

    def test_d_basis(self):
        self.assertEqual(m.d_basis(8, 4), [1, 2, 4])
        self.assertEqual(m.d_basis(5, 4), [2, 5, 8])
        for f in range(1, 16):
            b = m.d_basis(f, 4)
            self.assertEqual(sa.rank_f2(b), 3)
            self.assertTrue(all(not m.parity(f & v) for v in b))
            self.assertTrue(m.parity(f & (1 << m.low_bit(f))))

    def test_equal_to_m94_t6(self):
        mine, _, info = m.encode_rank4(6, 3, [N1, N2])
        theirs, _, _ = m94.encode_n4(6, 3, [N1, N2])
        self.assertEqual(mine.clauses, theirs.clauses)
        self.assertEqual(mine.nv, theirs.nv)
        self.assertEqual([info[x] for x in ("units", "outside", "inv", "lin", "a_units")],
                         [9, 0, 7, 36, 30])
        self.assertEqual([info["vars"], info["clauses"], info["start"], info["first_var"]],
                         m.M94_SIZES[(6, 3)])
        self.assertEqual(m.relax(mine, 6), (1 << 8) - 1)

    def test_counts_d3_t6(self):
        _, _, info = m.encode_rank4(6, 3, [N1, N2], 1)
        self.assertEqual([info[x] for x in ("units", "outside", "inv", "lin", "a_units")],
                         [6, 1, 7, 36, 30])
        _, _, info = m.encode_rank4(6, 3, [N1, N2], 1, ("lin", "a"))
        self.assertEqual([info[x] for x in ("units", "outside", "inv", "lin", "a_units")],
                         [6, 1, 7, 0, 0])

    def test_rejects(self):
        with self.assertRaises(ValueError):
            m.encode_rank4(6, 3, [N1, N2], 4)           # ker e_2^T is not invariant under N
        with self.assertRaises(ValueError):
            m.build({"t": 6, "k": 3, "w": None, "f": 1, "relax": True})

    def test_d3_clauses_on_data(self):
        self.assertTrue(new_clauses_hold(6, 3, [N1, N2], 1, AU6))
        # [e_3] -> e_0: T maps all of F_2^3 into X_1, so (O) fails.
        self.assertFalse(new_clauses_hold(6, 3, [N1, N2], 1, (0, 0, 0, 1, 2, 4)))
        # [e_4] -> e_4 leaves X_1 although [e_4] is in D: (D) fails.
        self.assertFalse(new_clauses_hold(6, 3, [N1, N2], 1, (0, 0, 0, 8, 16, 2)))
        # [e_4] and [e_5] -> e_0: T is not one-to-one.
        self.assertFalse(new_clauses_hold(6, 3, [N1, N2], 1, (0, 0, 0, 8, 1, 1)))
        # beta(v_i, .) built from the other matrix: (a) fails.
        self.assertFalse(new_clauses_hold(6, 3, [N1, N2], 1, AU6, b_vals(6, 3, [N2, N1])))

    def test_fixed_parts(self):
        Ms = [N1, N2]
        As = [sa.from_cols(list(AU6), 6)] + [sa.from_cols(a_cols(6, 3, AU6, M), 6) for M in Ms]
        self.assertEqual(m.fixed_parts(As, b_vals(6, 3, Ms), 6, 3, Ms, 1),
                         {"units": True, "inv": True, "lin": True, "a": True})
        self.assertFalse(m.fixed_parts(As, b_vals(6, 3, Ms), 6, 3, Ms)["units"])
        bad = [sa.from_cols([0, 0, 0, 8, 1, 1], 6)] + As[1:]
        parts = m.fixed_parts(bad, b_vals(6, 3, Ms), 6, 3, Ms, 1)
        self.assertFalse(parts["inv"])
        self.assertFalse(parts["lin"])
        self.assertFalse(m.fixed_parts(As, b_vals(6, 3, [N2, N1]), 6, 3, Ms, 1)["a"])

    def test_specs(self):
        orbits = [{"index": 0, "basis": [1, 64, 1056], "size": 10080, "n4": True,
                   "hyper": [1, 4, 8]},
                  {"index": 7, "basis": [2, 4, 8], "size": 960, "n4": False, "hyper": [2]}]
        a = m.group_specs("a", orbits)
        b = m.group_specs("b", orbits)
        self.assertEqual([s["name"] for s in a], ["n4_o00_s10080"])
        self.assertEqual([s["name"] for s in b],
                         ["d3_o00_f01", "d3_o00_f04", "d3_o00_f08", "d3_o07_f02"])
        self.assertTrue(all(s["f"] is None for s in a))
        lad = m.ladder_specs()
        self.assertEqual([s["name"] for s in lad], [x[0] for x in m.LADDER])
        self.assertEqual([bool(s.get("relax")) for s in lad], [True, True] + [False] * 5)
        self.assertEqual(lad[-1]["drop"], ["lin", "a"])


if __name__ == "__main__":
    unittest.main()
