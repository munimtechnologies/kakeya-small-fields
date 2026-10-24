# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m96.py (job m96). The comparisons at (6, 3) and (8, 4) with m94's CNFs and m95b's
sizes are in --part selfcheck, which the job runs as its own step."""
import time
import unittest

import m94
import m96 as m

N1, N2 = m94.SHIFT, m94.SHIFT2
AU6 = (0, 0, 0, 8, 1, 2)            # t = 6, f = 1: [e_3] -> e_3 (outside X_1), [e_4] -> e_0, [e_5] -> e_1
NEW = ("units", "outside", "inv", "lin", "a")


def a_cols(t, k, au, M):
    """The columns of A_(v_i) that (S) asks for (as in test_m95.py)."""
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


def failing(t, k, Ms, f, au, Bs=None):
    """The groups of the new families (type, T one-to-one, (S), (a)) whose clauses fail on the data
    (A_u, A_(v_i), beta(v_i, .))."""
    cnf, names, labels, info = m.build(t, k, Ms, f)
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
        val[v] = sum(val[x] for x in kind[1]) % 2 == 1
    bad = set()
    for c, lab in zip(cnf.clauses[info["start"]:], labels[info["start"]:]):
        if not any(val[x] if x > 0 else not val[-x] for x in c):
            bad.add(lab)
    return {m.family(x) for x in bad}


class TestM96(unittest.TestCase):
    def test_equal_to_m94_t4(self):
        for M in m.T4.values():
            cnf, _, labels, _ = m.build(4, 2, [M])
            theirs, _, _ = m94.encode_n4(4, 2, [M])
            self.assertEqual(cnf.clauses, theirs.clauses)
            self.assertEqual(cnf.nv, theirs.nv)
            self.assertEqual(len(labels), len(cnf.clauses))
            self.assertEqual(labels.count("aniso"), 31)
            self.assertEqual(m.family_counts(labels), {"nf": 7, "shape": 3, "units": 2, "inv": 3,
                                                       "lin": 2, "a": 3, "aniso": 1})
            self.assertTrue(all(x is None or x == "aniso" or m.family(x) in
                                ("nf", "shape") + NEW for x in labels))

    def test_d3_labels_t6(self):
        cnf, _, labels, info = m.build(6, 3, [N1, N2], 1)
        fams = m.family_counts(labels)
        self.assertEqual({k: fams[k] for k in NEW}, {"units": 2, "outside": 1, "inv": 7,
                                                    "lin": 6, "a": 10})
        self.assertEqual(sorted({x for x in labels if x and x.startswith("units")}),
                         ["units:D2", "units:D4"])
        # before info["start"] only (*), anisotropy, the normal form and shape (c)
        self.assertTrue(all(x is None or m.family(x) in ("aniso", "nf", "shape")
                            for x in labels[:info["start"]]))
        self.assertTrue(all(m.family(x) in NEW for x in labels[info["start"]:]))

    def test_groups_on_data(self):
        self.assertEqual(failing(6, 3, [N1, N2], 1, AU6), set())
        # [e_3] -> e_0: T maps all of F_2^3 into X_1, so (O) fails.
        self.assertEqual(failing(6, 3, [N1, N2], 1, (0, 0, 0, 1, 2, 4)), {"outside"})
        # [e_4] -> e_4 leaves X_1 although [e_4] is in D: (D) fails.
        self.assertIn("units", failing(6, 3, [N1, N2], 1, (0, 0, 0, 8, 16, 2)))
        # [e_4] and [e_5] -> e_0: T is not one-to-one.
        self.assertIn("inv", failing(6, 3, [N1, N2], 1, (0, 0, 0, 8, 1, 1)))
        # beta(v_i, .) built from the other matrix: (a) fails, nothing else.
        self.assertEqual(failing(6, 3, [N1, N2], 1, AU6, b_vals(6, 3, [N2, N1])), {"a"})
        # d = 4: [e_3] -> e_3 is not in X_1, so (N4) fails, and in rows 0 to 2 (the only rows
        # the one-to-one clauses of (N4) read) that column is 0.
        self.assertEqual(failing(6, 3, [N1, N2], None, AU6), {"units", "inv"})
        self.assertEqual(failing(6, 3, [N1, N2], None, (0, 0, 0, 4, 1, 2)), set())

    def test_rejects(self):
        with self.assertRaises(ValueError):
            m.build(6, 3, [N1, N2], 4)              # ker e_2^T is not invariant under N
        with self.assertRaises(ValueError):
            m.build(4, 2, [[[1, 0], [0, 1]]])       # I is excluded

    def test_core_toy(self):
        clauses = [[1], [-1], [2], [-2, 3], [-3]]
        labels = ["x:g1", "x:g2", "x:g3", "x:g4", "x:g5"]
        g = m.Guarded(clauses, labels, 3)
        allg = list(g.groups)
        self.assertEqual(g.solve([], 5)[0], "SAT")
        self.assertEqual(g.solve(["x:g1", "x:g3", "x:g4"], 5)[0], "SAT")
        self.assertEqual(g.solve(allg, 5)[0], "UNSAT")
        res = m.min_core(g, allg, 5, time.time() + 60)
        self.assertIn(set(res["core"]), ({"x:g1", "x:g2"}, {"x:g3", "x:g4", "x:g5"}))
        self.assertTrue(res["minimal"])
        self.assertEqual(res["final"], "UNSAT")
        g.delete()

    def test_bare_t4(self):
        cnf, names, labels, _ = m.build(4, 2, [m.T4["N"]])
        g = m.Guarded(cnf.clauses, labels, cnf.nv)
        self.assertEqual(g.solve([], 30)[0], "SAT")
        chk = m.check_model(g.model(), cnf, names, labels, set(), 4, 2)
        self.assertTrue(chk["clauses_ok"])
        self.assertTrue(chk["system"])
        # the same model read against every group fails somewhere: the full CNF is UNSAT (A(4) = 4)
        self.assertFalse(m.check_model(g.model(), cnf, names, labels, set(g.groups), 4, 2)
                         ["clauses_ok"])
        self.assertEqual(g.solve(list(g.groups), 30)[0], "UNSAT")
        g.delete()

    def test_order(self):
        labs = ["nf:su", "a:v1n3", "inv:3", "lin:v1c0", "units:T0", "shape:s_v1", "outside:O"]
        self.assertEqual(sorted(labs, key=m.order_key),
                         ["a:v1n3", "lin:v1c0", "inv:3", "units:T0", "outside:O", "shape:s_v1",
                          "nf:su"])


if __name__ == "__main__":
    unittest.main()
