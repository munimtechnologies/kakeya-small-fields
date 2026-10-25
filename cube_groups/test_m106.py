# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m106.py (job m106, notes/a98.md). Needs m42.py, sat_aniso.py, m100.py, m101.py,
m102.py, m103.py, m104.py, m105.py and python-sat next to it. Every expected value below was worked
out by hand; add_aniso_masks is tested against what the solver needs (sigma(h) != 0), not against
its own output."""
import itertools
import random
import unittest

import m101
import m102
import m104
import m106
import sat_aniso as sa

T, D = m106.T, m106.D


def fake_names(cnf):
    S = [[cnf.new() for _ in range(T)] for _ in range(D)]
    B = {(i, k): [cnf.new() for _ in range(T)] for i, k in itertools.combinations(range(D), 2)}
    return None, S, B


def evaluate(cnf, val):
    """Extends val (S and B variables) to every auxiliary variable, as sat_aniso.assignment."""
    for v in sorted(cnf.defs):
        kind = cnf.defs[v]
        if kind[0] == "and":
            val[v] = val[kind[1]] and val[kind[2]]
        else:
            val[v] = sum(val[x] for x in kind[1]) % 2 == 1
    return all(any(val[x] if x > 0 else not val[-x] for x in c) for c in cnf.clauses)


class TestM106(unittest.TestCase):
    def test_names(self):
        self.assertEqual(m106.vec_name(1), "u")
        self.assertEqual(m106.vec_name(0b1010), "v1+v3")
        self.assertEqual(m106.vec_name(256 | 1024), "h5+h7")
        self.assertEqual(m106.vec_name(0), "0")

    def test_order(self):
        # 7 has three terms, 3 two, then 2 before 1
        self.assertEqual(m106.deletion_order([1, 3, 2, 7]), [7, 3, 2, 1])

    def test_minimize(self):
        def oracle(s):
            return "UNSAT" if {1, 2} <= set(s) else "SAT"
        kept, why, log = m106.minimize([1, 2, 3, 4], oracle)
        # order 3, 4, 2, 1: 3 and 4 go, 2 and 1 stay (removing either gives SAT)
        self.assertEqual(kept, [2, 1])
        self.assertEqual(why, {2: "SAT", 1: "SAT"})
        self.assertEqual(len(log), 5)
        self.assertTrue(m106.proven({"kept": kept, "why": why}))
        self.assertEqual(m106.minimize([3, 4], oracle)[0], None)
        self.assertFalse(m106.proven({"kept": None, "why": {}}))

    def test_minimize_unknown(self):
        def oracle(s):
            if 1 in s:
                return "UNSAT" if 4 in s else "UNKNOWN"
            return "SAT"
        kept, why, _ = m106.minimize([1, 4], oracle)
        self.assertEqual(kept, [4, 1])
        self.assertEqual(why, {4: "UNKNOWN", 1: "SAT"})
        self.assertFalse(m106.proven({"kept": kept, "why": why}))

    def test_aniso_clause_means_sigma_nonzero(self):
        rng = random.Random(106)
        for h in (1, 6, 7, 256 | 512, 15, 1 | 2 | 1024, (1 << D) - 1):
            for _ in range(12):
                cnf = sa.CNF()
                names = fake_names(cnf)
                self.assertEqual(m106.add_aniso_masks(cnf, names, T, [h]), 1)
                ss = [rng.getrandbits(T) for _ in range(D)]
                if rng.random() < 0.3:
                    ss = [0] * D
                Bv = {key: rng.getrandbits(T) if rng.random() < 0.7 else 0 for key in names[2]}
                val = {}
                for i in range(D):
                    for r in range(T):
                        val[names[1][i][r]] = bool((ss[i] >> r) & 1)
                for key, vs in names[2].items():
                    for r in range(T):
                        val[vs[r]] = bool((Bv[key] >> r) & 1)
                _, sv = sa.tables([0] * D, ss, Bv, D)
                self.assertEqual(evaluate(cnf, val), sv[h] != 0)

    def test_same_size_as_add_aniso_on(self):
        for idx in ([0, 1, 2, 3], [8, 9, 10], [0, 1, 2, 3, 8]):
            c1, c2 = sa.CNF(), sa.CNF()
            n1, n2 = fake_names(c1), fake_names(c2)
            a = m101.add_aniso_on(c1, n1, T, idx)
            b = m106.add_aniso_masks(c2, n2, T, m104.w_masks(idx))
            self.assertEqual(a, b)
            self.assertEqual((len(c1.clauses), c1.nv), (len(c2.clauses), c2.nv))

    def test_unknown_list(self):
        self.assertEqual(len(set(m106.UNKNOWN_D2)), 28)
        self.assertTrue(all(len(x) > 20 and x[19] == "_" for x in m106.UNKNOWN_D2))

    def test_case_of(self):
        spec, case = m106.case_of("r3b_t8_B7_o004_c001_t3_m002_132")
        self.assertEqual((spec["pair"], spec["cls"]), (4, 1))
        self.assertEqual(m102.case_label(case), "t3_m002_132")
        self.assertEqual(case["maps"], [2, 132])


if __name__ == "__main__":
    unittest.main()
