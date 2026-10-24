# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m102.py (job m102, notes/a94.md). Needs m42.py, sat_aniso.py, m100.py, m101.py
and python-sat next to it."""
import itertools
import random
import unittest

import m100
import m101
import m102
import sat_aniso as sa

AU00 = m100.PAIRS[0][2][0][0]
# job m101, r3b_t8_B7_o000_c000_relax_n.child.json: anisotropic on N, A_(v_2) = A_(v_3) = A_u J pi
M101_A = [2113664, 0, 14737632, 14737632, 11574427464381693950, 4629771175354653438,
          11574427466409584254, 11574428061145114238, 6510792576876936954, 2658571006874254308,
          11194323665462273701]
M101_S = [1, 18, 20, 30, 178, 170, 187, 187, 250, 238, 232]
M101_B = [[0, 1, 0], [0, 2, 0], [0, 3, 0], [0, 4, 2], [0, 5, 4], [0, 6, 8], [0, 7, 16], [0, 8, 32],
          [0, 9, 64], [0, 10, 128], [1, 2, 0], [1, 3, 0], [1, 4, 24], [1, 5, 0], [1, 6, 18],
          [1, 7, 10], [1, 8, 0], [1, 9, 0], [1, 10, 18], [2, 3, 0], [2, 4, 0], [2, 5, 30],
          [2, 6, 10], [2, 7, 10], [2, 8, 246], [2, 9, 232], [2, 10, 252], [3, 4, 0], [3, 5, 30],
          [3, 6, 0], [3, 7, 0], [3, 8, 246], [3, 9, 232], [3, 10, 246], [4, 5, 24], [4, 6, 26],
          [4, 7, 26], [4, 8, 24], [4, 9, 170], [4, 10, 170], [5, 6, 28], [5, 7, 4], [5, 8, 232],
          [5, 9, 68], [5, 10, 66], [6, 7, 10], [6, 8, 50], [6, 9, 234], [6, 10, 50], [7, 8, 42],
          [7, 9, 242], [7, 10, 32], [8, 9, 30], [8, 10, 18], [9, 10, 180]]


def solve(clauses):
    from pysat.solvers import Solver
    for name in sa.SOLVERS:
        try:
            s = Solver(name=name, bootstrap_with=clauses)
        except Exception:
            continue
        ok = s.solve()
        s.delete()
        return ok
    raise RuntimeError("no SAT solver available")


def rebase(As, ss, Bl, a, b):
    """The same system in the basis with v_a replaced by v_a + v_b."""
    B = {(i, k): v for i, k, v in Bl}

    def bget(i, k):
        return 0 if i == k else B[m101.bkey(i, k)]

    As2, ss2 = list(As), list(ss)
    As2[a] = As[a] ^ As[b]
    ss2[a] = ss[a] ^ ss[b] ^ bget(a, b)
    B2 = {}
    for i, k in B:
        if a in (i, k):
            other = k if i == a else i
            B2[(i, k)] = bget(a, other) ^ bget(b, other)
        else:
            B2[(i, k)] = B[(i, k)]
    return As2, ss2, [[i, k, v] for (i, k), v in sorted(B2.items())]


class TestM102(unittest.TestCase):
    def test_gl3(self):
        self.assertEqual(len(m102.GL3), 168)
        self.assertEqual(m102.I3, 273)
        for g in m102.GL3:
            self.assertEqual(m102.mm3(g, m102.INV3[g]), m102.I3)

    def test_a_of_t(self):
        self.assertEqual(m102.a_of_t(AU00, m102.I3), AU00)
        self.assertEqual(m102.a_of_t(AU00, 0), 0)
        self.assertEqual(m102.a_of_t(AU00, m102.J3), 14737632)
        rng = random.Random(102)
        for _ in range(40):
            tm = rng.randrange(512)
            a = m102.a_of_t(AU00, tm)
            for x in range(256):
                want = sa.mat_apply(AU00, sa.mat_apply(tm, x >> 5, 3) << 5, 8)
                self.assertEqual(sa.mat_apply(a, x, 8), want)

    def test_lift_g(self):
        rng = random.Random(7)
        swap01 = sa.entries(3, [(1, 0), (0, 1), (2, 2)])
        swap02 = sa.entries(3, [(2, 0), (1, 1), (0, 2)])
        for gq in (m102.I3, swap01):
            g = m102.lift_g(AU00, gq, rng)
            self.assertIsNotNone(g)
            self.assertTrue(m102.g_ok(AU00, gq, g))
        # A_u e_7 = e_0, so g e_7 = e_5 mod X_1 would force g e_0 = A_u e_5 = e_2
        self.assertIsNone(m102.lift_g(AU00, swap02, rng))
        # the permutation e_1 <-> e_2, e_5 <-> e_6 is a lift of swap01, and g_ok accepts it
        perm = sa.from_cols([1, 4, 2, 8, 16, 64, 32, 128], 8)
        self.assertTrue(m102.g_ok(AU00, swap01, perm))
        self.assertFalse(m102.g_ok(AU00, m102.I3, perm))

    def test_cases(self):
        self.assertEqual([len(m102.n0_ws(c)) for c in
                          (m102.case_t1(), m102.case_t2(5), m102.case_t3(5, 6))], [7, 3, 1])
        self.assertEqual(m102.n0_ws(m102.case_t2(5)), [(1,), (2,), (1, 2)])
        self.assertEqual(m102.case_label(m102.case_t2(5)), "t2_m005")
        self.assertEqual(m102.case_label(m102.case_t3(5, 46)), "t3_m005_046")
        self.assertEqual(m102.inst_name(m100.spec_of(0, 0), m102.case_t1()),
                         "r3b_t8_B7_o000_c000_t1")
        self.assertEqual(m102.basis_of((0, 1, 272, 273)), [1])

    def test_case_two_w(self):
        t, d = 8, 4
        rng = random.Random(1021)
        cases = []
        for w in [(1, 2), (2,), (1, 2, 3)]:
            zero = {k: 0 for k in itertools.combinations(range(d), 2)}
            one12 = dict(zero)
            one12[(1, 2)] = 1
            cases.append((w, [0, 1, 0, 0], zero))
            cases.append((w, [0, 2, 3, 0], one12))
            for _ in range(15):
                cases.append((w, [rng.randrange(32) for _ in range(d)],
                              {k: rng.randrange(32) for k in itertools.combinations(range(d), 2)}))
        for w, ss, bv in cases:
            cnf = sa.CNF()
            S = [[cnf.new() for _ in range(t)] for _ in range(d)]
            B = {key: [cnf.new() for _ in range(t)] for key in itertools.combinations(range(d), 2)}
            n = m102.add_case_two_w(cnf, (None, S, B), t, d, w)
            self.assertEqual(n, 1 + sum(1 for j in range(d) if [i for i in w if i != j]))
            for i in range(d):
                cnf.clauses += [[S[i][r]] if (ss[i] >> r) & 1 else [-S[i][r]] for r in range(t)]
            for key, v in bv.items():
                cnf.clauses += [[B[key][r]] if (v >> r) & 1 else [-B[key][r]] for r in range(t)]
            want = 1 not in m100.span(m102.model_gens(ss, bv, w, d))
            self.assertEqual(solve(cnf.clauses), want, (w, ss, bv))
        # by hand: sigma(v_1 + v_2) = 2 + 3 + 1 = 0 and beta(v_1 + v_2, e_0) = 1
        bv = {k: 0 for k in itertools.combinations(range(d), 2)}
        bv.update({(1, 2): 1, (0, 1): 1})
        self.assertEqual(m102.model_gens([0, 2, 3, 0], bv, (1, 2), d), [0, 1, 1, 1, 0])

    def test_orbits_cover(self):
        two, three = m102.t_spaces()
        self.assertEqual(len(m102.orbits(two, [m102.I3])), len(two))
        self.assertEqual(sum(n for _, n in m102.orbits(two, m102.GL3)), len(two))
        self.assertEqual(sum(n for _, n in m102.orbits(three, m102.GL3)), len(three))
        for s in two + three:
            self.assertEqual(sorted(m100.span([m102.I3] + m102.basis_of(s))), list(s))

    def test_known_model(self):
        """Job m101's relax_n model, with v_2 replaced by v_2 + v_3, is a model of the t2 case with
        M = J: every check that the relax_n mode needs holds outside the encoder."""
        As, ss, Bl = rebase(M101_A, M101_S, M101_B, 2, 3)
        self.assertEqual((As[2], As[3]), (0, m102.a_of_t(AU00, m102.J3)))
        spec = m100.spec_of(0, 0)
        res = {"A": As, "s": ss, "B": Bl}
        chk = m101.check_model(spec, res)
        chk.update(m102.extra_checks(spec, m102.case_t2(m102.J3), res))
        for key in m102.needed(spec, "relax_n"):
            self.assertTrue(chk[key], key)
        self.assertFalse(m102.extra_checks(spec, m102.case_t2(m102.I3 ^ 1), res)["t_maps"])


if __name__ == "__main__":
    unittest.main()
