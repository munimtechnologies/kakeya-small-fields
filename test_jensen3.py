# SPDX-License-Identifier: Apache-2.0
"""Tests for jensen3.py (note a166: Theorem 42, Lemmas 117-119, Proposition 50,
Theorem 43, Corollary 132).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only. Every assertion is a fact proved by hand in a166 (or in
a163-a165), so a failure means a bug in the code or an error in a hand proof.
The commit carrying a166 ships only if all of them pass.
"""

import random
import unittest

import jensen3 as j3


def regular_random(q, rng):
    while True:
        T = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
        if j3.is_regular(T, q):
            return T


def jordan_examples(q):
    """Regular matrices of each Jordan shape, all defined over F_q (q >= 5)."""
    diag = [[1, 0, 0], [0, 2, 0], [0, 0, 3]]
    j21 = [[1, 1, 0], [0, 1, 0], [0, 0, 2]]
    j3_ = [[1, 1, 0], [0, 1, 1], [0, 0, 1]]
    comp = [[0, 0, q - 1], [1, 0, q - 1], [0, 1, 0]]  # companion of x^3 + x + 1
    return [diag, j21, j3_, comp]


class TestJensen(unittest.TestCase):
    """Theorem 42: Lambda(P) <= q log2(1 + Pibar/q) for EVERY map P of F_q^k."""

    def test_arbitrary_maps(self):
        rng = random.Random(42)
        for q, k, n in ((3, 2, 25), (3, 3, 4), (5, 2, 6)):
            for _ in range(n):
                tab = j3.table_of(j3.random_map(q, rng, k), q, k)
                sizes = j3.fibre_sizes(tab, q, k)
                self.assertTrue(j3.jensen_holds(sizes, q, k), (q, k))

    def test_degree_two_maps(self):
        rng = random.Random(7)
        for q, n in ((3, 10), (5, 4), (7, 2)):
            for _ in range(n):
                tab = j3.table_of(j3.random_quadratic(q, rng), q)
                self.assertTrue(j3.jensen_holds(j3.fibre_sizes(tab, q), q), q)
        for q in (3, 5, 7):
            tab = j3.table_of(j3.E_map(q), q)
            self.assertTrue(j3.jensen_holds(j3.fibre_sizes(tab, q), q), q)

    def test_pair_total_is_sum_of_pi(self):
        rng = random.Random(11)
        for q in (3, 5):
            for f in (j3.random_quadratic(q, rng), j3.E_map(q), j3.type_b(q, rng)):
                tab = j3.table_of(f, q)
                cls = j3.classify(tab, q)
                total = sum(v[2] for v in cls.values())
                self.assertEqual(total, j3.pair_total(j3.fibre_sizes(tab, q)))


class TestProp47(unittest.TestCase):
    """a164 Prop 47 (q odd, degree 2): Pi_w = (q-1) q^(3-r_w) if active, else 0; and the
    closed form of sum_w Pi_w when there is no full direction."""

    def test_formula(self):
        rng = random.Random(5)
        maps = []
        for q in (3, 5):
            maps += [(q, j3.random_quadratic(q, rng)), (q, j3.E_map(q)),
                     (q, j3.type_b(q, rng)), (q, j3.family(q, 1, 2))]
        maps.append((7, j3.E_map(7)))
        for q, f in maps:
            tab = j3.table_of(f, q)
            cls = j3.classify(tab, q)
            for w, (r, act, pi) in cls.items():
                self.assertEqual(pi, (q - 1) * q ** (3 - r) if act else 0, (q, w))
            full = [w for w, (r, act, _) in cls.items() if act and r == 0]
            if not full:
                nD = sum(1 for (r, act, _) in cls.values() if act and r == 1)
                nZ0 = sum(1 for (r, act, _) in cls.values() if not act)
                total = sum(v[2] for v in cls.values())
                self.assertEqual(total, q * j3.pibar_formula_times_q2(q, nD, nZ0))


class TestProp51(unittest.TestCase):
    """sum_w q^(3-r_w) = sum_x e(M_x), where M_x w = beta(x, w) and e(M) counts the
    directions w with M w in F_q w; hence sum_w Pi_w <= (q-1) sum_x e(M_x)."""

    def test_identity(self):
        rng = random.Random(41)
        for q in (3, 5):
            for f in (j3.random_quadratic(q, rng), j3.E_map(q), j3.type_b(q, rng)):
                tab = j3.table_of(f, q)
                cls = j3.classify(tab, q)
                dirs = j3.directions(q)
                lhs = sum(q ** (3 - r) for (r, _, _) in cls.values())
                rhs = sum(1 for x in j3.pts(q) for w in dirs
                          if j3.parallel(w, j3.beta(tab, x, w, q), q))
                self.assertEqual(lhs, rhs, q)
                total = sum(v[2] for v in cls.values())
                self.assertLessEqual(total, (q - 1) * rhs, q)


class TestLemma117(unittest.TestCase):
    """A nonzero ternary cubic form has at most 3(q+1) zeros in PG(2,q) (q >= 5)."""

    def count_zeros(self, coeffs, monos, q):
        n = 0
        for w in j3.directions(q):
            val = 0
            for (a, b, c), co in zip(monos, coeffs):
                val += co * w[0] ** a * w[1] ** b * w[2] ** c
            n += (val % q == 0)
        return n

    def test_random_cubics(self):
        monos = [(a, b, 3 - a - b) for a in range(4) for b in range(4 - a)]
        self.assertEqual(len(monos), 10)
        rng = random.Random(3)
        for q in (5, 7):
            for _ in range(60):
                co = [rng.randrange(q) for _ in monos]
                if not any(co):
                    continue
                self.assertLessEqual(self.count_zeros(co, monos, q), 3 * (q + 1))
            # three concurrent lines x y (x - y): exactly 3q + 1 zeros
            co = [0] * 10
            co[monos.index((2, 1, 0))] = 1
            co[monos.index((1, 2, 0))] = q - 1
            self.assertEqual(self.count_zeros(co, monos, q), 3 * q + 1)


class TestLemma118(unittest.TestCase):
    """For regular T: {A : det(w, Tw, Aw) == 0 identically} = span(I, T)."""

    def check(self, T, q):
        self.assertTrue(j3.is_regular(T, q))
        rows = j3.span_lemma_rows(T, q)
        self.assertEqual(9 - j3.rank(rows, q), 2, (q, T))
        I = [1 if i == j else 0 for i in range(3) for j in range(3)]
        Tf = [T[i][j] % q for i in range(3) for j in range(3)]
        for row in rows:
            self.assertEqual(sum(a * b for a, b in zip(row, I)) % q, 0)
            self.assertEqual(sum(a * b for a, b in zip(row, Tf)) % q, 0)

    def test_jordan_shapes(self):
        for q in (5, 7):
            for T in jordan_examples(q):
                self.check(T, q)

    def test_random_regular(self):
        rng = random.Random(9)
        for q in (5, 7):
            for _ in range(6):
                self.check(regular_random(q, rng), q)


class TestLemma119(unittest.TestCase):
    """For regular T, a(y)w + b(y)Tw = a(w)y + b(w)Ty forces a = b = 0."""

    def test_only_zero(self):
        rng = random.Random(13)
        for q in (5, 7):
            Ts = jordan_examples(q) + [regular_random(q, rng) for _ in range(6)]
            for T in Ts:
                self.assertEqual(j3.rank(j3.symmetric_rows(T, q), q), 6, (q, T))


class TestProp50(unittest.TestCase):
    """If all columns beta(e_j, w) and Lw lie in span(w, Tw) for every w: regular T forces
    beta = 0; T = aI + u psi^T forces beta in F_q u and L = sI mod u (P respects F_q u)."""

    def test_regular(self):
        rng = random.Random(17)
        for q in (5, 7):
            for T in jordan_examples(q) + [regular_random(q, rng) for _ in range(3)]:
                basis = j3.nullspace(j3.pencil_system_rows(T, q), 27, q)
                self.assertTrue(basis)  # L = I is always a solution
                for v in basis:
                    self.assertTrue(all(c == 0 for c in v[:18]), (q, T))

    def test_non_regular(self):
        rng = random.Random(19)
        for q in (5, 7):
            for _ in range(6):
                a = rng.randrange(q)
                u = (0, 0, 0)
                while not any(u):
                    u = tuple(rng.randrange(q) for _ in range(3))
                psi = (0, 0, 0)
                while not any(psi):
                    psi = tuple(rng.randrange(q) for _ in range(3))
                T = [[((a if i == j else 0) + u[i] * psi[j]) % q for j in range(3)]
                     for i in range(3)]
                self.assertFalse(j3.is_regular(T, q))
                basis = j3.nullspace(j3.pencil_system_rows(T, q), 27, q)
                self.assertTrue(basis)
                found_beta = False
                for v in basis:
                    for val in j3.solution_beta(v).values():
                        self.assertTrue(j3.parallel(u, val, q), (q, T))
                        found_beta = found_beta or any(val)
                    L = j3.solution_L(v)
                    ok = False
                    for s in range(q):
                        cols = [tuple((L[l][m] - (s if l == m else 0)) % q for l in range(3))
                                for m in range(3)]
                        if all(j3.parallel(u, col, q) for col in cols):
                            ok = True
                            break
                    self.assertTrue(ok, (q, T))
                self.assertTrue(found_beta)  # beta with values in F_q u does occur


class TestTheorem43(unittest.TestCase):
    """C_q(3) for every degree-<=2 map (q odd), through the case split of the proof."""

    def run_map(self, q, f, expect_respects=None):
        tab = j3.table_of(f, q)
        sizes = j3.fibre_sizes(tab, q)
        self.assertTrue(j3.conjecture_holds(sizes, q), q)
        self.assertTrue(j3.jensen_holds(sizes, q), q)
        resp = j3.respects_subspace(tab, q)
        if expect_respects is not None:
            self.assertEqual(resp, expect_respects, q)
        if resp or j3.quadratic_part_zero(tab, q):
            return resp
        cls = j3.classify(tab, q)
        # no full direction when no subspace is respected
        self.assertFalse(any(act and r == 0 for (r, act, _) in cls.values()), q)
        if q >= 5:
            # Proposition 50: Z is not the whole plane, so Lemma 117 bounds Z(F_q)
            self.assertFalse(j3.z_is_whole_plane(tab, q), q)
            Z = set(j3.rational_Z(tab, q))
            D = {w for w, (r, act, _) in cls.items() if act and r == 1}
            self.assertTrue(D <= Z, q)
            self.assertLessEqual(len(Z), 3 * q + 3, q)
        # the Jensen bound itself is already below 3(q-1)
        self.assertTrue(j3.jensen_strict_below(sizes, q), q)
        return resp

    def test_q3(self):
        rng = random.Random(23)
        for _ in range(25):
            self.run_map(3, j3.random_quadratic(3, rng))
        for _ in range(5):
            self.run_map(3, j3.type_b(3, rng))
        self.run_map(3, j3.E_map(3), expect_respects=False)

    def test_q5(self):
        rng = random.Random(29)
        for _ in range(6):
            self.run_map(5, j3.random_quadratic(5, rng))
        for _ in range(4):
            self.run_map(5, j3.type_b(5, rng))
        for rho, delta in ((2, 0), (0, 0), (1, 2)):  # (2, 0) is E at q = 5
            self.run_map(5, j3.family(5, rho, delta), expect_respects=False)

    def test_q7(self):
        rng = random.Random(31)
        self.run_map(7, j3.random_quadratic(7, rng))
        self.run_map(7, j3.type_b(7, rng))
        self.run_map(7, j3.E_map(7), expect_respects=False)

    def test_line_respecting_have_full_Z(self):
        """The shape P = sx + h(x)u + const respects F_q u and has Z = P^2."""
        rng = random.Random(37)
        for q in (5, 7):
            tab = j3.table_of(j3.line_respecting(q, rng), q)
            self.assertTrue(j3.respects_subspace(tab, q))
            self.assertTrue(j3.z_is_whole_plane(tab, q))
            self.assertTrue(j3.conjecture_holds(j3.fibre_sizes(tab, q), q))


class TestNumbers(unittest.TestCase):
    """The arithmetic closing the proof of Theorem 43 and Corollary 132."""

    def test_q3(self):
        # |D| <= 13, Z0 >= 0: q^2 Pibar <= 78; Jensen < 6 iff (27 + 78)^3 < 2^6 27^3
        self.assertEqual(j3.pibar_formula_times_q2(3, 13, 0), 78)
        self.assertLess((27 + 78) ** 3, 64 * 27 ** 3)

    def test_q_at_least_5(self):
        for q in range(5, 1000, 2):
            self.assertEqual(j3.pibar_formula_times_q2(q, 3 * q + 3, 0),
                             (q - 1) * (4 * q * q + q - 2))
            self.assertLess((q - 1) * (4 * q * q + q - 2), 4 * q ** 3)  # Pibar/q < 4
            self.assertLessEqual(5 ** q, 8 ** (q - 1))  # q log2 5 <= 3(q-1)

    def test_kakeya_comparison(self):
        # q 2^(-(q-1)/q) > q/(2 - 1/q)  <=>  2 (2q-1)^q > (2q)^q
        for q in range(3, 200, 2):
            self.assertGreater(2 * (2 * q - 1) ** q, (2 * q) ** q)


if __name__ == "__main__":
    unittest.main()
