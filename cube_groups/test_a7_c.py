# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import a7_c
import sat_aniso as sa
import shape_c as sc
import shape_c3 as s3


def random_coords(rng, t, k, Ms, good):
    """Random coordinates (As, ss, B); if good, with (D), (W), (K), (U) and (G) forced. In (K), q(y)
    is set through sigma for one e_j and through beta for two; for three (k = 4) it is fixed by the
    rest, so good points are drawn until it fits."""
    d = t + k - 1
    m = t - k
    low = (1 << k) - 1
    for _ in range(500):
        As = [rng.getrandbits(t * t) for _ in range(d)]
        ss = [rng.getrandbits(t) for _ in range(d)]
        B = {(i, j): rng.getrandbits(t) for i, j in itertools.combinations(range(d), 2)}
        if not good:
            return As, ss, B
        for r in range(k, t):
            for c in range(k, t):
                As[0] &= ~(1 << (t * r + c))
        for j, M in enumerate(Ms, start=1):
            i = s3.w_index(k, j)
            for l in range(m):
                for c in range(t):
                    bit = 1 << (t * (k + l) + c)
                    want = c >= k and (M >> (m * l + c - k)) & 1
                    As[i] = As[i] | bit if want else As[i] & ~bit
        for j in range(1, k):
            B[(1, s3.w_index(k, j))] &= 2
        wk = s3.w_index(k, 1)
        for r in range(k):
            As[wk] &= ~(1 << (t * r + 1))
        for yb in sorted(range(1, 1 << (k - 1)), key=lambda y: bin(y).count("1")):
            bits = [j for j in range(k - 1) if (yb >> j) & 1]
            if len(bits) > 2:
                continue
            M = s3.m_of_y(Ms, yb)
            target = rng.choice([z for z in range(1 << m) if sa.mat_apply(M, z, m) == 0])
            if len(bits) == 1:
                i = s3.w_index(k, bits[0] + 1)
                ss[i] = (ss[i] & low) | (target << k)
            else:
                key = (s3.w_index(k, bits[0] + 1), s3.w_index(k, bits[1] + 1))
                B[key] ^= (s3.q_of(ss, B, k, yb) ^ target) << k
        if a7_c.satisfies_a7(As, ss, B, t, k, Ms):
            return As, ss, B
    raise AssertionError("no good coordinates found")


def added_ok(cnf, base, names, As, ss, B, t, d):
    val = sa.assignment(cnf, names, As, ss, B, t, d)
    return all(any(val[lit] if lit > 0 else not val[-lit] for lit in cl)
               for cl in cnf.clauses[base:])


class TestInstances(unittest.TestCase):
    def test_selfcheck_grades(self):
        st = a7_c.selfcheck()
        self.assertTrue(all(st["graded"].values()), st)

    def test_reps(self):
        self.assertEqual(a7_c.reps(3, 2), [(0, (0,))])
        r74 = a7_c.reps(7, 4)
        self.assertEqual([i for i, _ in r74], [i for i, _ in s3.kept_orbits(3, 2)])
        self.assertEqual([Ms[1:] for _, Ms in r74], [tuple(p) for _, p in s3.kept_orbits(3, 2)])
        for t, k in ((3, 2), (5, 3), (7, 4)):
            for _, Ms in a7_c.reps(t, k):
                self.assertEqual(len(Ms), k - 1)
                self.assertEqual(Ms[0], 0)
        with self.assertRaises(ValueError):
            a7_c.reps(6, 3)

    def test_schur_bound_is_attained(self):
        # The bound m is reached: the 3 x 3 diagonal matrices commute, contain I and span a space
        # of dimension 3, so the check of selfcheck() is about the right number.
        self.assertTrue(a7_c.commuting_dim_ok(2))
        diag3 = [sa.entries(3, [(r, r)]) for r in range(3)]
        self.assertEqual(sa.rank_f2(diag3), 3)
        self.assertIn(sc.identity(3), a7_c.span_set(diag3))
        for A, B in itertools.combinations(diag3, 2):
            self.assertEqual(sa.mat_mul(A, B, 3), sa.mat_mul(B, A, 3))
        self.assertEqual(len(a7_c.span_set(diag3)), 8)

    def test_encode_checks(self):
        with self.assertRaises(ValueError):
            a7_c.encode_a7(6, 3, (0, 0))
        with self.assertRaises(ValueError):
            a7_c.encode_a7(5, 3, (1, 0))


class TestEncoding(unittest.TestCase):
    def check_agreement(self, t, k, which, cases, seed):
        rng = random.Random(seed)
        d = t + k - 1
        seen = set()
        todo = a7_c.reps(t, k)
        for pos in which:
            _, Ms = todo[pos]
            cnf, names = sc.encode_split(t, k, Ms)
            base = len(cnf.clauses)
            a7_c.add_a7(cnf, names, t, k, Ms)
            for n in range(cases):
                good = n % 2 == 0
                As, ss, B = random_coords(rng, t, k, Ms, good)
                want = a7_c.satisfies_a7(As, ss, B, t, k, Ms)
                if good:
                    self.assertTrue(want)
                self.assertEqual(added_ok(cnf, base, names, As, ss, B, t, d), want)
                seen.add(want)
                # One-bit changes: the CNF and the direct check still agree.
                for _ in range(3):
                    As2, ss2, B2 = list(As), list(ss), dict(B)
                    kind = rng.randrange(3)
                    if kind == 0:
                        i = rng.randrange(d)
                        As2[i] ^= 1 << rng.randrange(t * t)
                    elif kind == 1:
                        i = rng.randrange(d)
                        ss2[i] ^= 1 << rng.randrange(t)
                    else:
                        key = rng.choice(sorted(B2))
                        B2[key] ^= 1 << rng.randrange(t)
                    self.assertEqual(added_ok(cnf, base, names, As2, ss2, B2, t, d),
                                     a7_c.satisfies_a7(As2, ss2, B2, t, k, Ms))
        self.assertEqual(seen, {True, False})

    def test_agreement_3_2(self):
        self.check_agreement(3, 2, [0], 20, 21)

    def test_agreement_5_3(self):
        self.check_agreement(5, 3, [0, 1, 2], 8, 23)

    def test_agreement_7_4(self):
        self.check_agreement(7, 4, [0, 15], 4, 29)

    def test_extra_clause_count(self):
        # (U) and (G) add exactly (k - 1)(t - 1) + k unit clauses and no variables.
        for t, k in ((3, 2), (5, 3)):
            for _, Ms in a7_c.reps(t, k):
                cnf1, names1 = sc.encode_split(t, k, Ms)
                s3.add_d3(cnf1, names1, t, k, Ms)
                cnf2, _ = a7_c.encode_a7(t, k, Ms)
                self.assertEqual(len(cnf2.clauses) - len(cnf1.clauses), a7_c.extra_count(t, k))
                self.assertEqual(cnf2.nv, cnf1.nv)
                self.assertTrue(all(len(cl) == 1 for cl in cnf2.clauses[len(cnf1.clauses):]))

    def test_extra_bits_rejected(self):
        # Flipping any bit fixed by (U) or (G) at a good point is rejected.
        t, k = 5, 3
        rng = random.Random(31)
        _, Ms = a7_c.reps(t, k)[-1]
        As, ss, B = random_coords(rng, t, k, Ms, True)
        for j in range(1, k):
            key = (1, s3.w_index(k, j))
            for c in range(t):
                if c != 1:
                    B2 = dict(B)
                    B2[key] ^= 1 << c
                    self.assertFalse(a7_c.satisfies_a7(As, ss, B2, t, k, Ms))
        wk = s3.w_index(k, 1)
        for r in range(k):
            As2 = list(As)
            As2[wk] ^= 1 << (t * r + 1)
            self.assertFalse(a7_c.satisfies_a7(As2, ss, B, t, k, Ms))


if __name__ == "__main__":
    unittest.main()
