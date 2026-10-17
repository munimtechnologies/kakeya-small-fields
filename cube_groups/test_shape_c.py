# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import case_b as cb
import case_b_shapes as cs
import sat_aniso as sa
import shape_c as sc


class TestOrbits(unittest.TestCase):
    def test_commuting_counts(self):
        # By hand (notes/shape-c.md): sum over A of 2^(dim of its centraliser), class by class:
        # 2 x 512 + 2 x 21 x 32 + 2 x 42 x 8 + 2 x (28 x 32 + 84 x 8) + 2 x 24 x 8 + 2 x 56 x 8
        # = 7456, which the Feit-Fine generating function confirms (168 x 932/21). For 2 x 2:
        # 2 x 16 + 14 x 4 = 88.
        self.assertEqual(len(sc.commuting_tuples(1, 1)), 2)
        self.assertEqual(len(sc.commuting_tuples(2, 1)), 16)
        self.assertEqual(len(sc.commuting_tuples(2, 2)), 88)
        self.assertEqual(len(sc.commuting_tuples(3, 2)), 7456)

    def test_small_orbits(self):
        # r = 1: conjugacy classes of M_m(F_2): 2, 6, 14. m = r = 2: (0, 0), one orbit for each of
        # the 5 non-zero classes, and the 3 classes of planes span(I, M): 9, of sizes summing to 88.
        self.assertEqual(len(sc.orbits(1, 1)), 2)
        self.assertEqual(len(sc.orbits(2, 1)), 6)
        self.assertEqual(len(sc.orbits(3, 1)), 14)
        o22 = sc.orbits(2, 2)
        self.assertEqual(len(o22), 9)
        self.assertEqual(sorted(o[1] for o in o22), [1, 3, 6, 6, 9, 9, 18, 18, 18])

    def test_orbit_stabiliser_3_2(self):
        big = sc.orbits(3, 2)
        self.assertEqual(sum(o[1] for o in big), 7456)
        self.assertTrue(all(o[1] * o[2] == 1008 for o in big))
        dims = [sc.span_dim(o[0], 3) for o in big]
        self.assertEqual(dims.count(0), 1)
        self.assertEqual(dims.count(1), 13)
        # every representative commutes and is the least tuple of its orbit
        for tup, _, _ in big:
            self.assertEqual(sa.mat_mul(tup[0], tup[1], 3), sa.mat_mul(tup[1], tup[0], 3))
        rng = random.Random(7)
        group = [(g, sa.mat_inv(g, 3), R) for g in sc.gl(3) for R in sc.gl(2)]
        for tup, _, _ in rng.sample(big, 5):
            self.assertEqual(min(sc.act(g, gi, R, tup, 3) for g, gi, R in group), tup)

    def test_act_is_an_action(self):
        rng = random.Random(3)
        tups = sc.commuting_tuples(3, 2)
        G, R = sc.gl(3), sc.gl(2)
        for _ in range(20):
            tup = rng.choice(tups)
            g1, g2 = rng.choice(G), rng.choice(G)
            r1, r2 = rng.choice(R), rng.choice(R)
            once = sc.act(g1, sa.mat_inv(g1, 3), r1, tup, 3)
            twice = sc.act(g2, sa.mat_inv(g2, 3), r2, once, 3)
            g, r = sa.mat_mul(g1, g2, 3), sa.mat_mul(r2, r1, 2)
            self.assertEqual(sc.act(g, sa.mat_inv(g, 3), r, tup, 3), twice)
            self.assertIn(twice, set(tups))


def synthetic(t, k, Ms, rng):
    """Coordinates in the normal form of shape c whose A_(v_i) satisfy (S) for Ms, with a random
    A_u that is one-to-one on span(e_k, ..., e_(t-1)) (other values 0)."""
    d = t + k - 1
    m = t - k
    while True:
        cols = [rng.randrange(1 << t) for _ in range(m)]
        if sa.rank_f2(cols) == m:
            break
    As = [0] * d
    As[0] = sa.from_cols([0] * k + cols, t)
    for i, M in enumerate(Ms, start=1):
        acol = []
        for j in range(m):
            c = sa.mat_apply(M, 1 << j, m)
            acol.append(sa.combine(cols, c))
        As[i] = sa.from_cols([0] * k + acol, t)
    ss = [0] * d
    ss[0] = 1
    for i in range(1, k):
        ss[i] = 1 << i
    B = {key: 0 for key in itertools.combinations(range(d), 2)}
    for i in range(1, d):
        B[(0, i)] = cb.wanted_phi(i, k)
    return As, ss, B


class TestEncoding(unittest.TestCase):
    def test_clauses_added(self):
        rng = random.Random(5)
        for t, k in ((3, 2), (4, 2), (6, 3)):
            base, _ = cs.encode_shape(t, k, "c")
            reps = [o[0] for o in sc.orbits(t - k, k - 1)]
            for Ms in rng.sample(reps, min(4, len(reps))):
                cnf, _ = sc.encode_split(t, k, Ms)
                self.assertEqual(cnf.nv, base.nv)
                self.assertEqual(cnf.clauses[:len(base.clauses)], base.clauses)
                self.assertEqual(len(cnf.clauses) - len(base.clauses),
                                 sc.split_clause_count(t, k, Ms))
        # M_1 = 0 at (3, 2): A_(v_1) e_2 = 0, one unit clause per row
        cnf, names = sc.encode_split(3, 2, (0,))
        base, _ = cs.encode_shape(3, 2, "c")
        A = names[0]
        self.assertEqual(cnf.clauses[len(base.clauses):], [[-A[1][r][2]] for r in range(3)])

    def test_synthetic_accepted_and_flips_rejected(self):
        rng = random.Random(11)
        for t, k in ((4, 2), (6, 3)):
            d = t + k - 1
            reps = [o[0] for o in sc.orbits(t - k, k - 1)]
            for Ms in rng.sample(reps, min(5, len(reps))):
                As, ss, B = synthetic(t, k, Ms, rng)
                self.assertTrue(cs.in_shape(As, ss, B, t, k, "c"))
                self.assertTrue(sc.satisfies_split(As, t, k, Ms))
                for i in range(1, k):
                    self.assertEqual(sc.m_of(As, 1 << i, t, k), Ms[i - 1])
                self.assertEqual(sc.m_of(As, 1, t, k), sc.identity(t - k))
                cnf, names = sc.encode_split(t, k, Ms)
                nbase = len(cs.encode_shape(t, k, "c")[0].clauses)
                added = cnf.clauses[nbase:]

                def ok(As2):
                    val = sa.assignment(cnf, names, As2, ss, B, t, d)
                    return all(any(val[x] if x > 0 else not val[-x] for x in cl) for cl in added)

                self.assertTrue(ok(As))
                for _ in range(6):
                    As2 = list(As)
                    i = rng.randrange(1, k)
                    As2[i] ^= 1 << (t * rng.randrange(t) + k + rng.randrange(t - k))
                    self.assertFalse(sc.satisfies_split(As2, t, k, Ms))
                    self.assertFalse(ok(As2))

    def test_m_of_needs_injective_t(self):
        t, k = 6, 3
        As = [0] * 8
        As[0] = sa.from_cols([0, 0, 0, 8, 8, 16], t)
        self.assertIsNone(sc.m_of(As, 1, t, k))

    def test_selfcheck_grades(self):
        st = sc.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])


if __name__ == "__main__":
    unittest.main()
