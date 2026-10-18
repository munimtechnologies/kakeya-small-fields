# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import case_a as ca
import sat_aniso as sa


class TestOrbits(unittest.TestCase):
    def test_candidates(self):
        # By hand (notes/case-a.md): an injective map X/X_1 -> X with image a (t - 2)-space that
        # contains e_1: (number of such spaces) x |GL_(t-2)| = 1 x 1, 7 x 6, 35 x 168.
        for t, (n, _, _) in ca.HAND.items():
            cands = ca.candidates(t)
            self.assertEqual(len(cands), n)
            for A in cands[:50]:
                self.assertEqual(sa.mat_apply(A, 1, t), 0)
                self.assertEqual(sa.mat_apply(A, 2, t), 0)
                self.assertEqual(ca.kernel_dim(A, t), 2)

    def test_group(self):
        for t, (_, order, _) in ca.HAND.items():
            G = ca.group(t)
            self.assertEqual(len(G), order)
            self.assertEqual(ca.group_order(t), order)
            for g in G[:200]:
                self.assertEqual(sa.mat_apply(g, 1, t), 1)
                self.assertEqual(sa.mat_apply(g, 2, t), 2)
                self.assertEqual(sa.rank_f2(sa.rows_of(g, t)), t)
        for t in (3, 4, 5):
            for g in ca.generators(t):
                self.assertEqual(sa.mat_mul(g, g, t), ca.identity(t))

    def test_orbits_against_hand_counts(self):
        for t, (n, order, sizes) in ca.HAND.items():
            orb = ca.orbits(t)
            self.assertEqual(sorted(o[1] for o in orb), sizes)
            self.assertEqual(sum(o[1] for o in orb), n)
            for A, size in orb:
                self.assertEqual(size * ca.stabiliser(A, t), order)
            ds = [ca.invariants(o[0], t)[0] for o in orb]
            self.assertEqual(ds.count(2), ca.HAND_D2[t])
            self.assertEqual(ds.count(1), len(sizes) - ca.HAND_D2[t])

    def test_representatives_are_least(self):
        rng = random.Random(4)
        for t in (4, 5):
            G = ca.group(t)
            cands = set(ca.candidates(t))
            for A, _ in ca.orbits(t):
                for g in rng.sample(G, min(300, len(G))):
                    B = sa.mat_mul(sa.mat_mul(g, A, t), sa.mat_inv(g, t), t)
                    self.assertGreaterEqual(B, A)
                    self.assertIn(B, cands)


def synthetic(t, Au, rng):
    """Coordinates in the normal form of Lemma 48 with A_u = Au; everything else random."""
    d = t + 1
    As = [Au] + [rng.getrandbits(t * t) for _ in range(t)]
    ss = [1, 2] + [rng.randrange(1 << t) for _ in range(t - 1)]
    B = {key: rng.randrange(1 << t) for key in itertools.combinations(range(d), 2)}
    for i in range(1, d):
        B[(0, i)] = ca.wanted_phi(i)
    return As, ss, B


class TestEncoding(unittest.TestCase):
    def test_units_added(self):
        for t in (3, 4, 5):
            base, _ = sa.encode(t, t + 1, echelon=False)
            for Au, _ in ca.orbits(t)[:3]:
                cnf, _ = ca.encode_case_a(t, Au)
                self.assertEqual(cnf.nv, base.nv)
                self.assertEqual(cnf.clauses[:len(base.clauses)], base.clauses)
                added = cnf.clauses[len(base.clauses):]
                self.assertEqual(len(added), ca.unit_count(t))
                self.assertTrue(all(len(cl) == 1 for cl in added))

    def test_normal_form_accepted_and_flips_rejected(self):
        rng = random.Random(9)
        for t in (4, 5):
            d = t + 1
            for Au, _ in ca.orbits(t):
                cnf, names = ca.encode_case_a(t, Au)
                added = cnf.clauses[len(sa.encode(t, d, echelon=False)[0].clauses):]

                def ok(As, ss, B):
                    val = sa.assignment(cnf, names, As, ss, B, t, d)
                    return all(any(val[x] if x > 0 else not val[-x] for x in cl) for cl in added)

                As, ss, B = synthetic(t, Au, rng)
                self.assertTrue(ca.in_normal_form(As, ss, B, t, Au))
                self.assertTrue(ok(As, ss, B))
                for _ in range(4):
                    As2, ss2, B2 = list(As), list(ss), dict(B)
                    which = rng.randrange(4)
                    if which == 0:
                        As2[0] ^= 1 << rng.randrange(t * t)
                    elif which == 1:
                        ss2[rng.randrange(2)] ^= 1 << rng.randrange(t)
                    else:
                        B2[(0, rng.randrange(1, d))] ^= 1 << rng.randrange(t)
                    self.assertFalse(ca.in_normal_form(As2, ss2, B2, t, Au))
                    self.assertFalse(ok(As2, ss2, B2))
                # values outside the normal form are free
                As3 = list(As)
                As3[1] ^= 1
                self.assertTrue(ok(As3, ss, B))

    def test_selfcheck_grades(self):
        st = ca.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])


if __name__ == "__main__":
    unittest.main()
