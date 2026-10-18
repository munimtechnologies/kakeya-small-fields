# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import sat_aniso as sa
import shape_c as sc
import shape_c3 as s3


def random_coords(rng, t, k, Ms, good):
    """Random coordinates (As, ss, B); if good, with (D), (W) and (K) forced (k <= 3, where only
    y = e_1 + e_2 involves a value of beta)."""
    d = t + k - 1
    m = t - k
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
    low = (1 << k) - 1
    for yb in range(1, 1 << (k - 1)):
        M = s3.m_of_y(Ms, yb)
        target = rng.choice([z for z in range(1 << m) if sa.mat_apply(M, z, m) == 0])
        if bin(yb).count("1") == 1:
            i = s3.w_index(k, yb.bit_length())
            ss[i] = (ss[i] & low) | (target << k)
        else:
            key = (s3.w_index(k, 1), s3.w_index(k, 2))
            B[key] ^= (s3.q_of(ss, B, k, yb) ^ target) << k
    return As, ss, B


def added_ok(cnf, base, names, As, ss, B, t, d):
    val = sa.assignment(cnf, names, As, ss, B, t, d)
    return all(any(val[lit] if lit > 0 else not val[-lit] for lit in cl)
               for cl in cnf.clauses[base:])


class TestFilter(unittest.TestCase):
    def test_selfcheck_grades(self):
        st = s3.selfcheck()
        self.assertTrue(all(st["graded"].values()), st)

    def test_kept_is_orbit_invariant(self):
        # Conjugating and recombining a kept pair keeps it kept, and an unkept one unkept.
        rng = random.Random(5)
        g3 = sc.gl(3)
        g2 = sc.gl(2)
        for tup, _, _ in sc.orbits(3, 2):
            g = rng.choice(g3)
            R = rng.choice(g2)
            img = sc.act(g, sa.mat_inv(g, 3), R, tup, 3)
            self.assertEqual(s3.all_singular(img, 3), s3.all_singular(tup, 3))

    def test_field_orbits_dropped(self):
        # Every orbit whose span contains an invertible matrix is dropped, in particular the 5
        # field orbits of Corollary 23(d).
        kept = {i for i, _ in s3.kept_orbits(3, 2)}
        for i, (tup, _, _) in enumerate(sc.orbits(3, 2)):
            inv = any(sa.rank_f2(sa.rows_of(s3.m_of_y(tup, yb), 3)) == 3 for yb in (1, 2, 3))
            self.assertEqual(i in kept, not inv)


class TestEncoding(unittest.TestCase):
    def check_agreement(self, t, k, cases, seed):
        rng = random.Random(seed)
        d = t + k - 1
        seen = set()
        for _, Ms in s3.kept_orbits(t - k, k - 1)[:4]:
            cnf, names = sc.encode_split(t, k, Ms)
            base = len(cnf.clauses)
            nv = cnf.nv
            s3.add_d3(cnf, names, t, k, Ms)
            if k <= 2:
                # Only (D), (W) and parity equations on at most m variables: no new variables.
                self.assertEqual(cnf.nv, nv)
            for n in range(cases):
                good = n % 2 == 0
                As, ss, B = random_coords(rng, t, k, Ms, good)
                want = s3.satisfies_d3(As, ss, B, t, k, Ms)
                if good:
                    self.assertTrue(want)
                self.assertEqual(added_ok(cnf, base, names, As, ss, B, t, d), want)
                seen.add(want)
                # One-bit changes: the CNF and the direct check still agree.
                for _ in range(3):
                    As2, ss2, B2 = list(As), list(ss), dict(B)
                    which = rng.randrange(3)
                    if which == 0:
                        i = rng.randrange(d)
                        As2[i] ^= 1 << rng.randrange(t * t)
                    elif which == 1:
                        i = rng.randrange(d)
                        ss2[i] ^= 1 << rng.randrange(t)
                    else:
                        key = rng.choice(sorted(B2))
                        B2[key] ^= 1 << rng.randrange(t)
                    self.assertEqual(added_ok(cnf, base, names, As2, ss2, B2, t, d),
                                     s3.satisfies_d3(As2, ss2, B2, t, k, Ms))
        self.assertEqual(seen, {True, False})

    def test_agreement_4_2(self):
        self.check_agreement(4, 2, 30, 11)

    def test_agreement_6_3(self):
        self.check_agreement(6, 3, 8, 13)

    def test_fixed_bits_rejected(self):
        # Each bit fixed by (D) or (W) is rejected when flipped from a good point.
        t, k = 6, 3
        rng = random.Random(17)
        _, Ms = s3.kept_orbits(3, 2)[-1]
        As, ss, B = random_coords(rng, t, k, Ms, True)
        self.assertTrue(s3.satisfies_d3(As, ss, B, t, k, Ms))
        for r in range(k, t):
            for c in range(k, t):
                As2 = list(As)
                As2[0] ^= 1 << (t * r + c)
                self.assertFalse(s3.satisfies_d3(As2, ss, B, t, k, Ms))
        for j in (1, 2):
            i = s3.w_index(k, j)
            for r in range(k, t):
                for c in range(t):
                    As2 = list(As)
                    As2[i] ^= 1 << (t * r + c)
                    self.assertFalse(s3.satisfies_d3(As2, ss, B, t, k, Ms))

    def test_needs_t_2k(self):
        with self.assertRaises(ValueError):
            s3.encode_d3(5, 2, (0,))


if __name__ == "__main__":
    unittest.main()
