# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import sat_aniso as sa
import shape_c as sc
import shape_c4 as s4


def low(k):
    return (1 << k) - 1


def set_upper(M, t, k, c, v):
    """Rows r < k of column c of the t x t matrix M := v (a k-bit vector)."""
    for r in range(k):
        bit = 1 << (t * r + c)
        M = M | bit if (v >> r) & 1 else M & ~bit
    return M


def set_lower(M, t, k, c, v):
    """Rows k, ..., t - 1 of column c := v (an m-bit vector)."""
    for l in range(t - k):
        bit = 1 << (t * (k + l) + c)
        M = M | bit if (v >> l) & 1 else M & ~bit
    return M


def random_coords(rng, t, k):
    d = t + k - 1
    As = [rng.getrandbits(t * t) for _ in range(d)]
    ss = [rng.getrandbits(t) for _ in range(d)]
    B = {(i, j): rng.getrandbits(t) for i, j in itertools.combinations(range(d), 2)}
    return As, ss, B


def set_q(ss, B, k, yb, target):
    """Make q(y) = target: through sigma(v_(k-1+j)) for y = e_j, through beta(v_k, v_(k+1)) for
    y = e_1 + e_2 (k <= 3)."""
    hs = s4.hs_of(k, yb)
    if len(hs) == 1:
        i = hs[0]
        ss[i] = (ss[i] & low(k)) | (target << k)
    else:
        key = (hs[0], hs[1])
        B[key] ^= (s4.q_of(ss, B, k, yb) ^ target) << k


def make_units(rng, As, ss, B, t, k, Ms, Ab):
    m = t - k
    a = s4.image_vector(Ab, m)
    for l in range(m):
        for c in range(m):
            bit = 1 << (t * (k + l) + k + c)
            As[0] = As[0] | bit if (Ab >> (m * l + c)) & 1 else As[0] & ~bit
    for i, M in enumerate(Ms, start=1):
        for j in range(1, k):
            key = (i, s4.w_index(k, j))
            B[key] &= low(k)
        for j in range(m):
            key = (i, s4.p_index(k, j))
            B[key] = (B[key] & low(k)) | (sa.mat_apply(M, 1 << j, m) << k)
    for j, M in enumerate(Ms, start=1):
        i = s4.w_index(k, j)
        for c in range(k):
            As[i] = set_lower(As[i], t, k, c, 0)
        for c in range(m):
            As[i] = set_lower(As[i], t, k, k + c,
                              sa.mat_apply(M, 1 << c, m) ^ rng.choice((0, a)))


def make_q(rng, As, ss, B, t, k, Ms, Ab):
    m = t - k
    for yb in range(1, 1 << (k - 1)):
        good = [q for q in range(1 << m) if s4.q_ok(q, Ms, m, Ab, yb)]
        set_q(ss, B, k, yb, rng.choice(good))


def make_t2(rng, As, ss, B, t, k, Ms, Ab):
    lo = low(k)
    for j in range(1, k):
        yb = 1 << (j - 1)
        yv = s4.yvec(yb)
        tq = s4.t_of(As, t, k, s4.q_of(ss, B, k, yb)) & lo
        i = s4.w_index(k, j)
        As[i] = set_upper(As[i], t, k, j, tq ^ yv)
    if k == 3:
        yb = 3
        yv = s4.yvec(yb)
        tq = s4.t_of(As, t, k, s4.q_of(ss, B, k, yb)) & lo
        i3, i4 = s4.w_index(k, 1), s4.w_index(k, 2)
        cur = (sa.mat_apply(As[i3], 1 << 1, t) ^ sa.mat_apply(As[i4], 1 << 1, t)
               ^ sa.mat_apply(As[i4], 1 << 2, t)) & lo
        As[i3] = set_upper(As[i3], t, k, 2, tq ^ yv ^ cur)


def make_j2(rng, As, ss, B, t, k, Ms, Ab):
    m = t - k
    lo = low(k)
    if s4.jtype(Ab, m) != "J":
        return
    a = s4.image_vector(Ab, m)
    ys = s4.unit_ys(Ms, m, a)
    for yb in ys:
        yv = s4.yvec(yb)
        cols = [c for c in range(m) if (a >> c) & 1]
        others = 0
        for c in cols[1:]:
            others ^= sa.mat_apply(As[0], 1 << (k + c), t) & lo
        As[0] = set_upper(As[0], t, k, k + cols[0], yv ^ others)
        set_q(ss, B, k, yb, a)
        hs = s4.hs_of(k, yb)
        if len(hs) == 1:
            for j in range(k):
                want = 0 if (yv >> j) & 1 else rng.choice((0, yv))
                As[hs[0]] = set_upper(As[hs[0]], t, k, j, want)
        else:
            g = rng.choice((0, yv))
            for j in range(k):
                want = g if (yv >> j) & 1 else rng.choice((0, yv))
                cur = sa.mat_apply(As[hs[0]], 1 << j, t) & lo
                As[hs[1]] = set_upper(As[hs[1]], t, k, j, want ^ cur)


MAKERS = {"units": make_units, "q": make_q, "t2": make_t2, "j2": make_j2}


def added_ok(cnf, base, names, As, ss, B, t, d):
    val = sa.assignment(cnf, names, As, ss, B, t, d)
    return all(any(val[lit] if lit > 0 else not val[-lit] for lit in cl)
               for cl in cnf.clauses[base:])


def perturb(rng, As, ss, B, t, d):
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
    return As2, ss2, B2


def j2_instances(t, k):
    m = t - k
    return [x for x in s4.instances(m, k - 1, "J")
            if s4.unit_ys(x[1], m, s4.image_vector(x[2], m))]


class TestOrbits(unittest.TestCase):
    def test_selfcheck_grades(self):
        st = s4.selfcheck()
        self.assertTrue(all(st["graded"].values()), st)

    def test_keep_is_invariant(self):
        # The filter, the type and the number of unit y are the same on every triple of an orbit.
        rng = random.Random(3)
        for m, r in ((2, 1), (3, 2)):
            group = s4.group_elements(m, r)
            trip = s4.triples(m, r)
            for idx, tup, Ab in rng.sample(trip, min(len(trip), 40)):
                g, gi, R = rng.choice(group)
                tup2 = sc.act(g, gi, R, tup, m)
                Ab2 = s4.conj(gi, Ab, g, m)
                self.assertEqual(s4.keep(tup2, m, Ab2), s4.keep(tup, m, Ab))
                self.assertEqual(s4.jtype(Ab2, m), s4.jtype(Ab, m))
                self.assertEqual(len(s4.unit_ys(tup2, m, s4.image_vector(Ab2, m))),
                                 len(s4.unit_ys(tup, m, s4.image_vector(Ab, m))))

    def test_types_and_filters(self):
        for m, r in ((2, 1), (3, 2)):
            for idx, Ms, Ab, ty in s4.instances(m, r):
                self.assertEqual(sa.rank_f2(sa.rows_of(Ab, m)), 1)
                sq = sa.mat_mul(Ab, Ab, m)
                self.assertEqual(ty == "J", sq == 0)
                if ty == "E":
                    self.assertEqual(sq, Ab)
                    self.assertTrue(s4.all_singular(Ms, m))
                    self.assertEqual(s4.unit_ys(Ms, m, s4.image_vector(Ab, m)), [])
                else:
                    self.assertLessEqual(len(s4.unit_ys(Ms, m, s4.image_vector(Ab, m))), 1)
        self.assertTrue(j2_instances(4, 2))
        self.assertTrue(j2_instances(6, 3))


class TestEncoding(unittest.TestCase):
    def family_agreement(self, t, k, fam, cases, picks, seed):
        rng = random.Random(seed)
        d = t + k - 1
        m = t - k
        if fam == "j2":
            insts = j2_instances(t, k)[:picks]
        else:
            insts = s4.instances(m, k - 1)
            insts = [insts[0], insts[-1]] + rng.sample(insts, max(0, picks - 2))
        self.assertTrue(insts)
        seen = set()
        check = s4.CHECKS[fam]
        for idx, Ms, Ab, ty in insts:
            cnf, names = sc.encode_split(t, k, Ms)
            base = len(cnf.clauses)
            s4.ADDERS[fam](cnf, names, t, k, Ms, Ab)
            self.assertGreater(len(cnf.clauses), base)
            for n in range(cases):
                As, ss, B = random_coords(rng, t, k)
                if n % 2 == 0:
                    MAKERS[fam](rng, As, ss, B, t, k, Ms, Ab)
                    self.assertTrue(check(As, ss, B, t, k, Ms, Ab), (fam, idx, Ab))
                want = check(As, ss, B, t, k, Ms, Ab)
                self.assertEqual(added_ok(cnf, base, names, As, ss, B, t, d), want)
                seen.add(want)
                for _ in range(3):
                    As2, ss2, B2 = perturb(rng, As, ss, B, t, d)
                    self.assertEqual(added_ok(cnf, base, names, As2, ss2, B2, t, d),
                                     check(As2, ss2, B2, t, k, Ms, Ab))
        self.assertEqual(seen, {True, False})

    def test_units_4_2(self):
        self.family_agreement(4, 2, "units", 16, 4, 11)

    def test_units_6_3(self):
        self.family_agreement(6, 3, "units", 6, 3, 12)

    def test_q_4_2(self):
        self.family_agreement(4, 2, "q", 16, 4, 13)

    def test_q_6_3(self):
        self.family_agreement(6, 3, "q", 6, 3, 14)

    def test_t2_4_2(self):
        self.family_agreement(4, 2, "t2", 16, 4, 15)

    def test_t2_6_3(self):
        self.family_agreement(6, 3, "t2", 6, 3, 16)

    def test_j2_4_2(self):
        self.family_agreement(4, 2, "j2", 16, 2, 17)

    def test_j2_6_3(self):
        self.family_agreement(6, 3, "j2", 6, 2, 18)

    def test_all_families_agree(self):
        # The whole of add_d2 against satisfies_d2 on random points and one-bit changes.
        rng = random.Random(19)
        for t, k, cases in ((4, 2, 10), (6, 3, 4)):
            d = t + k - 1
            insts = s4.instances(t - k, k - 1)
            for idx, Ms, Ab, ty in (insts[0], insts[len(insts) // 2], insts[-1]):
                cnf, names = s4.encode_d2(t, k, Ms, Ab)
                base_cnf, _ = sc.encode_split(t, k, Ms)
                base = len(base_cnf.clauses)
                for n in range(cases):
                    As, ss, B = random_coords(rng, t, k)
                    # Some families forced (their makers may undo each other, so the outcome is
                    # not asserted, only the agreement of the CNF with the direct check).
                    for fam in rng.sample(s4.FAMILIES, rng.randrange(len(s4.FAMILIES) + 1)):
                        MAKERS[fam](rng, As, ss, B, t, k, Ms, Ab)
                    self.assertEqual(added_ok(cnf, base, names, As, ss, B, t, d),
                                     s4.satisfies_d2(As, ss, B, t, k, Ms, Ab))
                    for _ in range(3):
                        As2, ss2, B2 = perturb(rng, As, ss, B, t, d)
                        self.assertEqual(added_ok(cnf, base, names, As2, ss2, B2, t, d),
                                         s4.satisfies_d2(As2, ss2, B2, t, k, Ms, Ab))

    def test_fixed_bits_rejected(self):
        # Every bit fixed by (D2) or by the X_1 -> X_1 part of (W2) is rejected when flipped.
        t, k = 6, 3
        rng = random.Random(21)
        idx, Ms, Ab, ty = s4.instances(3, 2)[-1]
        As, ss, B = random_coords(rng, t, k)
        make_units(rng, As, ss, B, t, k, Ms, Ab)
        self.assertTrue(s4.sat_units(As, ss, B, t, k, Ms, Ab))
        for r in range(k, t):
            for c in range(k, t):
                As2 = list(As)
                As2[0] ^= 1 << (t * r + c)
                self.assertFalse(s4.sat_units(As2, ss, B, t, k, Ms, Ab))
        for j in (1, 2):
            i = s4.w_index(k, j)
            for r in range(k, t):
                for c in range(k):
                    As2 = list(As)
                    As2[i] ^= 1 << (t * r + c)
                    self.assertFalse(s4.sat_units(As2, ss, B, t, k, Ms, Ab))

    def test_block(self):
        t, k = 6, 3
        rng = random.Random(23)
        for _ in range(20):
            M = rng.getrandbits(t * t)
            b = s4.block(M, t, k)
            for l in range(3):
                for c in range(3):
                    self.assertEqual((b >> (3 * l + c)) & 1, (M >> (t * (k + l) + k + c)) & 1)

    def test_bad_arguments(self):
        with self.assertRaises(ValueError):
            s4.encode_d2(5, 2, (0,), 1)
        with self.assertRaises(ValueError):
            s4.encode_d2(4, 2, (0,), 0)
        with self.assertRaises(ValueError):
            s4.encode_d2(4, 2, (0,), sc.identity(2))


if __name__ == "__main__":
    unittest.main()
