# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import case_b as cb
import case_b_shapes as cs
import sat_aniso as sa
import shape_c as sc
import shape_c2 as s2


class TestCounts(unittest.TestCase):
    def test_selfcheck_grades(self):
        # By hand (notes/shape-c.md, Lemma 41): orbits of C(M) on the non-zero vectors, summed
        # over the classes of M_m(F_2), are 2, 10, 38 for m = 1, 2, 3; type ii counts twice, so
        # 3, 13, 47 instances. Centraliser orders are 168 / class size.
        st = s2.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])

    def test_types_are_invariant(self):
        for m in (2, 3):
            for (M,), _, _ in sc.orbits(m, 1):
                cent = s2.centraliser(M, m)
                for q in range(1, 1 << m):
                    typ = s2.lemma40_type(M, q, m)
                    for g in cent:
                        self.assertEqual(s2.lemma40_type(M, sa.mat_apply(g, q, m), m), typ)

    def test_representatives_are_least(self):
        for (M,), _, _ in sc.orbits(3, 1):
            cent = s2.centraliser(M, 3)
            for q, size in s2.q_orbits(M, 3):
                orb = {sa.mat_apply(g, q, 3) for g in cent}
                self.assertEqual(min(orb), q)
                self.assertEqual(len(orb), size)

    def test_type_iii_needs_two_dimensions(self):
        self.assertEqual([typ for _, _, typ, _ in s2.instances(3)], ["i", "ii", "ii"])


def synthetic(t, M, q, typ, c, rng):
    """Coordinates in the normal form of shape c with M_v = M and every value that encode_q fixes
    (other values 0; not a system)."""
    m = t - 2
    d = t + 1
    while True:
        cols = [rng.randrange(1 << t) for _ in range(m)]
        if sa.rank_f2(cols) < m or sa.combine(cols, q) != s2.T_Q[typ]:
            continue
        if typ == "iii" and sa.combine(cols, sa.mat_apply(M, q, m)) != s2.T_MQ_III:
            continue
        break
    As = [0] * d
    As[0] = sa.from_cols([0, 0] + cols, t)
    As[1] = sa.from_cols([0, 0] + [sa.combine(cols, sa.mat_apply(M, 1 << j, m))
                                   for j in range(m)], t)
    As[2] = sa.from_cols([2, s2.BETA_VW[typ]] + [0] * m, t)
    ss = [0] * d
    ss[0], ss[1], ss[2] = 1, 2, c | (q << 2)
    B = {key: 0 for key in itertools.combinations(range(d), 2)}
    for i in range(1, d):
        B[(0, i)] = cb.wanted_phi(i, 2)
    B[(1, 2)] = s2.BETA_VW[typ]
    return As, ss, B


class TestEncoding(unittest.TestCase):
    def picks(self, rng):
        out = [(3,) + x for x in s2.instances(3)]
        out += [(4,) + x for x in rng.sample(list(s2.instances(4)), 4)]
        for typ in s2.TYPES:
            out += [(5,) + x for x in rng.sample([x for x in s2.instances(5) if x[2] == typ], 2)]
        return out

    def test_clauses_added(self):
        rng = random.Random(5)
        for t, M, q, typ, c in self.picks(rng):
            base, _ = sc.encode_split(t, 2, (M,))
            cnf, _ = s2.encode_q(t, M, q, typ, c)
            self.assertEqual(cnf.nv, base.nv)
            self.assertEqual(cnf.clauses[:len(base.clauses)], base.clauses)
            self.assertEqual(len(cnf.clauses) - len(base.clauses),
                             s2.added_clause_count(t, M, q, typ))

    def test_synthetic_accepted_and_flips_rejected(self):
        rng = random.Random(11)
        for t in (3, 4, 5):
            insts = list(s2.instances(t))
            chosen = insts if t == 3 else ([x for x in insts if x[2] == "iii"][:2]
                                           + [x for x in insts if x[2] == "ii"][:2]
                                           + [x for x in insts if x[2] == "i"][:1])
            for M, q, typ, c in chosen:
                d = t + 1
                As, ss, B = synthetic(t, M, q, typ, c, rng)
                self.assertTrue(cs.in_shape(As, ss, B, t, 2, "c"))
                self.assertTrue(sc.satisfies_split(As, t, 2, (M,)))
                self.assertTrue(s2.satisfies_q(As, ss, B, t, M, q, typ, c))
                self.assertEqual(sc.m_of(As, 2, t, 2), M)
                cnf, names = s2.encode_q(t, M, q, typ, c)
                nbase = len(sc.encode_split(t, 2, (M,))[0].clauses)
                added = cnf.clauses[nbase:]

                def ok(As2, ss2, B2):
                    val = sa.assignment(cnf, names, As2, ss2, B2, t, d)
                    return all(any(val[x] if x > 0 else not val[-x] for x in cl) for cl in added)

                self.assertTrue(ok(As, ss, B))
                flips = []
                for r in range(t):
                    ss2 = list(ss)
                    ss2[2] ^= 1 << r
                    flips.append((As, ss2, B))
                    B2 = dict(B)
                    B2[(1, 2)] ^= 1 << r
                    flips.append((As, ss, B2))
                    for col in (0, 1):
                        As2 = list(As)
                        As2[2] ^= 1 << (t * r + col)
                        flips.append((As2, ss, B))
                    l = next(l for l in range(t - 2) if (q >> l) & 1)
                    As2 = list(As)
                    As2[0] ^= 1 << (t * r + 2 + l)
                    flips.append((As2, ss, B))
                for As2, ss2, B2 in flips:
                    self.assertFalse(s2.satisfies_q(As2, ss2, B2, t, M, q, typ, c))
                    self.assertFalse(ok(As2, ss2, B2))


if __name__ == "__main__":
    unittest.main()
