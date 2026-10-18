# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import ablate_c as ab
import sat_aniso as sa
import shape_c as sc
import shape_c3 as s3
import shape_c4 as s4


def random_coords(rng, t, k):
    d = t + k - 1
    As = [rng.getrandbits(t * t) for _ in range(d)]
    ss = [rng.getrandbits(t) for _ in range(d)]
    B = {(i, j): rng.getrandbits(t) for i, j in itertools.combinations(range(d), 2)}
    return As, ss, B


def set_block(M, t, k, Ab):
    m = t - k
    for l in range(m):
        for c in range(m):
            bit = 1 << (t * (k + l) + k + c)
            M = M | bit if (Ab >> (m * l + c)) & 1 else M & ~bit
    return M


def added_ok(cnf, base, names, As, ss, B, t, d):
    val = sa.assignment(cnf, names, As, ss, B, t, d)
    return all(any(val[lit] if lit > 0 else not val[-lit] for lit in cl)
               for cl in cnf.clauses[base:])


class TestInstances(unittest.TestCase):
    def test_selfcheck_grades(self):
        st = ab.selfcheck()
        self.assertTrue(all(st["graded"].values()), st)

    def test_cover(self):
        # Every orbit of tuples appears once with Abar = 0, and with exactly the rank-1 matrices of
        # job m19's triples; every Abar has rank <= 1.
        for m, r in ((2, 1), (3, 2)):
            inst = ab.instances(m, r)
            zero = [x[0] for x in inst if x[2] == 0]
            self.assertEqual(zero, list(range(len(sc.orbits(m, r)))))
            self.assertEqual([x for x in inst if x[2]], list(s4.triples(m, r)))
            for idx, Ms, Ab in inst:
                self.assertLessEqual(sa.rank_f2(sa.rows_of(Ab, m)), 1)
                self.assertEqual(Ms, sc.orbits(m, r)[idx][0])

    def test_names_unique(self):
        for t, k in ((4, 2), (6, 3)):
            names = [ab.instance_name(t, k, x[0], x[2]) for x in ab.instances(t - k, k - 1)]
            self.assertEqual(len(names), len(set(names)))


class TestEncoding(unittest.TestCase):
    def test_zero_block_is_d_of_m18(self):
        # For Abar = 0, (Z) is exactly the first family (D) that shape_c3.add_d3 appends.
        for t, k in ((4, 2), (6, 3)):
            m = t - k
            Ms = sc.orbits(m, k - 1)[0][0]
            cnf, names = sc.encode_split(t, k, Ms)
            base = len(cnf.clauses)
            ab.add_block(cnf, names, t, k, 0)
            mine = cnf.clauses[base:]
            cnf3, names3 = sc.encode_split(t, k, Ms)
            s3.add_d3(cnf3, names3, t, k, Ms)
            self.assertEqual(mine, cnf3.clauses[base:base + m * m])

    def test_rank1_block_is_d2_of_m19(self):
        # For rank 1, (Z) is exactly the first family (D2) that shape_c4.add_units appends.
        rng = random.Random(5)
        for t, k in ((4, 2), (6, 3)):
            m = t - k
            trip = s4.triples(m, k - 1)
            for idx, Ms, Ab in [trip[0], trip[-1]] + rng.sample(trip, 3):
                cnf, names = sc.encode_split(t, k, Ms)
                base = len(cnf.clauses)
                ab.add_block(cnf, names, t, k, Ab)
                mine = cnf.clauses[base:]
                cnf4, names4 = sc.encode_split(t, k, Ms)
                s4.add_units(cnf4, names4, t, k, Ms, Ab)
                self.assertEqual(mine, cnf4.clauses[base:base + m * m])

    def test_agreement(self):
        # The appended clauses accept exactly the coordinates whose block is Ab.
        rng = random.Random(7)
        for t, k, cases in ((4, 2, 12), (6, 3, 6)):
            d = t + k - 1
            inst = ab.instances(t - k, k - 1)
            for idx, Ms, Ab in [inst[0], inst[-1]] + rng.sample(inst, 3):
                cnf, names = ab.encode_z(t, k, Ms, Ab)
                base_cnf, _ = sc.encode_split(t, k, Ms)
                base = len(base_cnf.clauses)
                seen = set()
                for n in range(cases):
                    As, ss, B = random_coords(rng, t, k)
                    if n % 2 == 0:
                        As[0] = set_block(As[0], t, k, Ab)
                    want = ab.satisfies_z(As, t, k, Ab)
                    seen.add(want)
                    self.assertEqual(added_ok(cnf, base, names, As, ss, B, t, d), want)
                    for r in range(k, t):
                        for c in range(k, t):
                            As2 = list(As)
                            As2[0] ^= 1 << (t * r + c)
                            self.assertEqual(added_ok(cnf, base, names, As2, ss, B, t, d),
                                             ab.satisfies_z(As2, t, k, Ab))
                self.assertEqual(seen, {True, False})

    def test_bad_arguments(self):
        with self.assertRaises(ValueError):
            ab.encode_z(5, 2, (0,), 0)
        with self.assertRaises(ValueError):
            ab.encode_z(4, 2, (0,), sc.identity(2))


if __name__ == "__main__":
    unittest.main()
