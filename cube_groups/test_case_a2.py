# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import case_a as ca
import case_a2 as cb
import sat_aniso as sa


def bare(t):
    """A CNF with only the variables of sat_aniso.encode (d = t + 1) and no clauses."""
    return sa.encode(t, t + 1, star=False, aniso=False, echelon=False)


def random_coords(t, rng):
    d = t + 1
    As = [rng.getrandbits(t * t) for _ in range(d)]
    ss = [rng.randrange(1 << t) for _ in range(d)]
    B = {key: rng.randrange(1 << t) for key in itertools.combinations(range(d), 2)}
    return As, ss, B


def added_ok(cnf, names, k0, As, ss, B, t):
    val = sa.assignment(cnf, names, As, ss, B, t, t + 1)
    return all(any(val[x] if x > 0 else not val[-x] for x in cl) for cl in cnf.clauses[k0:])


class TestPlanes(unittest.TestCase):
    def test_hand_counts(self):
        # notes/case-a-radical.md: 3 planes per orbit with e_0 outside R (d = 1), 2 with e_0 in R
        # (d = 2) at t = 5; 1 and 0 at t = 4; none at t = 3.
        for t, n in cb.HAND_PLANES.items():
            self.assertEqual(len(cb.instances(t)), n)
        for A, _ in ca.orbits(5):
            d = ca.invariants(A, 5)[0]
            self.assertEqual(len(cb.planes(A, 5)), {1: 3, 2: 2}[d])
            R = cb.image(A, 5)
            self.assertEqual(len(R), 8)
            for r2 in cb.planes(A, 5):
                P = cb.span([cb.E1, r2])
                self.assertEqual(len(P), 4)
                self.assertTrue(P <= R)
                self.assertNotIn(cb.E0, P)
                self.assertNotIn(cb.E0 ^ cb.E1, P)
                self.assertEqual(r2, min(P - {0, cb.E1}))

    def test_lift(self):
        self.assertEqual(cb.lift(0b00001, 5), 0b000010)
        self.assertEqual(cb.lift(0b10010, 5), 0b100100)
        # phi(s(p)) = p in the normal form: phi(v_i) = e_(i-1)
        for p in range(32):
            h = cb.lift(p, 5)
            self.assertEqual(h & 1, 0)
            self.assertEqual(sum(1 << (i - 1) for i in range(1, 6) if (h >> i) & 1), p)

    def test_selfcheck_grades(self):
        st = cb.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])


class TestConstraints(unittest.TestCase):
    """Each added constraint, alone on a bare CNF, accepts exactly the coordinates that satisfy it."""

    def check(self, t, add, holds, samples=300, seed=1):
        rng = random.Random(seed)
        cnf, names = bare(t)
        k0 = len(cnf.clauses)
        add(cnf, names)
        self.assertGreater(len(cnf.clauses), k0)
        seen = set()
        for _ in range(samples):
            As, ss, B = random_coords(t, rng)
            want = holds(As, ss, B)
            self.assertEqual(added_ok(cnf, names, k0, As, ss, B, t), want)
            seen.add(want)
        self.assertEqual(seen, {True, False})

    def test_columns(self):
        t = 5
        for Au, _ in ca.orbits(t)[:4]:
            R = cb.image(Au, t)
            Rb = sa.independent([sa.mat_apply(Au, 1 << c, t) for c in range(t)])
            r2 = cb.planes(Au, t)[0]
            for j, r in ((1, cb.E1), (3, r2)):
                self.check(t, lambda cnf, names: cb.add_columns(cnf, names, t, Rb, j, r),
                           lambda As, ss, B: sa.mat_apply(As[j], r, t) in R, samples=120)

    def test_coset(self):
        t = 5
        for Au, _ in ca.orbits(t)[:3]:
            r2 = cb.planes(Au, t)[-1]
            P = cb.span([cb.E1, r2])
            for r in (cb.E1, r2, r2 ^ cb.E1):
                h = (1 << 1) ^ cb.lift(r, t)

                def holds(As, ss, B, h=h, r=r):
                    y = sa.tables(As, ss, B, t + 1)[1][h]
                    return y in P and y not in (0, r)

                self.check(t, lambda cnf, names, r=r: cb.add_coset(cnf, names, t, r2, r), holds,
                           samples=400, seed=r)

    def test_closed(self):
        t = 5
        for Au, _ in ca.orbits(t)[:3]:
            for r2 in cb.planes(Au, t)[:2]:
                P = cb.span([cb.E1, r2])
                a, b = cb.lift(cb.E1, t), cb.lift(r2, t)

                def holds(As, ss, B, a=a, b=b, P=P):
                    sv = sa.tables(As, ss, B, t + 1)[1]
                    return sv[a ^ b] ^ sv[a] ^ sv[b] in P

                self.check(t, lambda cnf, names, r2=r2: cb.add_closed(cnf, names, t, r2), holds,
                           samples=300, seed=r2)

    def test_full_encoding_extends_case_a(self):
        rng = random.Random(3)
        for t in (4, 5):
            for idx, Au, r2 in cb.instances(t)[:3]:
                base, _ = ca.encode_case_a(t, Au)
                cnf, names = cb.encode_case_a2(t, Au, r2)
                self.assertEqual(cnf.clauses[:len(base.clauses)], base.clauses)
                self.assertGreater(cnf.nv, base.nv)
                # the added clauses agree with conditions() on random coordinates
                k0 = len(base.clauses)
                for _ in range(20):
                    As, ss, B = random_coords(t, rng)
                    want = all(cb.conditions(As, ss, B, t, Au, r2).values())
                    self.assertEqual(added_ok(cnf, names, k0, As, ss, B, t), want)


if __name__ == "__main__":
    unittest.main()
