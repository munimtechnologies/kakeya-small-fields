# SPDX-License-Identifier: Apache-2.0
"""Tests for oval_rigidity.py (note a162). Standard library only.

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Every assertion here is a fact proved by hand in a162 (or a classical theorem: Segre's
theorem for q = 3, 5, 7), so a failure means a bug in the code, not a false theorem.
"""

import random
import unittest

import oval_rigidity as orr


class TestProposition42(unittest.TestCase):
    """1D maximisers are exactly the graphs that are arcs (ovals with the vertical point);
    for odd q they are exactly the nondegenerate quadratics (Segre)."""

    def test_max_iff_arc(self):
        for q in (2, 3, 5, 7):
            maxset, arcset = set(), set()
            for f in orr.maps_1d_fixed0(q):
                P = orr.lift1(f)
                self.assertFalse(orr.exceeds(P, q, 1))  # C_q(1)
                if orr.is_max(P, q, 1):
                    maxset.add(f)
                if orr.is_arc_graph(f, q):
                    arcset.add(f)
            self.assertEqual(maxset, arcset, q)
            if q % 2 == 1:
                quad = orr.quadratics_fixed0(q)
                self.assertEqual(len(quad), q * (q - 1))
                self.assertEqual(maxset, quad, q)
            print("Prop 42: q =", q, "maximisers with f(0) = 0:", len(maxset))


class TestLemma112(unittest.TestCase):
    """Pointwise form: sum_t (z_t(x) - 1) = N(x) and sum_x phi(x) = q^k Lambda."""

    def test_random_maps(self):
        rng = random.Random(162)
        for q, k, reps in ((3, 2, 6), (5, 2, 2), (2, 3, 3), (5, 1, 20), (7, 1, 20)):
            pts = orr.points(q, k)
            for r in range(reps):
                if r % 2 == 0:
                    P = [tuple(rng.randrange(q) for _ in range(k)) for _ in pts]
                else:  # large fibres
                    P = [tuple(rng.randrange(2) for _ in range(k)) for _ in pts]
                rows = orr.pointwise(P, q, k)
                total = 0.0
                for phi, excess, n in rows:
                    self.assertEqual(excess, n)
                    total += phi
                    if k == 1:
                        # pointwise proof of C_q(1): log2 z <= z - 1 and N(x) <= q - 1
                        self.assertLessEqual(n, q - 1)
                        self.assertLessEqual(phi, q - 1 + 1e-9)
                self.assertAlmostEqual(total, q ** k * orr.loss(P, q, k), places=7)


class TestProposition43(unittest.TestCase):
    """q = 3: the 216 frame products are distinct maximisers with a zero-slack frame."""

    def test_q3(self):
        q = 3
        quad = orr.quadratics_fixed0(q)
        nonaffine = {
            f for f in orr.maps_1d_fixed0(q)
            if f not in {tuple((c * y) % q for y in range(q)) for c in range(q)}
        }
        self.assertEqual(quad, nonaffine)
        fp = orr.frame_products(q, sorted(quad))
        self.assertEqual(len(fp), 216)
        self.assertEqual(orr.frame_product_count(q), 216)
        for P, (e1, e2, f, g) in fp.items():
            self.assertEqual(P[0], (0, 0))
            self.assertTrue(orr.is_max(list(P), q, 2))
            self.assertTrue(orr.zero_slack(list(P), q, e1, e2))
        # control: a triangular map that is not a frame product loses strictly less
        pts = orr.points(q, 2)
        T = [((x[0] * x[0] + x[1]) % q, (x[1] * x[1]) % q) for x in pts]
        self.assertNotIn(tuple(T), fp)
        self.assertFalse(orr.is_max(T, q, 2))
        self.assertFalse(orr.exceeds(T, q, 2))
        print("Prop 43: q = 3 frame products", len(fp), "all maximal, all zero-slack")


class TestFrameProductsLargerQ(unittest.TestCase):
    def test_q5(self):
        q = 5
        fp = orr.frame_products(q, sorted(orr.quadratics_fixed0(q)))
        self.assertEqual(len(fp), orr.frame_product_count(q))
        self.assertEqual(len(fp), 6000)
        for P, (e1, e2, f, g) in fp.items():
            self.assertTrue(orr.is_max(list(P), q, 2))
        for P, (e1, e2, f, g) in list(fp.items())[::40]:
            self.assertTrue(orr.zero_slack(list(P), q, e1, e2))
        print("q = 5 frame products", len(fp), "all maximal")

    def test_q7_count(self):
        q = 7
        fp = orr.frame_products(q, sorted(orr.quadratics_fixed0(q)))
        self.assertEqual(len(fp), orr.frame_product_count(q))
        self.assertEqual(len(fp), 49392)
        for P in list(fp)[::997]:
            self.assertTrue(orr.is_max(list(P), q, 2))
        print("q = 7 frame products", len(fp))

    def test_normalised_counts(self):
        # under P -> P + cI the frame products split into orbits of size q; the census of
        # job kakeya-quad-v1 keeps the member whose first coordinate has no x1 term
        for q, expect in ((3, 72), (5, 1200)):
            fp = orr.frame_products(q, sorted(orr.quadratics_fixed0(q)))
            pts = orr.points(q, 2)
            i10 = pts.index((1, 0))
            i20 = pts.index((2, 0))
            # P1(x1, 0) = a x1^2 + d x1, so d = (4 P1(1,0) - P1(2,0)) / 2
            inv2 = pow(2, q - 2, q)
            n = sum(1 for P in fp if ((4 * P[i10][0] - P[i20][0]) * inv2) % q == 0)
            self.assertEqual(n, expect)
            self.assertEqual(n * q, len(fp))


if __name__ == "__main__":
    unittest.main(verbosity=2)
