# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m93.py: the arithmetic against naive versions, Feit and Fine's count at n <= 3,
the tables at n = 4, the dimension-1 sweep, and the flags of two subspaces worked out by hand."""
import random
import unittest

import m93


def entry(x, r, c):
    return (x >> (4 * r + c)) & 1


def naive_mul(x, y):
    out = 0
    for r in range(4):
        for c in range(4):
            if sum(entry(x, r, k) & entry(y, k, c) for k in range(4)) & 1:
                out |= 1 << (4 * r + c)
    return out


def e(r, c):
    return 1 << (4 * r + c)


class TestArithmetic(unittest.TestCase):
    def test_mul(self):
        rng = random.Random(93)
        for _ in range(300):
            x, y = rng.randrange(m93.FULL), rng.randrange(m93.FULL)
            self.assertEqual(m93.mul(x, y), naive_mul(x, y))
            self.assertEqual(m93.mul(m93.IDENT, x), x)
            self.assertEqual(m93.mul(x, m93.IDENT), x)

    def test_vectors(self):
        rng = random.Random(1)
        for _ in range(200):
            x, v = rng.randrange(m93.FULL), rng.randrange(16)
            col = sum(1 << r for r in range(4)
                      if sum(entry(x, r, c) & (v >> c & 1) for c in range(4)) & 1)
            row = sum(1 << c for c in range(4)
                      if sum((v >> r & 1) & entry(x, r, c) for r in range(4)) & 1)
            self.assertEqual(m93.mat_vec(x, v), col)
            self.assertEqual(m93.vec_mat(v, x), row)

    def test_rank_inverse(self):
        self.assertEqual(m93.rank(0), 0)
        self.assertEqual(m93.rank(m93.IDENT), 4)
        self.assertEqual(m93.rank(e(0, 3)), 1)
        self.assertIsNone(m93.inverse(e(0, 3)))
        rng = random.Random(2)
        for _ in range(300):
            x = rng.randrange(m93.FULL)
            self.assertEqual(len({m93.mat_vec(x, v) for v in range(16)}), 1 << m93.rank(x))
            xi = m93.inverse(x)
            if m93.rank(x) == 4:
                self.assertEqual(m93.mul(x, xi), m93.IDENT)
            else:
                self.assertIsNone(xi)

    def test_feit_fine(self):
        self.assertEqual(m93.feit_fine(1), 4)
        self.assertEqual(m93.feit_fine(2), 88)
        self.assertEqual(m93.feit_fine(3), 7456)

    def test_subspaces(self):
        subs = m93.subspaces()
        self.assertEqual(len(subs), 67)
        self.assertEqual([sum(1 for s in subs if len(s) == 1 << d) for d in range(5)],
                         [1, 15, 35, 15, 1])
        self.assertEqual(len(m93.SUBSPACE_BASES), 66)
        self.assertTrue(all(len(m93.span_of(b)) == len(set(m93.span_of(b))) for b in
                            m93.SUBSPACE_BASES))

    def test_spans(self):
        self.assertEqual(sorted(m93.span_of([1, 2])), [0, 1, 2, 3])
        self.assertEqual(m93.dim_span([1, 2, 3, 4]), 3)
        self.assertEqual(m93.key_of([2, 0, 1]), (1 << 16) | 2)


class TestTables(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.t = m93.Tables()

    def test_checks(self):
        ok, pairs = self.t.checks()
        self.assertTrue(all(ok.values()), ok)
        self.assertEqual(pairs, m93.feit_fine(4))

    def test_dim1(self):
        d1 = m93.run(self.t, 1)
        self.assertTrue(d1["complete"])
        self.assertEqual(len(d1["orbits"]), 32)
        self.assertEqual(d1["subspaces"], m93.FULL - 2)
        self.assertEqual(d1["orbit_size_sum"], m93.FULL - 2)

    def test_flags_first_row(self):
        """span(E_01, E_02, E_03): every product 0, seven matrices of rank 1."""
        b = [e(0, 1), e(0, 2), e(0, 3)]
        f = m93.flags(self.t, b)
        self.assertEqual(f["ranks"], [7, 0, 0, 0])
        self.assertTrue(f["singular"])
        self.assertEqual((f["common_kernel_dim"], f["image_dim"], f["hyperplanes"]), (1, 1, 7))
        self.assertTrue(f["algebra"] and f["square_zero"])
        self.assertEqual((f["nilpotent"], f["defect"]), (7, -3))
        self.assertTrue(f["n4"] and f["f3"])
        self.assertTrue(m93.reps_ok([{"basis": b, "size": 1}]))

    def test_flags_diagonal(self):
        """span(E_00, E_11, E_22): diagonal idempotents."""
        b = [e(0, 0), e(1, 1), e(2, 2)]
        f = m93.flags(self.t, b)
        self.assertEqual(f["ranks"], [3, 3, 1, 0])
        self.assertTrue(f["singular"])
        self.assertEqual((f["common_kernel_dim"], f["image_dim"], f["hyperplanes"]), (1, 3, 4))
        self.assertTrue(f["algebra"])
        self.assertFalse(f["square_zero"])
        self.assertEqual((f["nilpotent"], f["defect"]), (0, -1))

    def test_flags_invertible(self):
        """span(I + E_10, E_01, E_02) contains the invertible I + E_10 (and not I), so it is not
        singular and dim(W U) >= dim U for every U."""
        p = m93.IDENT ^ e(1, 0)
        b = [p, e(0, 1), e(0, 2)]
        self.assertEqual(m93.rank(p), 4)
        self.assertNotIn(m93.IDENT, m93.span_of(b))
        f = m93.flags(self.t, b)
        self.assertFalse(f["singular"])
        self.assertFalse(f["n4"] or f["f3"])
        self.assertEqual(f["defect"], 0)


if __name__ == "__main__":
    unittest.main()
