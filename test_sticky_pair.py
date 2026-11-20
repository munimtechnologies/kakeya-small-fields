# test_sticky_pair.py -- checks of the pair operation search (note a196, job sticky-pair-v1).
# MV2 of Munim, Inc. Made with AI agents working in MV2's name. Licence: Apache-2.0.

import random
import unittest

import sticky_pair as sp
import sticky_s7 as s7


class TestPair(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.s3 = sp.Shape(3)
        cls.s4 = sp.Shape(4)

    def test_encode_decode(self):
        for s in (self.s3, self.s4):
            for c in range(s.N):
                self.assertEqual(s.encode(s.decode(c)), c)
            self.assertEqual(s.ADD[0], list(range(s.N)))

    def test_table_roundtrip(self):
        s = self.s3
        for P in (s7.tree_A, s7.tree_B, s7.tree_C, s7.classical):
            tbl = sp.table_of(P, s)
            Q = sp.fn_of(tbl, s)
            for d in s.dom:
                self.assertEqual(Q(d), P(d))

    def test_slice_codes_match_slices(self):
        s = self.s4
        tbl = sp.table_of(s7.tree_H, s)
        codes = sp.slice_codes(tbl, s)
        direct = s7.slices(s7.tree_H, 4)
        for t in range(3):
            self.assertEqual(codes[t], set(s.encode(p) for p in direct[t]))

    def test_a196_pair(self):
        s = self.s3
        A, B = sp.table_of(s7.tree_A, s), sp.table_of(s7.tree_B, s)
        val, v = sp.lam(A, B, s)
        self.assertEqual(val, 31)
        ver = sp.verify_pair(A, B, v, s)
        self.assertTrue(ver["sticky"])
        self.assertEqual(ver["N_slices"], [11, 20, 20])
        self.assertEqual(ver["triangle_slices"], [31, 31, 31])

    def test_classical_pair(self):
        s = self.s3
        C = sp.table_of(s7.classical, s)
        self.assertEqual(sp.lam(C, C, s)[0], 32)

    def test_height4_seed(self):
        s = self.s4
        H = sp.table_of(s7.tree_H, s)
        val, v = sp.lam(H, H, s)
        self.assertEqual(val, 62)
        ver = sp.verify_pair(H, H, v, s)
        self.assertTrue(ver["sticky"])
        self.assertEqual(ver["N_slices"], [22, 40, 40])
        self.assertEqual(ver["triangle_slices"], [62, 62, 62])

    def test_random_pairs_verify(self):
        rng = random.Random(7)
        s = self.s3
        for _ in range(5):
            A, B = sp.random_table(s, rng), sp.random_table(s, rng)
            val, v = sp.lam(A, B, s)
            ver = sp.verify_pair(A, B, v, s)
            self.assertTrue(ver["sticky"])
            self.assertEqual(ver["triangle_slices"], [val, val, val])

    def test_anneal_smoke(self):
        s = self.s3
        seeds = sp.seeds_for(3, s)
        best, restarts, finals = sp.anneal(s, seeds, random.Random(1), 2.0, steps=300)
        self.assertLessEqual(best[0], 31)
        self.assertGreaterEqual(restarts, 1)


if __name__ == "__main__":
    unittest.main()
