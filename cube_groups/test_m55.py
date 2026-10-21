# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m55.py (job m55). The full counts are the job's own run step."""
import random
import unittest

import m55 as m


class TestM55(unittest.TestCase):
    def test_classes(self):
        self.assertEqual(len(m.CLASSES), 10)
        for name, (mask, x1, rb) in m.CLASSES.items():
            au = m.cols_of(mask)
            st = m.structure(au, x1, rb)
            self.assertEqual(st["rank_au"], 3, name)
            self.assertTrue(st["ker_is_x1"] and st["im_is_r"] and st["d3"], name)
            self.assertEqual(st["x1_in_h0"], x1 == m.ALPHA, name)
            self.assertEqual(m.compose(au, au), (0,) * m.T, name)

    def test_kinds(self):
        # x0 in R exactly for pair orbits 0, 20 and 31; R inside P exactly for pair orbit 1.
        for name, (mask, x1, rb) in m.CLASSES.items():
            st = m.structure(m.cols_of(mask), x1, rb)
            self.assertEqual(st["x0_in_r"], name[11:14] in ("000", "020", "031"), name)
            self.assertEqual(st["r_in_p"], name[11:14] == "001", name)

    def test_hand_valid(self):
        self.assertEqual(m.HAND_VALID[m.ALPHA], 405566)
        self.assertEqual(m.HAND_VALID[m.BETA], 323966)

    def test_index_roundtrip(self):
        rng = random.Random(1)
        for x1, rb in ((m.ALPHA, (4, 2, 1)), (m.BETA, (64, 4, 3))):
            mp = m.Maps(x1, rb)
            for _ in range(200):
                i = rng.randrange(1 << m.NBITS)
                self.assertEqual(mp.index(mp.cols(i)), i)
                j = rng.randrange(1 << m.NBITS)
                a, b = mp.cols(i), mp.cols(j)
                self.assertEqual(mp.index(tuple(x ^ y for x, y in zip(a, b))), i ^ j)

    def test_au_index(self):
        for name, (mask, x1, rb) in m.CLASSES.items():
            mp = m.Maps(x1, rb)
            self.assertEqual(mp.cols(mp.index(m.cols_of(mask))), m.cols_of(mask), name)

    def test_base_block(self):
        rng = random.Random(2)
        for x1, rb in ((m.ALPHA, (8, 4, 3)), (m.BETA, (64, 2, 1))):
            mp = m.Maps(x1, rb)
            for _ in range(20):
                h = rng.randrange(1 << 15)
                blk = mp.base_block(h)
                for v in range(128):
                    self.assertEqual(blk[v], int(mp.base_slow(h | v << 15)))

    def test_small_group(self):
        name = "r3b_t7_B5_o031_c000"
        mask, x1, rb = m.CLASSES[name]
        au = m.cols_of(mask)
        grp, dim = m.group(au)
        # The order is graded by the job against Proposition 32, not asserted here.
        self.assertTrue(m.check_group(au, grp))
        self.assertGreater(len(grp), 1)
        mp = m.Maps(x1, rb)
        rng = random.Random(3)
        g = rng.choice(grp)
        gi = m.inverse(g)
        self.assertEqual(m.compose(g, gi), m.IDENT)
        tabs = m.index_map(mp, g, gi)
        for _ in range(100):
            i = rng.randrange(1 << m.NBITS)
            self.assertEqual(m.map_apply(tabs, i), m.conj_index(mp, g, gi, i))


if __name__ == "__main__":
    unittest.main()
