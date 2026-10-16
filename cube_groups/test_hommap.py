import unittest

import hommap


class TestHommap(unittest.TestCase):
    def test_rank(self):
        self.assertEqual(hommap.rank_f2([0b11, 0b01, 0b10]), 2)
        self.assertEqual(hommap.rank_f2([0]), 0)

    def test_apply(self):
        # M = [[1,0],[1,1]] (rows as bitmasks of columns), w = e_0
        self.assertEqual(hommap.apply((0b01, 0b11), 0b01, 2, 2), 0b11)
        self.assertEqual(hommap.apply((0b01, 0b11), 0b10, 2, 2), 0b10)

    def test_b1_control(self):
        # b = 1: symmetric zero-diagonal matrices, a(a-1)/2 dimensions (lemma fails)
        for a in range(1, 5):
            self.assertEqual(hommap.nullity_linear(a, 1), a * (a - 1) // 2)

    def test_b_ge_2(self):
        for a in range(1, 5):
            for b in range(2, 4):
                self.assertEqual(hommap.nullity_linear(a, b), 0)

    def test_brute_small(self):
        self.assertEqual(hommap.count_brute(2, 1), 2)
        self.assertEqual(hommap.count_brute(3, 1), 8)
        self.assertEqual(hommap.count_brute(2, 2), 1)
        self.assertEqual(hommap.count_brute(1, 2), 1)

    def test_bounds(self):
        # Theorem 39 alone leaves (3,2) at s = 0 open (13 > 12); Theorem 40 closes it.
        self.assertEqual(3 + 4 + 6 - 0, 13)
        self.assertEqual(hommap.theorem40_bound(3, 2, 0), 12)
        self.assertTrue(hommap.settled(3, 2))
        self.assertTrue(hommap.settled(5, 1))
        self.assertTrue(hommap.settled(2, 4))
        self.assertFalse(hommap.settled(4, 2))
        self.assertFalse(hommap.settled(3, 3))


if __name__ == "__main__":
    unittest.main()
