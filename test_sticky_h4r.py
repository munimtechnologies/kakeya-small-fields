# Tests for sticky_h4r.py.  MV2 of Munim, Inc.; made with AI agents working in MV2's name.
# Licence: Apache-2.0.
import itertools
import random
import unittest

import sticky_h3 as h3
import sticky_h4r as h4r

# the 19 minimal real height-2 vectors (a189; sticky-h3-v1 output), = the game front at height 2
M2_KNOWN = sorted([(1, 9, 9), (2, 6, 6), (3, 3, 9), (3, 4, 8), (3, 5, 5), (3, 8, 4), (3, 9, 3),
                   (4, 3, 8), (4, 4, 4), (4, 8, 3), (5, 3, 5), (5, 5, 3), (6, 2, 6), (6, 6, 2),
                   (8, 3, 4), (8, 4, 3), (9, 1, 9), (9, 3, 3), (9, 9, 1)])


def brute_next(F):
    R = set()
    for kids in itertools.product(F, repeat=3):
        for root in h3.ALL_MAPS:
            R.add(h3.node_lower(root, kids))
    return h3.minimal3(R)


class TestFronts(unittest.TestCase):
    def test_front_from_best2(self):
        rng = random.Random(1)
        for _ in range(200):
            vecs = [tuple(rng.randint(1, 12) for _ in range(3)) for _ in range(rng.randint(1, 40))]
            best2 = {}
            for v in vecs:
                k = (v[0], v[1])
                if v[2] < best2.get(k, h3.INF):
                    best2[k] = v[2]
            self.assertEqual(h4r.front_from_best2(best2), h3.minimal3(vecs))

    def test_leaf(self):
        self.assertEqual(h4r.next_front([(1, 1, 1)]), [(1, 3, 3), (2, 2, 2), (3, 1, 3), (3, 3, 1)])

    def test_height2_is_known_front(self):
        F1 = h4r.next_front([(1, 1, 1)])
        self.assertEqual(h4r.next_front(F1), M2_KNOWN)

    def test_matches_node_by_node(self):
        rng = random.Random(7)
        for _ in range(25):
            F = list(set(tuple(rng.randint(1, 9) for _ in range(3)) for _ in range(rng.randint(1, 5))))
            self.assertEqual(h4r.next_front(F), brute_next(F))

    def test_witness(self):
        rng = random.Random(3)
        F = list(set(tuple(rng.randint(1, 9) for _ in range(3)) for _ in range(6)))
        wit = {}
        front = h4r.next_front(F, wit)
        roots = {"quadratic": None, "affine-slice-0": 0, "affine-slice-1": 1, "affine-slice-2": 2}
        for v in front:
            kind, A, B, C = wit[(v[0], v[1])]
            s = roots[kind]
            if s is None:
                got = (A[0] + max(B[0], C[0]), B[1] + max(A[1], C[1]), C[2] + max(A[2], B[2]))
            else:
                got = tuple(max(A[t], B[t], C[t]) if t == s else A[t] + B[t] + C[t]
                            for t in range(3))
            self.assertEqual(got, v)

    def test_game_height3(self):
        F3 = h4r.next_front(M2_KNOWN)
        self.assertEqual(len(F3), 112)
        self.assertEqual(min(a * b * c for a, b, c in F3), 512)


if __name__ == "__main__":
    unittest.main()
