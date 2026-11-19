# Tests for sticky_beam.py (note a188, pre-registered job sticky-beam-v1).
# MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0. Stdlib only.
import itertools
import random
import unittest

import sticky_beam as sbm


def to_set(bits, k):
    pts = set()
    for i, y in enumerate(itertools.product(range(3), repeat=k)):
        if (bits >> i) & 1:
            pts.add(y)
    return pts


def to_bits(pts, k):
    b = 0
    for i, y in enumerate(itertools.product(range(3), repeat=k)):
        if y in pts:
            b |= 1 << i
    return b


def slices_as_sets(maps, k):
    S = [set(), set(), set()]
    for d in itertools.product(range(3), repeat=k):
        p = tuple(maps[d[:j]][d[j]] for j in range(k))
        for t in range(3):
            S[t].add(tuple((p[j] + t * d[j]) % 3 for j in range(k)))
    return S


def random_maps(k, rng):
    return {a: tuple(rng.randrange(3) for _ in range(3))
            for j in range(k) for a in itertools.product(range(3), repeat=j)}


class TestBitsets(unittest.TestCase):
    def test_index_order(self):
        # bit index of y is sum_j y_j 3^(k-1-j): itertools.product enumerates in that order
        for i, y in enumerate(itertools.product(range(3), repeat=3)):
            self.assertEqual(i, y[0] * 9 + y[1] * 3 + y[2])

    def test_translate(self):
        rng = random.Random(5)
        for k in (1, 2, 3, 4):
            for _ in range(10):
                pts = {y for y in itertools.product(range(3), repeat=k) if rng.random() < 0.4}
                w = tuple(rng.randrange(3) for _ in range(k))
                moved = {tuple((y[j] + w[j]) % 3 for j in range(k)) for y in pts}
                self.assertEqual(to_set(sbm.translate_bits(to_bits(pts, k), w, k), k), moved)

    def test_slices_from_maps(self):
        rng = random.Random(6)
        for k in (0, 1, 2, 3):
            for _ in range(5):
                m = random_maps(k, rng)
                S = sbm.slices_from_maps(m, k)
                ref = slices_as_sets(m, k)
                for t in range(3):
                    self.assertEqual(to_set(S[t], k), ref[t])

    def test_combine_matches_maps(self):
        rng = random.Random(7)
        for k in (0, 1, 2):
            for _ in range(10):
                kids = [random_maps(k, rng) for _ in range(3)]
                root = tuple(rng.randrange(3) for _ in range(3))
                S = sbm.combine(root, [sbm.slices_from_maps(m, k) for m in kids], k)
                self.assertEqual(S, sbm.slices_from_maps(sbm.node_maps(root, kids), k + 1))

    def test_perm_and_translate_maps(self):
        rng = random.Random(8)
        for k in (1, 2, 3):
            for _ in range(6):
                m = random_maps(k, rng)
                S = sbm.slices_from_maps(m, k)
                for eps in (1, 2):
                    for c in range(3):
                        pm = sbm.perm_maps(m, eps, c)
                        self.assertTrue(sbm.is_full(pm, k))
                        self.assertEqual(sbm.slices_from_maps(pm, k), sbm.perm_slices(S, eps, c))
                w = tuple(rng.randrange(3) for _ in range(k))
                tm = sbm.translate_maps(m, w)
                self.assertEqual(sbm.slices_from_maps(tm, k),
                                 tuple(sbm.translate_bits(s, w, k) for s in S))


class TestBeam(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cfg = sbm.default_config()
        cfg.update({"kmax": 4, "cands": 1500, "local_top": 3, "local_tries": 20, "passes": 1,
                    "cap": 400, "trans_bases": 6})
        cls.cfg = cfg
        cls.res = sbm.run(cfg, 1)

    def test_sanity_values(self):
        H = self.res["heights"]
        self.assertEqual(H[1]["best_product"], 8)       # Proposition 83
        self.assertEqual(H[2]["best_product"], 64)      # Proposition 83
        for h in range(1, 5):
            self.assertLessEqual(H[h]["best_product"], 8 ** h)   # doubling keeps the classical ratio

    def test_height1_is_exhaustive(self):
        sizes = sorted(tuple(sorted(b["sizes"])) for b in self.res["bases"][1])
        self.assertIn((2, 2, 2), sizes)
        self.assertIn((1, 3, 3), sizes)

    def test_every_base_rebuilds_from_its_recipe(self):
        bases = self.res["bases"]
        for h in range(1, 5):
            memo = {}
            for i, b in enumerate(bases[h]):
                maps = sbm.maps_of_base(h, i, bases, memo)
                self.assertTrue(sbm.is_full(maps, h))
                self.assertEqual(sbm.slices_from_maps(maps, h), tuple(b["S"]))
                self.assertEqual(tuple(sbm.popcount(s) for s in b["S"]), tuple(b["sizes"]))

    def test_hits_are_verified_or_absent(self):
        for x in self.res["hits"]:
            self.assertEqual(x["claimed_sizes"], x["recomputed_sizes"])

    def test_verify_detects_a_corrupted_tree(self):
        bases = self.res["bases"]
        b = bases[3][0]
        root, kids = b["recipe"][1], b["recipe"][2]
        maps, full, S = sbm.verify(root, kids, bases, 3)
        self.assertTrue(full)
        self.assertEqual(S, tuple(b["S"]))
        bad = dict(maps)
        del bad[(0, 0)]
        self.assertFalse(sbm.is_full(bad, 3))


if __name__ == "__main__":
    unittest.main()
