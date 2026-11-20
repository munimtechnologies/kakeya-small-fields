# test_sticky_s7.py -- brute-force checks of the explicit S7 witness of note a196.
# MV2 of Munim, Inc. Made with AI agents working in MV2's name. Licence: Apache-2.0.

import json
import os
import unittest

import sticky_s7 as s7


def find_witness():
    here = os.path.dirname(os.path.abspath(__file__))
    p = os.path.join(here, "results", "sticky-s7", "witness.json")
    if os.path.exists(p):
        return p
    p = os.path.join(os.path.dirname(here), "results", "sticky-s7", "witness.json")
    if os.path.exists(p):
        return p
    for root, _dirs, files in os.walk(here):
        if "witness.json" in files and os.path.basename(root) == "sticky-s7":
            return os.path.join(root, "witness.json")
    return None


class TestS7Witness(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.S = {name: s7.slices(P, k) for name, (P, k) in
                 {"A": (s7.tree_A, 3), "B": (s7.tree_B, 3), "C": (s7.tree_C, 3),
                  "H": (s7.tree_H, 4), "G": (s7.tree_G, 5)}.items()}

    def test_all_trees_are_sticky(self):
        for P, k in ((s7.tree_A, 3), (s7.tree_B, 3), (s7.tree_C, 3), (s7.tree_H, 4),
                     (s7.tree_G, 5), (s7.classical, 5)):
            self.assertTrue(s7.is_sticky(P, k))

    def test_sticky_check_rejects_non_sticky_map(self):
        self.assertFalse(s7.is_sticky(lambda d: (d[1], d[0]), 2))

    def test_child_slices(self):
        S = self.S
        self.assertEqual([len(s) for s in S["A"]], [4, 12, 12])
        self.assertEqual(S["A"][1], S["A"][2])
        self.assertEqual([len(s) for s in S["B"]], [7, 7, 13])
        self.assertEqual(S["C"][0], S["B"][0])
        self.assertEqual(S["C"][1], S["B"][2])
        self.assertEqual(S["C"][2], S["B"][1])
        self.assertTrue(S["A"][1] | S["A"][2] <= S["B"][2])

    def test_height4_tree(self):
        S = self.S["H"]
        self.assertEqual([len(s) for s in S], [11, 20, 20])
        self.assertEqual(S[1], S[2])
        k, arg = s7.kappa(s7.tree_H, 4)
        self.assertEqual(k, 31)
        self.assertEqual(arg[0], 0)

    def test_height5_tree_beats_eight_to_the_five(self):
        S = self.S["G"]
        sizes = [len(s) for s in S]
        self.assertEqual(sizes, [31, 31, 31])
        self.assertEqual(sizes[0] * sizes[1] * sizes[2], 29791)
        self.assertLess(29791, 8 ** 5)
        c = [len(s) for s in s7.slices(s7.classical, 5)]
        self.assertEqual(c, [32, 32, 32])

    def test_rho_shifts_slices(self):
        S = self.S["H"]
        for c in range(3):
            R = s7.slices(s7.rho(s7.tree_H, c), 4)
            for t in range(3):
                self.assertEqual(R[t], S[(t + c) % 3])

    def test_kakeya_sets(self):
        K2 = s7.classical_kakeya(2)
        self.assertEqual(len(K2), 7)
        self.assertTrue(s7.is_kakeya(K2, 2))
        K5 = s7.classical_kakeya(5)
        self.assertTrue(s7.is_kakeya(K5, 5))
        K6 = s7.kakeya_from(s7.tree_G, 5, K5)
        self.assertTrue(s7.is_kakeya(K6, 6))
        plane = set((0,) + p for p in s7.domain(5))
        self.assertFalse(s7.is_kakeya(plane, 6))

    def test_witness_file_matches_recomputation(self):
        path = find_witness()
        self.assertIsNotNone(path, "results/sticky-s7/witness.json must be in the commit")
        with open(path) as fh:
            W = json.load(fh)
        r = s7.run(None)
        for name in ("A", "B", "C", "H", "G"):
            self.assertEqual(W[name]["slice_sizes"], r[name]["slice_sizes"], name)
            self.assertTrue(r[name]["sticky"], name)
        for name in ("A", "B"):
            self.assertEqual(W[name]["slices"], r[name]["slices"], name)
        self.assertEqual(W["A"]["S1_equals_S2"], r["A"]["S1_equals_S2"])
        self.assertEqual(W["H"]["S1_equals_S2"], r["H"]["S1_equals_S2"])
        self.assertEqual(W["G"]["S1_equals_S2"], r["G"]["S1_equals_S2"])
        self.assertEqual(W["C"]["slices_are_B_0_B_2_B_1"], r["C"]["slices_are_B_0_B_2_B_1"])
        self.assertEqual(W["A1_union_A2_subset_B2"], r["A1_union_A2_subset_B2"])
        self.assertEqual(W["H"]["kappa"], r["H"]["kappa"])
        self.assertEqual(W["G"]["product"], r["G"]["product"])
        self.assertEqual(W["eight_to_5"], r["eight_to_5"])
        self.assertEqual(W["classical_height5_product"], r["classical_height5_product"])
        self.assertAlmostEqual(W["base_upper_bound"], 31 ** 0.2, places=5)
        self.assertEqual(W["kakeya_F3_6_from_G_is_kakeya"], r["kakeya_F3_6_from_G"]["is_kakeya"])
        self.assertEqual(r["verdict"], "S7-TRUE")


if __name__ == "__main__":
    unittest.main()
