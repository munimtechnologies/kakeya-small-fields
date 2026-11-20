# Tests for sticky_l4.py (job sticky-l4-v1).  MV2 of Munim, Inc.; made with AI agents working in
# MV2's name.  Licence: Apache-2.0.  The solver tests run only when ortools is installed.

import importlib.util
import random
import unittest

import sticky_s7 as s7
import sticky_kexact as kx
import sticky_l4 as l4

HAVE_ORTOOLS = importlib.util.find_spec("ortools") is not None


def random_maps(h, rng):
    return {a: tuple(rng.randrange(3) for _ in range(3)) for a in kx.prefixes(h)}


class TestStructure(unittest.TestCase):
    def test_split_assemble_roundtrip(self):
        rng = random.Random(1)
        for h in (2, 3, 4):
            for _ in range(5):
                mp = random_maps(h, rng)
                r, kids = l4.split(mp)
                self.assertEqual(l4.assemble(r, kids), mp)
                for x in range(3):
                    self.assertEqual(set(kids[x].keys()), set(kx.prefixes(h - 1)))

    def test_parent_slices_from_children(self):
        """S_t = union over x of {g(x) + t x} x S_t(child x): the identity the kappa_cut model uses."""
        rng = random.Random(2)
        for h in (2, 3, 4):
            for _ in range(8):
                mp = random_maps(h, rng)
                r, kids = l4.split(mp)
                ks = [kx.slices_of(kids[x], h - 1) for x in range(3)]
                self.assertEqual(l4.slices_from_children(r, ks), kx.slices_of(mp, h))

    def test_height1_front(self):
        self.assertEqual(l4.height1_front(), [(1, 3, 3), (2, 2, 2), (3, 1, 3), (3, 3, 1)])

    def test_kappa0_translation_invariant(self):
        rng = random.Random(3)
        for h in (2, 3):
            mp = random_maps(h, rng)
            self.assertEqual(kx.kappa0(kx.normalised(mp, h, range(h)), h), kx.kappa0(mp, h))

    def test_known_trees(self):
        mA = kx.maps_of(s7.tree_A, 3)
        mB = kx.maps_of(s7.tree_B, 3)
        hA, hB = kx.pair_hint(mA, mB, 3)
        self.assertEqual(kx.lam0(hA, hB, 3), 31)
        mH = kx.maps_of(s7.tree_H, 4)
        self.assertEqual([len(x) for x in kx.slices_of(mH, 4)], [11, 20, 20])

    def test_minimal_and_dominates(self):
        F = l4.minimal([(2, 2, 2), (3, 3, 3), (1, 3, 3), (1, 4, 4)])
        self.assertEqual(F, [(1, 3, 3), (2, 2, 2)])
        self.assertTrue(l4.dominates_some((2, 3, 2), F))
        self.assertFalse(l4.dominates_some((1, 2, 9), F))


@unittest.skipUnless(HAVE_ORTOOLS, "ortools not installed")
class TestModels(unittest.TestCase):
    def test_kappa_cut_h2(self):
        F1 = l4.height1_front()
        rec = l4.run_kappa_cut("t", 2, F1, 120, 2)
        self.assertEqual(rec["status"], "OPTIMAL")
        self.assertEqual(rec["verified_value"], 8)
        self.assertTrue(rec["verified_ok"])

    def test_kappa_cut_h2_cap_infeasible(self):
        rec = l4.run_kappa_cut("t", 2, l4.height1_front(), 120, 2, cap=7)
        self.assertEqual(rec["status"], "INFEASIBLE")
        self.assertEqual(rec["bound"], 8)

    def test_pair_cut_h1_matches_brute_force(self):
        best = None
        for a in l4.itertools_product3():
            for b in l4.itertools_product3():
                mA = {(): a}
                mB = {(): b}
                v, _ = kx.lam_best(mA, mB, 1)
                best = v if best is None else min(best, v)
        rec = l4.run_pair_cut("t", 1, l4.height1_front(), 120, 2)
        self.assertEqual(rec["status"], "OPTIMAL")
        self.assertEqual(rec["verified_value"], best)
        self.assertTrue(rec["verified_ok"])

    def test_pair_cut_h2_is_16(self):
        rec = l4.run_pair_cut("t", 2, None, 300, 2)
        self.assertEqual(rec["status"], "OPTIMAL")
        self.assertEqual(rec["verified_value"], 16)
        self.assertTrue(rec["verified_ok"])


if __name__ == "__main__":
    unittest.main()
