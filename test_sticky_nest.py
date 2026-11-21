# Tests for sticky_nest.py (stdlib only; the CP-SAT models are not built here).
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.

import random
import unittest

import sticky_s7 as s7
import sticky_kexact as kx
import sticky_nest as nest


def random_child_maps(h, rng):
    return {a: tuple(rng.randrange(3) for _ in range(3)) for a in kx.prefixes(h)}


def random_family_tree(h, rng, reflect=False, shear=None):
    """A random height-h tree with quadratic root; optionally child2 = child1(-e) and/or
    child1(e) = child0(-e) - e + shear."""
    c = rng.randrange(3)
    maps = {(): tuple((x * x + c) % 3 for x in range(3))}
    kids = [random_child_maps(h - 1, rng) for _ in range(3)]
    if shear is not None:
        kids[1] = {a: tuple((kids[0][nest.neg(a)][(-x) % 3] - x + shear[len(a)]) % 3 for x in range(3))
                   for a in kx.prefixes(h - 1)}
    if reflect:
        kids[2] = {a: tuple(kids[1][nest.neg(a)][(-x) % 3] for x in range(3)) for a in kx.prefixes(h - 1)}
    for x in range(3):
        for a, g in kids[x].items():
            maps[(x,) + a] = g
    return maps


def encoding_holds(maps, h, w):
    """Evaluate the CP-SAT shear constraints exactly as add_shear_tie writes them."""
    for k1, k0, j, x in nest.shear_pairs(h):
        v = maps[k1[0]][k1[1]]
        if maps[k0[0]][k0[1]] != (v + x - w[j]) % 3:
            return False
    return True


class TestFamilies(unittest.TestCase):
    def setUp(self):
        self.mA = kx.maps_of(s7.tree_A, 3)
        self.mB = kx.maps_of(s7.tree_B, 3)
        self.mH = kx.maps_of(s7.tree_H, 4)

    def test_a196_trees(self):
        self.assertTrue(nest.is_quadratic_root(self.mA))
        self.assertTrue(nest.is_quadratic_root(self.mB))
        self.assertTrue(nest.reflect_ok(self.mA, 3))
        self.assertFalse(nest.reflect_ok(self.mB, 3))
        self.assertEqual(nest.shear_w(self.mB, 3), [1, 0])
        self.assertTrue(encoding_holds(self.mB, 3, [1, 0]))
        self.assertFalse(encoding_holds(self.mB, 3, [0, 0]))
        self.assertTrue(nest.reflect_ok(self.mH, 4))
        self.assertIsNone(nest.shear_w(self.mH, 4))

    def test_roots(self):
        self.assertFalse(nest.is_quadratic_root({(): (0, 0, 0)}))
        self.assertTrue(nest.is_quadratic_root({(): (1, 2, 2)}))
        self.assertTrue(nest.is_quadratic_root({(): (2, 0, 0)}))
        self.assertFalse(nest.is_quadratic_root({(): (0, 1, 2)}))

    def test_sanity_hints_in_every_family(self):
        hA, hB = kx.pair_hint(self.mA, self.mB, 3)
        self.assertEqual(kx.lam0(hA, hB, 3), 31)
        for fam in nest.FAMILIES:
            self.assertTrue(nest.in_family(hA, hB, fam, 3), fam)
        # the model fixes B's translation, which forces B's root to x^2 + 2
        self.assertEqual(hB[()], (2, 0, 0))
        self.assertEqual(nest.shear_w(hB, 3), [1, 0])

    def test_height4_hint(self):
        hA, hB = kx.pair_hint(self.mH, self.mH, 4)
        self.assertEqual(kx.lam0(hA, hB, 4), 62)
        self.assertTrue(nest.in_family(hA, hB, "F2", 4))
        self.assertTrue(nest.in_family(hA, hB, "F1", 4))
        self.assertFalse(nest.in_family(hA, hB, "F0", 4))
        self.assertEqual(hB[()], (2, 0, 0))

    def test_random_members(self):
        rng = random.Random(3)
        for h in (2, 3, 4):
            for _ in range(5):
                w = [rng.randrange(3) for _ in range(h - 1)]
                A = random_family_tree(h, rng, reflect=True)
                B = random_family_tree(h, rng, shear=w)
                self.assertTrue(s7.is_sticky(kx.fn_of(A), h))
                self.assertTrue(s7.is_sticky(kx.fn_of(B), h))
                self.assertTrue(nest.in_family(A, B, "F0", h))
                self.assertEqual(nest.shear_w(B, h), w)
                self.assertTrue(encoding_holds(B, h, w))
                # a common translation keeps the pair in the family and keeps lambda
                c = [rng.randrange(3) for _ in range(h)]
                A2, B2 = kx.shift_maps(A, c), kx.shift_maps(B, c)
                self.assertTrue(nest.in_family(A2, B2, "F0", h))
                self.assertEqual(kx.lam0(A, B, h), kx.lam0(A2, B2, h))

    def test_pair_partition(self):
        """The reflect and shear pairs touch every child key exactly once."""
        for h in (2, 3, 4):
            keys2 = [k2 for k2, _ in nest.reflect_pairs(h)]
            keys1 = [k1 for _, k1 in nest.reflect_pairs(h)]
            n = len(kx.prefixes(h - 1)) * 3
            self.assertEqual(len(set(keys2)), n)
            self.assertEqual(len(set(keys1)), n)
            self.assertTrue(all(k[0][0] == 2 for k in keys2))
            self.assertTrue(all(k[0][0] == 1 for k in keys1))
            sk1 = [p[0] for p in nest.shear_pairs(h)]
            sk0 = [p[1] for p in nest.shear_pairs(h)]
            self.assertEqual(len(set(sk1)), n)
            self.assertEqual(len(set(sk0)), n)
            self.assertTrue(all(k[0][0] == 1 for k in sk1))
            self.assertTrue(all(k[0][0] == 0 for k in sk0))


class TestVerdict(unittest.TestCase):
    def rec(self, name, status, v, bound=None, hint=None, hint_ok=None, ok=True):
        return {"name": name, "status": status, "objective": v,
                "bound": bound if bound is not None else v, "verified_value": v,
                "verified_ok": ok, "hint_value": hint, "hint_in_family": hint_ok}

    def sanity(self):
        return [self.rec(n, "OPTIMAL", 31, hint=31, hint_ok=True) for n in nest.SANITY]

    def test_closed(self):
        recs = self.sanity() + [self.rec("F0_h4", "OPTIMAL", 64, hint=62, hint_ok=False),
                                self.rec("F1_h4", "FEASIBLE", 62, bound=45, hint=62, hint_ok=True)]
        v = nest.verdict(recs)
        self.assertEqual(v["verdict"], "FAMILY-CLOSED")
        self.assertIn("F0-CLOSED", v["flags"])
        self.assertEqual(v["height6_best_found"], 62)

    def test_beats(self):
        recs = self.sanity() + [self.rec("F1_h4", "FEASIBLE", 61, bound=40, hint=62, hint_ok=True)]
        v = nest.verdict(recs)
        self.assertEqual(v["verdict"], "H6-BEATS")
        self.assertAlmostEqual(v["base_upper_bound"], round(61 ** (1.0 / 6), 6))

    def test_undecided(self):
        recs = self.sanity() + [self.rec("F2_h4", "FEASIBLE", 62, bound=38, hint=62, hint_ok=True),
                                {"name": "F0_h4", "status": "UNKNOWN", "objective": None, "bound": 30,
                                 "verified_value": None, "hint_value": 62, "hint_in_family": False}]
        self.assertEqual(nest.verdict(recs)["verdict"], "UNDECIDED")

    def test_bugs(self):
        recs = self.sanity()
        recs[0] = self.rec("F0_h3", "OPTIMAL", 30, hint=31, hint_ok=True)
        self.assertEqual(nest.verdict(recs)["verdict"], "BUG")
        self.assertEqual(nest.verdict(self.sanity()[:2])["verdict"], "BUG")
        recs = self.sanity() + [self.rec("F1_h4", "FEASIBLE", 62, hint=62, hint_ok=False)]
        self.assertEqual(nest.verdict(recs)["verdict"], "BUG")
        recs = self.sanity() + [self.rec("F2_h4", "FEASIBLE", 62, bound=63, hint=62, hint_ok=True)]
        self.assertEqual(nest.verdict(recs)["verdict"], "BUG")
        recs = self.sanity() + [self.rec("F2_h4", "FEASIBLE", 59, bound=40, hint=62, hint_ok=True)]
        self.assertEqual(nest.verdict(recs)["verdict"], "BUG")
        recs = self.sanity()
        recs[1] = self.rec("F1_h3", "OPTIMAL", 32, hint=31, hint_ok=True)
        self.assertEqual(nest.verdict(recs)["verdict"], "BUG")


if __name__ == "__main__":
    unittest.main()
