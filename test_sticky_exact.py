# test_sticky_exact.py -- checks for sticky_exact.py (pre-registered job sticky-exact-v1, note a186).
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  The solver tests run only where ortools is installed.

import importlib.util
import itertools
import random
import unittest

import sticky_exact as se
import sticky_planes as sp

HAVE_ORTOOLS = importlib.util.find_spec("ortools") is not None


class TestSymmetries(unittest.TestCase):

    def test_prefix_count(self):
        for n in range(1, 6):
            self.assertEqual(len(se.prefixes(n)), (3 ** n - 1) // 2)

    def test_normalize_keeps_size_and_fixes_translation(self):
        rng = random.Random(11)
        for n in (1, 2, 3, 4):
            for _ in range(60):
                maps = sp.random_maps(n, rng)
                nm = se.normalize(maps, n)
                self.assertEqual(len(sp.kakeya_set(maps, n)), len(sp.kakeya_set(nm, n)))
                for j in range(n):
                    self.assertEqual(nm[(1,) * j][1], 0)

    def test_construction_has_reduced_form(self):
        rng = random.Random(12)
        for m in (1, 2, 3):
            for _ in range(60):
                mK = sp.random_maps(m, rng)
                mT = sp.random_maps(m, rng)
                w = tuple(rng.randrange(3) for _ in range(m))
                maps = sp.construct(mK, mT, 0, w, m)
                self.assertTrue(se.is_reduced_form(maps, m + 1))
                nm = se.normalize(maps, m + 1)
                self.assertTrue(se.is_reduced_form(nm, m + 1))
                self.assertEqual(len(sp.kakeya_set(nm, m + 1)), sp.formula_size(mK, mT, 0, w, m))

    def test_classical_reduces(self):
        # the classical set is reached by the reduced model: K' classical, T classical, h = 0
        for m in (1, 2, 3):
            best = None
            for w in itertools.product(range(3), repeat=m):
                v = sp.formula_size(sp.classical_maps(m), sp.classical_maps(m), 0, w, m)
                best = v if best is None else min(best, v)
            self.assertLessEqual(best, 2 ** (m + 2) - 1)

    def test_verdict_rules(self):
        base = []
        for n, v in ((2, 7), (3, 15)):
            for model in ("full", "reduced"):
                base.append({"n": n, "model": model, "status": "OPTIMAL", "objective": v,
                             "verified_size": v, "bound": v})
        r = se.verdict(base + [{"n": 4, "model": "reduced", "status": "OPTIMAL", "objective": 31,
                                "verified_size": 31, "bound": 31}])
        self.assertEqual(r["sanity"], "OK")
        self.assertEqual(r["n4"], "S4-CLASSICAL")
        r = se.verdict(base + [{"n": 4, "model": "full", "status": "FEASIBLE", "objective": 30,
                                "verified_size": 30, "bound": 27}])
        self.assertEqual(r["n4"], "S4-BREAK")
        r = se.verdict(base + [{"n": 4, "model": "full", "status": "FEASIBLE", "objective": 28,
                                "verified_size": 28, "bound": 20}])
        self.assertEqual(r["n4"], "BUG")
        r = se.verdict(base + [{"n": 4, "model": "full", "status": "FEASIBLE", "objective": 31,
                                "verified_size": 31, "bound": 29}])
        self.assertEqual(r["n4"], "UNDECIDED")
        r = se.verdict(base[:-1])
        self.assertEqual(r["sanity"], "BUG")


@unittest.skipUnless(HAVE_ORTOOLS, "ortools not installed")
class TestSolver(unittest.TestCase):

    def test_small_dimensions(self):
        for n, want in ((1, 3), (2, 7), (3, 15)):
            for reduced in (False, True):
                rec = se.solve(n, reduced, 300, 4)
                self.assertEqual(rec["status"], "OPTIMAL")
                self.assertEqual(rec["objective"], want)
                self.assertEqual(rec["verified_size"], want)
                self.assertTrue(rec["is_kakeya"])


if __name__ == "__main__":
    unittest.main()
