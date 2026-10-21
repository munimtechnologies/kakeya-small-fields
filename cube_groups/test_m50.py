# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m50.py (job m50). The full comparison of the XOR encoding with the CNF and the
classification checks are in --part check, which the job runs as its own step."""
import json
import os
import random
import tempfile
import unittest

import m42
import m50 as m
import sat_aniso as sa

try:
    import pycryptosat  # noqa: F401
    HAVE_CMS = True
except ImportError:
    HAVE_CMS = False


class TestM50(unittest.TestCase):
    def test_tables(self):
        self.assertEqual(len(m.CALIB), 9)
        self.assertEqual(len(m.TARGETS), 5)
        self.assertFalse(set(m.CALIB) & set(m.TARGETS))
        self.assertEqual(sorted(m.HAND_D), sorted(m.CALIB + m.TARGETS))
        self.assertTrue(set(m.HOST_CONTROL) <= set(m.CALIB))
        self.assertEqual(sorted(n for n in m.TARGETS if m.HAND_D[n] == 3),
                         ["r3b_t7_B5_o000_c000", "r3b_t7_B5_o020_c000", "r3b_t7_B6_o002_c000"])

    def test_specs(self):
        for name in m.CALIB + m.TARGETS:
            sp = m.spec_of(name)
            self.assertEqual(m42.instance_name(7, sp["p"], sp["pair"], sp["cls"]), name)
            self.assertEqual(m42.kernel(sp["au"], 7), tuple(sp["x1"]))
            self.assertEqual(m42.column_space(sp["au"], 7), tuple(sp["r"]))
            self.assertEqual(m42.dim_meet(tuple(sp["x1"]), tuple(sp["r"])), m.HAND_D[name])
        for name in ("r3b_t7_B5_o000_c000", "r3b_t7_B5_o020_c000", "r3b_t7_B6_o002_c000"):
            au = m.spec_of(name)["au"]
            self.assertEqual(sa.mat_mul(au, au, 7), 0)

    def test_budget(self):
        # Worst case of the solve part: 600 + 3216.9 + 424.05 + 3600 s, about 131 minutes.
        total = sum(cap for _, _, cap in m.plan())
        self.assertAlmostEqual(total, 7840.95, places=1)
        self.assertLess(total, 150 * 60)

    def test_xor_encoding(self):
        rng = random.Random(7)
        cases = 0
        for t, d, As, ss, B in sa.random_examples(rng, 30):
            at, sv = sa.tables(As, ss, B, d)
            ok = sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
            plain = sa.encode(t, d, echelon=False)
            xcnf = m.with_xor(sa.encode, t, d, True, True, False)
            self.assertIsInstance(xcnf[0], m.XorCNF)
            self.assertEqual(m.accepts(xcnf[0], sa.assignment(xcnf[0], xcnf[1], As, ss, B, t, d)),
                             ok)
            self.assertEqual(m.accepts(plain[0], sa.assignment(plain[0], plain[1], As, ss, B, t,
                                                                d)), ok)
            cases += 1
        self.assertEqual(cases, 30)
        self.assertIsNot(sa.CNF, m.XorCNF)        # with_xor restores sat_aniso.CNF
        self.assertNotIsInstance(sa.encode(2, 2)[0], m.XorCNF)

    def test_planted(self):
        As, ss, B = m42.planted()
        cnf, names = m.build(m42.planted_spec(), "xor")
        self.assertTrue(m.accepts(cnf, sa.assignment(cnf, names, As, ss, B, 6, 6)))
        self.assertGreater(len(cnf.xors), 0)

    @unittest.skipUnless(HAVE_CMS, "pycryptosat not installed")
    def test_tiny_solves(self):
        with tempfile.TemporaryDirectory() as d:
            for t, dd, want in ((2, 2, "SAT"), (2, 3, "UNSAT")):
                path = os.path.join(d, "c.json")
                m.child(m.small_spec(t, dd), "xor", path)
                with open(path) as f:
                    res = json.load(f)
                self.assertEqual(res["status"], want)
                if want == "SAT":
                    m.verify(m.small_spec(t, dd), res)
                    self.assertTrue(res["verified"])


if __name__ == "__main__":
    unittest.main()
