# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m107.py (job m107, notes/a99.md). Needs m42.py, sat_aniso.py, m100.py to m106.py
and python-sat next to it. Every expected value below was worked out by hand. The group checks are
tested against what each group states: a model of the CNF with all twelve groups must pass all of
them, and a one-entry change that breaks one stated property must be caught by that check only."""
import unittest

import m100
import m102
import m106
import m107
import sat_aniso as sa


class TestStatic(unittest.TestCase):
    def test_minimize_groups(self):
        def oracle(s):
            return "UNSAT" if "M" in s and ("Z" in s or "S1" in s) else "SAT"
        kept, why, log = m107.minimize_groups(oracle)
        # X, XE, CE, C, S2 go; S1 goes (Z and M still there); H4..H1 go; Z stays (only M left
        # would be SAT); M stays
        self.assertEqual(kept, ["Z", "M"])
        self.assertEqual(why, {"Z": "SAT", "M": "SAT"})
        self.assertEqual(len(log), 13)
        self.assertEqual(log[0], [None, "UNSAT"])
        self.assertTrue(m106.proven({"kept": kept, "why": why}))

    def test_minimize_groups_not_unsat(self):
        kept, why, log = m107.minimize_groups(lambda s: "UNKNOWN")
        self.assertIsNone(kept)
        self.assertEqual(len(log), 1)

    def test_minimize_groups_unknown(self):
        def oracle(s):
            if "H2" not in s:
                return "SAT"
            return "UNSAT" if "C" in s else "UNKNOWN"
        kept, why, _ = m107.minimize_groups(oracle)
        self.assertEqual(kept, ["H2", "C"])
        self.assertEqual(why, {"C": "UNKNOWN", "H2": "SAT"})
        self.assertFalse(m106.proven({"kept": kept, "why": why}))

    def test_lists(self):
        self.assertEqual(sorted(m107.DROP_ORDER), sorted(m107.GROUPS))
        self.assertEqual(len(set(m107.GROUPS)), 12)
        self.assertEqual(len(set(m107.OPEN_D2)), 4)
        self.assertTrue(set(m107.OPEN_D2) <= set(m106.UNKNOWN_D2))
        self.assertEqual(sum(m107.HIGH_BY_CLASS.values()), 88)
        self.assertEqual(sum(m107.HIGH_BY_K.values()), 88)

    def test_counts_by_hand(self):
        # m42.add_hints added 162 conditions in jobs m100a and m101a; m100's sweep has 144
        c = m107.COUNTS
        self.assertEqual(c["H1"] + c["H2"] + c["H3"] + c["H4"], 162)
        self.assertEqual(c["S1"] + c["S2"], m100.SWEEP_CONDITIONS)


class TestControl(unittest.TestCase):
    """o000_c000, t2 with M = J (the positive control of m102 to m106): SAT with no anisotropy."""

    @classmethod
    def setUpClass(cls):
        from pysat.solvers import Solver
        cls.spec, cls.case = m106.transfer_controls()[0]
        cnf, names, cls.counts = m107.build_groups(cls.spec, cls.case, m107.GROUPS)
        cls.hash, cls.n, cls.nv = m100.clause_hash(cnf), len(cnf.clauses), cnf.nv
        s = Solver(name="cadical195", bootstrap_with=cnf.clauses)
        cls.sat = s.solve()
        As, ss, B = sa.decode(s.get_model(), names, m107.T, m107.D)
        s.delete()
        del cnf
        cls.res = {"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]}

    def test_same_as_relax(self):
        ref, _, _ = m102.build(self.spec, self.case, "relax")
        self.assertEqual((m100.clause_hash(ref), len(ref.clauses), ref.nv), (self.hash, self.n,
                                                                             self.nv))

    def test_counts(self):
        want = dict(m107.COUNTS, XE=30, CE=23)
        self.assertEqual(self.counts, want)

    def test_dropping_unit_groups(self):
        # Z (64) and S2 (24) are unit clauses on variables that exist anyway
        keep = [g for g in m107.GROUPS if g not in ("Z", "S2")]
        cnf, _, counts = m107.build_groups(self.spec, self.case, keep)
        self.assertEqual((len(cnf.clauses), cnf.nv), (self.n - 88, self.nv))
        self.assertNotIn("Z", counts)
        self.assertNotIn("S2", counts)

    def test_model_meets_every_group(self):
        self.assertTrue(self.sat)
        chk = m107.group_checks(self.spec, self.case, self.res)
        self.assertEqual(sorted(k for k, v in chk.items() if not v), [])
        self.assertEqual(sorted(chk), sorted(m107.GROUPS))

    def changed(self, which, i, bit):
        res = {"A": list(self.res["A"]), "s": list(self.res["s"]),
               "B": [list(x) for x in self.res["B"]]}
        if which == "A":
            res["A"][i] ^= bit
        elif which == "s":
            res["s"][i] ^= bit
        else:
            for x in res["B"]:
                if (x[0], x[1]) == i:
                    x[2] ^= bit
        return m107.group_checks(self.spec, self.case, res)

    def test_checks_catch_changes(self):
        # In o000_c000, X_1 = ker A_u = span(e_0..e_4) and R = Im A_u = span(e_0, e_1, e_2).
        # Entry (0, 5) of A_(v_1): column e_5 (not x0, not in X_1) gains e_0, which is in R.
        chk = self.changed("A", 1, 1 << 5)
        self.assertFalse(chk["Z"])
        self.assertTrue(chk["H1"] and chk["H2"] and chk["S1"] and chk["M"])
        # the same entry of A_(v_3): the case's map is broken, nothing else
        chk = self.changed("A", 3, 1 << 5)
        self.assertFalse(chk["M"])
        self.assertTrue(chk["H1"] and chk["H2"] and chk["S1"] and chk["Z"])
        # sigma(v_1) gains e_7, which is not in X_1
        chk = self.changed("s", 1, 1 << 7)
        self.assertFalse(chk["H3"])
        self.assertTrue(chk["H1"] and chk["Z"] and chk["S2"])
        # beta(v_1, v_2) gains e_0: no longer 0, still in X_1
        chk = self.changed("B", (1, 2), 1)
        self.assertFalse(chk["S2"])
        self.assertTrue(chk["H4"] and chk["X"] and chk["H3"])


if __name__ == "__main__":
    unittest.main()
