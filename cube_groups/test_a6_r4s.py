# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests of a6_r4s.py (Lemma 66, job m26). Pure Python: no SAT solver is needed."""
import json
import os
import tempfile
import unittest

import a6_r4s
import sat_aniso as sa
import shape_c2 as s2


class TestSmall(unittest.TestCase):
    """2 x 2 matrices (t = 4): the class representatives are 0, 1 = diag(1, 0), 2 = J2 (e_1 -> e_0),
    6 = the swap, 7 = [[1, 1], [1, 0]] (x^2 + x + 1) and 9 = I; q = 1, 2, 3 are e_0, e_1, e_0 + e_1."""

    def test_moves(self):
        self.assertEqual(a6_r4s.moves(2, 1, "i", 2), [(2, 1)])        # (I + J2)^-1 J2 = J2
        self.assertEqual(a6_r4s.moves(2, 2, "iii", 2), [(11, 2)])     # (I + J2)^-1 = I + J2
        self.assertEqual(a6_r4s.moves(6, 3, "ii", 2), [(6, 3)])       # swap^-1 = swap
        self.assertEqual(a6_r4s.moves(6, 1, "iii", 2), [(15, 1)])     # swap^-1 + I
        self.assertEqual(a6_r4s.moves(7, 1, "iii", 2), [(7, 1), (7, 1)])
        self.assertEqual(a6_r4s.moves(1, 2, "i", 2), [])              # M and I + M singular
        self.assertEqual(a6_r4s.moves(1, 1, "ii", 2), [])
        self.assertEqual(a6_r4s.moves(1, 3, "iii", 2), [])
        self.assertEqual(a6_r4s.moves(0, 1, "i", 2), [(0, 1)])
        self.assertEqual(a6_r4s.moves(9, 1, "ii", 2), [(9, 1)])

    def test_canonical(self):
        # 11 = I + J2 and 15 = [[1, 1], [1, 1]] are conjugate to 6 and 2; the type iii orbits
        # there are {1, 2} (least 1) and {2, 3} (least 2).
        self.assertEqual(a6_r4s.canonical(11, 2, 2), (6, 1))
        self.assertEqual(a6_r4s.canonical(15, 1, 2), (2, 2))
        self.assertEqual(a6_r4s.canonical(7, 1, 2), (7, 1))
        tr = a6_r4s.transporters(2)
        self.assertEqual(len(tr), 16)
        for A, g in tr.items():
            gi = sa.mat_inv(g, 2)
            self.assertIn(sa.mat_mul(sa.mat_mul(gi, A, 2), g, 2), (0, 1, 2, 6, 7, 9))

    def test_analysis_t4(self):
        an = a6_r4s.analysis(4)
        self.assertEqual(an["pairs"], [(0, 1, "i"), (1, 1, "ii"), (1, 2, "i"), (1, 3, "iii"),
                                       (2, 1, "i"), (2, 2, "iii"), (6, 1, "iii"), (6, 3, "ii"),
                                       (7, 1, "iii"), (9, 1, "ii")])
        self.assertIn([5, 6], an["classes"])
        self.assertEqual(len(an["classes"]), 9)
        self.assertEqual(an["counts"], a6_r4s.HAND[4])
        self.assertTrue(all(an["checks"].values()), an["checks"])
        self.assertTrue(an["graded"])
        self.assertEqual(len(an["edges"]), 7)        # the two moves of 7 coincide
        reps = [idx for idx, _ in a6_r4s.representatives(4)]
        self.assertEqual(reps, [i for i in range(13) if i != 7])

    def test_pending_t4(self):
        names = {idx: s2.instance_name(4, idx) for idx in range(13)}
        self.assertEqual([idx for idx, _ in a6_r4s.pending(4, [])],
                         [i for i in range(13) if i != 7])
        # the partner (6, 1) refuted: the class of (2, 2) is done
        self.assertEqual([idx for idx, _ in a6_r4s.pending(4, [names[7]])],
                         [i for i in range(13) if i not in (6, 7)])
        # one of the two instances of the type ii pair (6, 3) UNSAT: the other one stays
        self.assertEqual([idx for idx, _ in a6_r4s.pending(4, [names[8]])],
                         [i for i in range(13) if i not in (7, 8)])
        self.assertEqual([idx for idx, _ in a6_r4s.pending(4, [names[8], names[9]])],
                         [i for i in range(13) if i not in (7, 8, 9)])
        co = a6_r4s.class_of_instance(4)
        self.assertEqual(len(co), 13)
        self.assertEqual(co[names[6]], co[names[7]])
        self.assertEqual(co[names[8]], co[names[9]])
        self.assertEqual(len(set(co.values())), 9)

    def test_round_robin(self):
        items = [(0, (7, 1, "i", 0)), (1, (7, 2, "iii", 0)), (2, (9, 1, "ii", 0)),
                 (3, (9, 1, "ii", 1)), (4, (9, 3, "iii", 0)), (5, (11, 1, "iii", 0))]
        self.assertEqual([idx for idx, _ in a6_r4s.round_robin(items)], [0, 2, 5, 1, 3, 4])
        self.assertEqual(a6_r4s.round_robin([]), [])


class TestHandCounts(unittest.TestCase):
    def test_t3_t5(self):
        for t in (3, 5):
            an = a6_r4s.analysis(t)
            self.assertEqual(an["counts"], a6_r4s.HAND[t], (t, an["counts"]))
            self.assertTrue(all(an["checks"].values()), (t, an["checks"]))

    def test_t6(self):
        an = a6_r4s.analysis(6)
        self.assertEqual(an["counts"], a6_r4s.HAND[6], an["counts"])
        self.assertTrue(all(an["checks"].values()), an["checks"])
        reps = a6_r4s.representatives(6)
        self.assertEqual(len(reps), 123)
        self.assertEqual(sorted(a6_r4s.pending(6, [])), sorted(reps))
        co = a6_r4s.class_of_instance(6)
        self.assertEqual(len(co), 146)
        self.assertEqual(len(set(co.values())), 102)
        # the three irreducible quartics form the only class of three pairs
        three = [g for g in an["classes"] if len(g) == 3]
        self.assertEqual(len(three), 1)
        self.assertEqual({an["pairs"][i][2] for i in three[0]}, {"iii"})
        # every class of two pairs joins a singular M with an invertible one, or two
        # matrices of the same kind in the two type i / type ii swaps
        for g in an["classes"]:
            self.assertEqual(len({an["pairs"][i][2] for i in g}), 1)

    def test_selfcheck(self):
        st = a6_r4s.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])


class TestGrade(unittest.TestCase):
    def write(self, d, name, res):
        with open(os.path.join(d, name + ".json"), "w") as f:
            json.dump(res, f)

    def test_grade_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "selfcheck.json"), "w") as f:
                json.dump({"graded": {"all": True}}, f)
            for t in a6_r4s.CONTROLS:
                for idx, _ in a6_r4s.representatives(t):
                    name = s2.instance_name(t, idx)
                    self.write(d, name, {"status": "UNSAT", "name": name, "t": t})
            reps6 = a6_r4s.representatives(6)
            idx6, inst6 = reps6[0]
            n6 = s2.instance_name(6, idx6)
            self.write(d, n6, {"status": "UNKNOWN", "name": n6, "t": 6, "wall_seconds": 600.0})
            out = a6_r4s.grade(d)
            self.assertTrue(all(out["graded"].values()), out["graded"])
            self.assertEqual(len(out["graded"]), 1 + 3 + 12)
            self.assertEqual(out["ungraded"], {})
            self.assertEqual(out["counts"]["6"], {"UNKNOWN": 1, "missing": 122})
            self.assertEqual(out["decided_6"], [])
            self.assertEqual(out["refuted_classes_6"], 0)
            self.assertEqual(out["classes_6"], 102)
            self.assertFalse(out["all_unsat_6"])
            self.assertFalse(out["any_sat_6"])
            # an UNSAT of a one-instance pair refutes its class; the --unsat names count too
            self.write(d, n6, {"status": "UNSAT", "name": n6, "t": 6})
            out = a6_r4s.grade(d)
            self.assertEqual(out["decided_6"], [n6])
            one = [s2.instance_name(6, idx) for idx, (M, q, typ, c) in reps6 if typ != "ii"]
            self.assertGreaterEqual(out["refuted_classes_6"], 1 if n6 in one else 0)
            out = a6_r4s.grade(d, one)
            self.assertEqual(out["refuted_classes_6"], len(one))
            # the 42 type ii instances are left, one of them (n6) UNSAT
            self.assertEqual(out["counts"]["6"], {"UNSAT": 1, "missing": 123 - len(one) - 1})
            # a SAT answer at t = 4 fails the grade
            name4 = s2.instance_name(4, a6_r4s.representatives(4)[0][0])
            self.write(d, name4, {"status": "SAT", "name": name4, "t": 4, "verified": False,
                                  "facts": {"max_rank": 2}})
            out = a6_r4s.grade(d)
            self.assertFalse(out["graded"][name4])
            self.assertFalse(out["graded"][name4 + "_verified"])

    def test_grade_missing(self):
        with tempfile.TemporaryDirectory() as d:
            out = a6_r4s.grade(d)
            self.assertEqual(out["ungraded"]["selfcheck"], "missing")
            self.assertEqual(out["counts"]["3"], {"missing": 3})
            self.assertEqual(out["counts"]["4"], {"missing": 12})
            self.assertEqual(out["counts"]["6"], {"missing": 123})


if __name__ == "__main__":
    unittest.main()
