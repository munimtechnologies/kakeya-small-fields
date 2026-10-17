# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import unittest

import case_b as cb
import case_b_shapes as cs
import sat_aniso as sa


class TestCensus(unittest.TestCase):
    def test_counts(self):
        # By hand (notes/case-b-shapes.md): 8 x (64 + 6 x 8)^2 = 100,352 tuples tried. Lifting the
        # 24 systems of Lemma 34 gives 8 lifts each, 192 in all: b = 0 (shape c, A = 0) 24,
        # b = e_0 (shape d1) 24, b outside span(e_0) (shape d2) 144.
        self.assertEqual(cs.n_census(), {"tried": 100352, "systems": 192, "c": 24, "d1": 24,
                                         "d2": 144, "other": 0})

    def test_shapes_on_n(self):
        for shape, cls in zip(cs.SHAPES, ("c", "d1", "d2", "d2")):
            data = cs.shape_on_n(shape)
            self.assertIsNotNone(data)
            self.assertEqual(cs.classify_n(*data), cls)

    def test_not_a_shape(self):
        # beta = e_0 with sigma(n_1) = sigma(n_2) is not a system (Lemma 34: delta = a is excluded)
        self.assertEqual(cs.classify_n(0, 0, 2, 2, 1), "other")


class TestEncoding(unittest.TestCase):
    def test_unit_clauses(self):
        for t, k, shape, units in ((3, 2, "c", 9), (4, 2, "c", 12), (6, 3, "c", 54),
                                   (6, 3, "d1", 54), (6, 3, "d2c0", 54), (6, 3, "d2c1", 54)):
            base, _ = cb.encode_case_b(t, k)
            cnf, _ = cs.encode_shape(t, k, shape)
            self.assertEqual(cnf.nv, base.nv)
            self.assertEqual(cnf.clauses[:len(base.clauses)], base.clauses)
            added = cnf.clauses[len(base.clauses):]
            self.assertEqual(len(added), units)
            self.assertTrue(all(len(cl) == 1 for cl in added))
            self.assertEqual(len({abs(cl[0]) for cl in added}), units)

    def test_units_match_in_shape(self):
        # Build coordinates that carry exactly the forced values (everything else 0) and check
        # that the added unit clauses accept them and reject each one-bit change of a forced bit.
        for t, k, shape in ((4, 2, "c"), (6, 3, "d1"), (6, 3, "d2c1")):
            d = t + k - 1
            As, ss = [0] * d, [0] * d
            B = {key: 0 for key in itertools.combinations(range(d), 2)}
            ss[0] = 1
            for i in range(1, d):
                B[(0, i)] = cb.wanted_phi(i, k)
            S, Bs, C = cs.shape_values(t, k, shape)
            for i, s in S.items():
                ss[i] = s
            B.update(Bs)
            for (i, c), v in C.items():
                for r in range(t):
                    if (v >> r) & 1:
                        As[i] |= 1 << (t * r + c)
            self.assertTrue(cs.in_shape(As, ss, B, t, k, shape))
            cnf, names = cs.encode_shape(t, k, shape)
            base, _ = cb.encode_case_b(t, k)
            added = cnf.clauses[len(base.clauses):]
            val = sa.assignment(cnf, names, As, ss, B, t, d)
            self.assertTrue(all(val[cl[0]] if cl[0] > 0 else not val[-cl[0]] for cl in added))
            for i, s in S.items():
                ss2 = list(ss)
                ss2[i] ^= 1 << (t - 1)
                self.assertFalse(cs.in_shape(As, ss2, B, t, k, shape))
            for (i, c) in C:
                As2 = list(As)
                As2[i] ^= 1 << (t * (t - 1) + c)
                self.assertFalse(cs.in_shape(As2, ss, B, t, k, shape))

    def test_selfcheck_grades(self):
        st = cs.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])


if __name__ == "__main__":
    unittest.main()
