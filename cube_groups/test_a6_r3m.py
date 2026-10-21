# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for a6_r3m.py (job m30). Pure Python, no SAT solver; the expected values are worked
out by hand in m30/predictions.md and notes/a17.md."""
import unittest

import a6_r3 as r3
import a6_r3m as m
import sat_aniso as sa


def lemma63_ii():
    """Lemma 63 (ii) with a = h_0, b = h_1, e = e_0, f = e_1: sigma(a) = sigma(b) = e,
    sigma(a + b) = f, A_a = A_b = E_11 (the projection onto span(f) along span(e))."""
    p = sa.entries(2, [(1, 1)])
    return [p, p], [1, 1], {(0, 1): 1 ^ 1 ^ 2}


class TestMatrices(unittest.TestCase):
    def test_t2(self):
        # kernel span(e_0), image span(e_1): A e_1 = e_1, entry (1, 1), bit 3.
        self.assertEqual(m.matrices(2, (1,), (2,)), [8])
        # image span(e_0 + e_1): A e_1 = e_0 + e_1, entries (0, 1) and (1, 1), bits 1 and 3.
        self.assertEqual(m.matrices(2, (1,), (3,)), [10])
        # rank 0: kernel everything, image 0: the zero matrix only.
        self.assertEqual(m.matrices(2, (2, 1), ()), [0])

    def test_counts_and_exactness(self):
        for t, x1, r, n in ((4, (1, 2), (4, 8), 6), (6, (1, 2, 4), (8, 16, 32), 168)):
            x1, r = r3.rref(list(x1)), r3.rref(list(r))
            ms = m.matrices(t, x1, r)
            self.assertEqual(len(ms), n)
            self.assertEqual(len(set(ms)), n)
            for A in ms:
                self.assertEqual(m.ker_of(A, t), x1)
                self.assertEqual(m.im_of(A, t), r)

    def test_conjugation_moves_kernel_and_image(self):
        t = 4
        x1, r = r3.rref([1, 6]), r3.rref([8, 5])
        for g in r3.generators(t, "B", 3):
            for A in m.matrices(t, x1, r):
                C = m.conj(g, A, t)
                self.assertEqual(m.ker_of(C, t), r3.image(g, x1, t))
                self.assertEqual(m.im_of(C, t), r3.image(g, r, t))


class TestStabiliser(unittest.TestCase):
    def test_small_groups(self):
        self.assertEqual(len(m.group_elements(2, "A", 1)), 2)
        self.assertEqual(len(m.group_elements(2, "B", 1)), 1)
        self.assertEqual(len(m.group_elements(4, "B", 3)), 168)

    def test_transversal_and_schreier(self):
        t = 4
        x1, r, size = r3.orbits(t, "B", 3, 2)[0]
        gens, points, index, parent, via = m.pair_orbit(t, "B", 3, x1, r)
        self.assertEqual(len(points), size)
        root = points[0]
        for i in range(len(points)):
            ti = m.transversal(gens, parent, via, i, t)
            self.assertEqual((r3.image(ti, root[0], t), r3.image(ti, root[1], t)), points[i])
            inv = m.transversal(gens, parent, via, i, t, inverse=True)
            self.assertEqual(sa.mat_mul(inv, ti, t), m.identity(t))
        for i in range(len(points)):
            for gi in range(len(gens)):
                hg = m.schreier(gens, points, index, parent, via, i, gi, t)
                if hg is not None:
                    self.assertEqual((r3.image(hg, root[0], t), r3.image(hg, root[1], t)), root)

    def test_classes_equal_exact_orbits_t4(self):
        t = 4
        G = m.group_elements(t, "B", 3)
        for idx, (x1, r, size) in enumerate(r3.orbits(t, "B", 3, 2)):
            cl = m.classes(t, "B", 3, x1, r, seed=f"test-{idx}")
            ex, hsize = m.exact_classes(t, "B", 3, x1, r, G)
            self.assertEqual([mem for _, mem in cl], [mem for _, mem in ex])
            self.assertEqual(hsize * size, 168)
            self.assertEqual(sum(len(mem) for _, mem in cl), 6)

    def test_t2_classes(self):
        # Shape A, rank 1: two pair orbits, one matrix each. Shape B: three, one each.
        self.assertEqual([len(m.classes(2, "A", 1, x1, r)) for x1, r, _ in r3.orbits(2, "A", 1, 1)],
                         [1, 1])
        self.assertEqual([len(m.classes(2, "B", 1, x1, r)) for x1, r, _ in r3.orbits(2, "B", 1, 1)],
                         [1, 1, 1])


class TestEncodingAndNames(unittest.TestCase):
    def test_accepts_the_lemma63_model_with_its_own_matrix_only(self):
        As, ss, B = lemma63_ii()
        cnf, names = m.encode_r3m(2, 2, "B", 1, 1, (1,), (2,), 8)
        self.assertTrue(sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, 2, 2)))
        cnf, names = m.encode_r3m(2, 2, "B", 1, 1, (1,), (2,), 0)
        self.assertFalse(sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, 2, 2)))

    def test_expected_controls(self):
        self.assertEqual(m.expected_control(2, 1, "A", (2,)), "UNSAT")
        self.assertEqual(m.expected_control(2, 1, "A", (1,)), "UNSAT")
        self.assertEqual(m.expected_control(2, 1, "B", (2,)), "SAT")
        self.assertEqual(m.expected_control(2, 1, "B", (3,)), "UNSAT")
        self.assertEqual(m.expected_control(2, 0, "A", ()), "SAT")
        self.assertEqual(m.expected_control(4, 2, "B", (8, 4)), "UNSAT")

    def test_names_and_order(self):
        self.assertEqual(m.instance_name(6, 3, "A", 5, 7, 3), "r3m_t6_r3_A5_o007_m003")
        sps = m.specs(4, 5, 2, "B", 3)
        self.assertEqual(len({sp["name"] for sp in sps}), len(sps))
        self.assertEqual(sorted(sp["orbit"] for sp in sps if sp["cls"] == 0), list(range(7)))
        self.assertEqual([sp["cls"] for sp in sps], sorted(sp["cls"] for sp in sps))
        for sp in sps:
            self.assertEqual(m.ker_of(sp["au"], 4), r3.rref(sp["x1"]))
            self.assertEqual(m.im_of(sp["au"], 4), r3.rref(sp["r"]))

    def test_t2_table_has_no_rank1_shape_a(self):
        counts = m.t2_ranks_and_shapes()
        self.assertEqual(sum(counts.values()), 72)
        self.assertNotIn("r1_A1", counts)
        self.assertEqual(counts.get("r1_B1"), 36)
        self.assertEqual(counts.get("r0_A1"), 18)


if __name__ == "__main__":
    unittest.main()
