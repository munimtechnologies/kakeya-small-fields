# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m97.py (job m97). The expected answers of the reduced system at (4, 2) and for
(N, N^2) at (6, 3) are the hand derivations of notes/a89.md."""
import unittest

import m94
import m97 as m


class TestM97(unittest.TestCase):
    def test_mat_x(self):
        N1, N2 = m94.SHIFT, m94.SHIFT2
        self.assertEqual(m.mat_x([N1, N2], 1), [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
        self.assertEqual(m.mat_x([N1, N2], 6), m94.add(N1, N2))
        self.assertEqual(m94.mul(N1, N1), N2)
        self.assertEqual(len(m.span_index([N1, N2])), 8)
        with self.assertRaises(ValueError):
            m.span_index([N1, N1])

    def test_squares_t4(self):
        # N^2 = 0, E^2 = E, (I + N)^2 = I, F^2 = F + I
        want = {"t4_N": 0, "t4_E": 2, "t4_IN": 1, "t4_F": 3}
        for name, z in want.items():
            Ms = m.SMALL[name][2]
            self.assertEqual(m.squares(Ms), ({2: z}, None))

    def test_reduced_t4(self):
        st = {name: m.reduced(m.SMALL[name][2]) for name in ("t4_N", "t4_E", "t4_IN", "t4_F")}
        self.assertEqual(st["t4_N"]["status"], "SAT")
        self.assertEqual(st["t4_E"]["status"], "SAT")
        # (G + G^2) e_1 != 0: the step "linear" fails for every choice
        self.assertEqual((st["t4_IN"]["status"], st["t4_IN"]["stage"]), ("UNSAT", "linear"))
        self.assertEqual((st["t4_F"]["status"], st["t4_F"]["stage"]), ("UNSAT", "linear"))
        # with anisotropy E is out (q(e_1) = 0), N is not
        self.assertEqual(m.reduced(m.SMALL["t4_E"][2], "aniso1")["stage"], "q_zero")
        self.assertEqual(m.reduced(m.SMALL["t4_N"][2], "aniso2")["status"], "SAT")

    def test_reduced_shift(self):
        res = m.reduced(m.SMALL["t6_shift"][2])
        self.assertEqual((res["status"], res["stage"]), ("UNSAT", "no_invertible_S"))
        # one choice of G passes the linear conditions (G_1 e_2 = G_2 e_1 = e_2)
        self.assertEqual(res["counts"]["linear"], 1)
        self.assertEqual(res["z"], {2: 4, 4: 0, 6: 4})

    def test_reduced_witness(self):
        for name in ("t4_N", "t6_e00e11", "t6_e00e12"):
            Ms = m.SMALL[name][2]
            res = m.reduced(Ms)
            self.assertEqual(res["status"], "SAT", name)
            k = len(Ms) + 1
            S = res["S_rows"]
            self.assertEqual(m.sa.rank_f2(S), k)
            # the witness satisfies M_i S w_y = S H_y e_i, recomputed directly
            G = res["G"]
            for y, w in res["w"].items():
                Gy = [0] * k
                for a in range(1, k):
                    if y >> a & 1:
                        Gy = [x ^ g for x, g in zip(Gy, G[a])]
                H = [g ^ m.g_apply(Gy, g) for g in Gy]
                Sw = sum((bin(S[r] & w).count("1") & 1) << r for r in range(k))
                for i in range(1, k):
                    SH = sum((bin(S[r] & H[i]).count("1") & 1) << r for r in range(k))
                    self.assertEqual(m.m95.apply(Ms[i - 1], Sw), SH)

    def test_idempotent_orbits(self):
        # every orbit whose W contains E_00 has z_(e_1) = e_1, so q(e_1) = 0 with anisotropy
        # (unless a square outside the span already rules it out)
        count = 0
        for i, w, s in m.N4_ORBITS:
            if w[0] == 1:
                count += 1
                Ms = [m94.m_of(x, 4) for x in w]
                self.assertEqual(m.mat_x(Ms, 2), [[1, 0, 0, 0], [0] * 4, [0] * 4, [0] * 4])
                res = m.reduced(Ms, "aniso1")
                self.assertEqual(res["status"], "UNSAT", i)
                self.assertIn(res["stage"], ("square", "q_zero"), i)
        self.assertEqual(count, 8)

    def test_invertible_in(self):
        k = 2
        ident = 1 | (1 << 3)            # S[0][0] = S[1][1] = 1
        self.assertEqual(m.invertible_in([ident], k), (ident, True))
        self.assertEqual(m.invertible_in([1, 2], k), (None, True))      # row 1 always 0
        self.assertEqual(m.invertible_in([], k), (None, True))

    def test_instances(self):
        names = [x[0] for x in m.instances()]
        self.assertEqual(len(names), 30)
        self.assertIn("n4_o05_s10080", names)
        self.assertTrue(all(m94.check_tuple(Ms) for _, _, _, Ms in m.instances()))


if __name__ == "__main__":
    unittest.main()
