# SPDX-License-Identifier: Apache-2.0
"""Tests for h3scan.py and h3scan.c. MV2 of Munim, Inc.; made with AI agents. Apache-2.0."""
import os
import random
import shutil
import subprocess
import tempfile
import unittest

import h3scan

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = ((0, 0, 0), (0, 0, 0), (0, 0, 0))
CLASSICAL = [tuple(v * v % 3 for v in x) for x in h3scan.PTS]


def random_matrix(rng):
    return tuple(tuple(rng.randrange(3) for _ in range(3)) for _ in range(3))


class TestReference(unittest.TestCase):
    def test_gl3_order(self):
        self.assertEqual(len(h3scan.gl3()), 26 * 24 * 18)

    def test_inverse(self):
        rng = random.Random(3)
        G = h3scan.gl3()
        eye = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
        for _ in range(30):
            A = rng.choice(G)
            self.assertEqual(h3scan.mat_mul(A, h3scan.mat_inv(A)), eye)

    def test_classical_is_162(self):
        P = h3scan.quad_map(ZERO, 1, 3, 9)
        self.assertEqual(P, CLASSICAL)
        self.assertEqual(h3scan.compare_162(P), 0)
        self.assertAlmostEqual(h3scan.S_float(P), 162.0, places=9)
        self.assertAlmostEqual(h3scan.base_from_S(162.0), 3 * 2 ** (-2 / 3), places=12)

    def test_zero_and_identity(self):
        # P = 0: F_0 has one fibre of 27 points, F_1, F_2 are injective.
        self.assertEqual(h3scan.S_exact_power([(0, 0, 0)] * 27), 3 ** 81)
        # P = id: F_2 = 3x = 0 has one fibre of 27 points.
        self.assertEqual(h3scan.S_exact_power(list(h3scan.PTS)), 3 ** 81)

    def test_family_contains_classical(self):
        f = sum(3 ** (6 * u + m) * (u * u % 3) for u in range(3) for m in range(6))
        self.assertEqual(h3scan.s3_map(f), CLASSICAL)
        self.assertEqual(len(h3scan.CYC_MONOS), 16)
        c = 3 ** h3scan.CYC_MONOS.index((2, 0, 0))
        self.assertEqual(h3scan.cyc_map(c), CLASSICAL)

    def test_s3_equivariant(self):
        rng = random.Random(5)
        for _ in range(10):
            P = h3scan.s3_map(rng.randrange(3 ** 18))
            for perm in ((1, 0, 2), (0, 2, 1), (2, 0, 1)):
                for x in h3scan.PTS:
                    y = tuple(x[perm[i]] for i in range(3))
                    Px = P[h3scan.idx(x)]
                    self.assertEqual(P[h3scan.idx(y)], tuple(Px[perm[i]] for i in range(3)))

    def test_invariance(self):
        rng = random.Random(7)
        G = h3scan.gl3()
        for _ in range(15):
            L = random_matrix(rng)
            c = [rng.randrange(729) for _ in range(3)]
            P = h3scan.quad_map(L, *c)
            A = rng.choice(G)
            P2 = h3scan.conjugate_map(P, A, h3scan.mat_inv(A))
            lam = rng.randrange(3)
            P3 = [tuple((P[i][j] + lam * h3scan.PTS[i][j]) % 3 for j in range(3)) for i in range(27)]
            N = h3scan.S_exact_power(P)
            self.assertEqual(h3scan.S_exact_power(P2), N)
            self.assertEqual(h3scan.S_exact_power(P3), N)

    def test_reps_cover(self):
        reps = h3scan.conj_shift_reps()
        self.assertEqual(sum(n for _, n in reps), 3 ** 9)
        self.assertEqual(reps[0][0], ZERO)
        self.assertEqual(len({L for L, _ in reps}), len(reps))


@unittest.skipUnless(shutil.which("gcc"), "gcc not available")
class TestC(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp()
        cls.exe = os.path.join(cls.tmp, "h3scan_test.exe" if os.name == "nt" else "h3scan_test")
        subprocess.run(["gcc", "-O2", "-o", cls.exe, os.path.join(HERE, "h3scan.c"), "-lm"],
                       check=True)

    def run_c(self, *args):
        r = subprocess.run([self.exe] + [str(a) for a in args], capture_output=True, text=True,
                           check=True)
        return float(r.stdout.split()[-1])

    def test_classical(self):
        self.assertAlmostEqual(self.run_c("evalquad", *([0] * 9), 1, 3, 9), 162.0, places=9)

    def test_evalquad_matches(self):
        rng = random.Random(11)
        for _ in range(25):
            L = random_matrix(rng)
            c = [rng.randrange(729) for _ in range(3)]
            s_c = self.run_c("evalquad", *h3scan.flat(L), *c)
            self.assertAlmostEqual(s_c, h3scan.S_float(h3scan.quad_map(L, *c)), places=8)

    def test_evals3_matches(self):
        rng = random.Random(13)
        for _ in range(25):
            f = rng.randrange(3 ** 18)
            self.assertAlmostEqual(self.run_c("evals3", f), h3scan.S_float(h3scan.s3_map(f)), places=8)

    def test_evalcyc_matches(self):
        rng = random.Random(17)
        for _ in range(25):
            c = rng.randrange(3 ** 16)
            self.assertAlmostEqual(self.run_c("evalcyc", c), h3scan.S_float(h3scan.cyc_map(c)), places=8)


if __name__ == "__main__":
    unittest.main()
