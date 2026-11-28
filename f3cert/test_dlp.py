# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Controls for f3cert/dlp.py (pure-stdlib dual simplex) and an offline end-to-end run of
f3cert/gaterun.py on Tomar's page.

1. Random small LPs against exact brute-force vertex enumeration (Fractions): the simplex
   value matches, and the exact bound recomputed from its duals never exceeds the true optimum
   (weak duality, checked exactly) and is within 1e-6 of it.
2. The same LPs started from two rows only (cutting planes) reach the same optimum.
3. A solver stopped at any time still returns a valid (smaller) exact bound.
4. A textbook LP whose exact optimum 7/5 is recovered exactly.
5. gaterun on Tomar's page with a one-row certificate (h(x)+h(y) >= h(x,y)): the control
   certifies 1, the symmetric LP certifies exactly 1/2 (= the certificate's own value), and
   every symmetric bound, including all pair and cross rows, stays between 1/2 and the value
   0.579380 of the KLSS construction, which no sound bound may exceed."""
import itertools
import os
import random
import shutil
import sys
import tempfile
import time
import unittest
from fractions import Fraction

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import dlp
    from . import f3cert as F
    from . import gaterun as G
except ImportError:  # pragma: no cover
    import dlp
    import f3cert as F
    import gaterun as G


def solve_exact(A, b):
    n = len(A)
    M = [row[:] + [bb] for row, bb in zip(A, b)]
    for c in range(n):
        piv = None
        for r in range(c, n):
            if M[r][c] != 0:
                piv = r
                break
        if piv is None:
            return None
        M[c], M[piv] = M[piv], M[c]
        p = M[c][c]
        M[c] = [v / p for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return [M[r][n] for r in range(n)]


def brute(cost, rows, n):
    cons = [([Fraction(co.get(i, 0)) for i in range(n)], Fraction(c)) for co, c in rows]
    cons += [([Fraction(1 if k == i else 0) for k in range(n)], Fraction(0)) for i in range(n)]
    best = None
    for combo in itertools.combinations(range(len(cons)), n):
        sol = solve_exact([cons[i][0] for i in combo], [-cons[i][1] for i in combo])
        if sol is None:
            continue
        if all(sum(a * s for a, s in zip(co, sol)) + c >= 0 for co, c in cons):
            v = sum(Fraction(cost.get(i, 0)) * sol[i] for i in range(n))
            if best is None or v < best:
                best = v
    return best


def instance(rng, n, m, box):
    h0 = [rng.randint(0, box - 4) for _ in range(n)]
    rows = []
    for _ in range(m):
        a = {i: rng.randint(-3, 3) for i in range(n)}
        a = {i: v for i, v in a.items() if v}
        if not a:
            continue
        c = -sum(v * h0[i] for i, v in a.items()) + rng.randint(0, 3)
        rows.append((a, c))
    for i in range(n):
        rows.append(({i: -1}, box))
    cost = {i: rng.randint(0, 4) for i in range(n)}
    return cost, rows


class TestDualSimplex(unittest.TestCase):
    def test_random_vs_brute_force(self):
        rng = random.Random(11)
        box = 10
        for trial in range(120):
            n = rng.choice((2, 3))
            cost, rows = instance(rng, n, rng.randint(2, 6), box)
            opt = brute(cost, rows, n)
            self.assertIsNotNone(opt)
            for init in (list(range(len(rows))), [0, 1]):
                res = dlp.solve(cost, rows, init, time.time() + 30)
                self.assertEqual(res["status"], "optimal-all", msg=str((trial, cost, rows)))
                self.assertAlmostEqual(res["z"], float(opt), places=7)
                val, _u, _b = dlp.exact_bound(cost, rows, res["duals"], lambda k: (0, box))
                self.assertLessEqual(val, opt)
                self.assertGreaterEqual(val, opt - Fraction(1, 10 ** 6))

    def test_stopped_solver_is_still_sound(self):
        rng = random.Random(12)
        box = 10
        for _ in range(60):
            n = 3
            cost, rows = instance(rng, n, 6, box)
            opt = brute(cost, rows, n)
            ds = dlp.DualSimplex(cost)
            for idx, (co, c) in enumerate(rows):
                ds.add_row(idx, co, c)
            ds.run(time.time() + 30, max_pivots=rng.randint(0, 2))
            val, _u, _b = dlp.exact_bound(cost, rows, ds.duals(), lambda k: (0, box))
            self.assertLessEqual(val, opt)
            res = dlp.solve(cost, rows, [0], time.time() - 1.0)
            self.assertEqual(res["status"], "time")
            val, _u, _b = dlp.exact_bound(cost, rows, res["duals"], lambda k: (0, box))
            self.assertLessEqual(val, opt)

    def test_textbook_exact(self):
        cost = {"x": 1, "y": 1}
        rows = [({"x": 1, "y": 2}, -2), ({"x": 3, "y": 1}, -3)]
        res = dlp.solve(cost, rows, [0, 1], time.time() + 10)
        self.assertEqual(res["status"], "optimal-all")
        val, used, _b = dlp.exact_bound(cost, rows, res["duals"], lambda k: (0, 100))
        self.assertEqual(val, Fraction(7, 5))
        self.assertEqual(sorted(q for _i, q in used), [Fraction(1, 5), Fraction(2, 5)])

    def test_equality_as_two_rows(self):
        cost = {"x": 1, "y": 1}
        rows = [({"x": 1, "y": -1}, 0), ({"x": -1, "y": 1}, 0), ({"x": 1, "y": 3}, -4)]
        res = dlp.solve(cost, rows, [2], time.time() + 10)
        self.assertEqual(res["status"], "optimal-all")
        self.assertAlmostEqual(res["z"], 2.0, places=9)
        val, _u, _b = dlp.exact_bound(cost, rows, res["duals"], lambda k: (0, 100))
        self.assertEqual(val, Fraction(2))

    def test_negative_cost_refused(self):
        with self.assertRaises(ValueError):
            dlp.DualSimplex({"x": -1})


ONE_ROW_CERT = {"steps": F.TOMAR_PAGE, "eqlaw": [],
                "rows": [{"type": "sub", "K": [], "i": [0, [1, 0]], "j": [0, [0, 1]],
                          "mult": "1"}],
                "lambda": {"1,0": "1", "0,1": "1", "1,1": "0"}, "claimed_C": "2"}


class TestGateRunOffline(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="f3cert-")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_one_row_certificate_on_tomar_page(self):
        rep = G.run("five", ONE_ROW_CERT, os.path.join(self.tmp, "five"), budget=120,
                    cfg_name="one-row")
        self.assertTrue(rep["complete"])
        self.assertEqual(rep["replay_nonzero_classes"], 0)
        v = rep["variants"]
        eps = Fraction(1, 10 ** 9)
        ctl = Fraction(v["cert-lambda-plain"]["lb_exact"])
        self.assertTrue(1 - eps <= ctl <= 1, msg=str(ctl))
        sp = Fraction(v["cert-sym-plain"]["lb_exact"])
        self.assertTrue(Fraction(1, 2) - eps <= sp <= Fraction(1, 2), msg=str(sp))
        for name, info in v.items():
            if info.get("symmetric"):
                lb = Fraction(info["lb_exact"])
                self.assertGreaterEqual(lb, Fraction(1, 2) - Fraction(1, 10 ** 9), msg=name)
                self.assertLessEqual(float(lb), F.KLSS_W + 1e-9, msg=name)
        self.assertEqual(rep["verdict"], "NO_GAIN")
        for f in ("results.json", "SUMMARY.md", "best_cert.json", "control_cert.json"):
            self.assertTrue(os.path.isfile(os.path.join(self.tmp, "five", f)), msg=f)

    def test_pairs_on_tomar_page_stay_below_klss(self):
        rep = G.run("aug", ONE_ROW_CERT, os.path.join(self.tmp, "aug"), budget=150,
                    cfg_name="one-row")
        self.assertTrue(rep["complete"])
        self.assertGreater(rep["pool_sizes"]["pairs"], 50)
        for name, info in rep["variants"].items():
            self.assertIn("lb_exact", info, msg=name)
            lb = Fraction(info["lb_exact"])
            self.assertGreaterEqual(lb, Fraction(1, 2) - Fraction(1, 10 ** 9), msg=name)
            self.assertLessEqual(float(lb), F.KLSS_W + 1e-9, msg=name)
        self.assertNotIn("UNSOUND", rep["verdict"])


if __name__ == "__main__":
    unittest.main()
