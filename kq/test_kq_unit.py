# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Controls for kq.py: field arithmetic, geometry counts, the independent checker, and known
exact values.  Planar values are Blokhuis-Mazzocca (K(2, q) = q(q+1)/2 for even q and
q(q+1)/2 + (q-1)/2 for odd q); K(3, 3) = 13 is MV2's earlier exhaustive result
(munimtechnologies/kakeya-conjecture v1.1.0).  The local search must reach the planar values,
and the integer programs (when scipy is importable) must return exactly the known values in
both formulations.  The checker must reject sets with one point removed."""
import json
import os
import sys
import time
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import kq, check
except ImportError:  # pragma: no cover
    import kq
    import check

OUT = os.environ.get("KQ_OUT") or r"E:\MV2-Pursuit\work\20261128T013852Z-mathematics\gate-out\kq"
KNOWN = {(2, 2): 3, (2, 3): 7, (2, 4): 10, (2, 5): 17, (3, 2): 5, (3, 3): 13}
LOG = {}


def note(key, value):
    LOG[key] = value
    try:
        os.makedirs(OUT, exist_ok=True)
        with open(os.path.join(OUT, "controls.json"), "w") as fh:
            json.dump(LOG, fh, indent=1)
    except OSError:
        pass


class TestKQ(unittest.TestCase):
    def test_fields(self):
        for q in (2, 3, 4, 5):
            self.assertTrue(check.field_axioms_ok(q))
            F = kq.Field(q)
            add, mul = check.ops(q)
            for x in range(q):
                for y in range(q):
                    self.assertEqual(F.add[x][y], add(x, y))
                    self.assertEqual(F.mul[x][y], mul(x, y))

    def test_geometry(self):
        for n, q in ((2, 3), (2, 4), (3, 4), (3, 5), (4, 4)):
            pts, dirs, lines = kq.geometry(n, q)
            self.assertEqual(len(pts), q ** n)
            self.assertEqual(len(dirs), (q ** n - 1) // (q - 1))
            for cls in lines:
                self.assertEqual(len(cls), q ** (n - 1))
                self.assertEqual(sorted(p for l in cls for p in l), list(range(q ** n)))

    def test_checker_rejects(self):
        pts, _d, _l = kq.geometry(3, 4)
        full = [list(p) for p in pts]
        self.assertTrue(check.is_kakeya(full, 3, 4)[0])
        # the 28-point construction {(t, bt + b^2, ct + c^2)} of MV2's v1.1.0, with t = 0 full
        F = kq.Field(4)
        S = set()
        for t in range(4):
            for b in range(4):
                for c in range(4):
                    S.add((t, F.add[F.mul[b][t]][F.mul[b][b]], F.add[F.mul[c][t]][F.mul[c][c]]))
        for y in range(4):
            for z in range(4):
                S.add((0, y, z))
        self.assertEqual(len(S), 28)
        self.assertTrue(check.is_kakeya(sorted(S), 3, 4)[0])
        note("construction_28", True)
        plane = [(0, y, z) for y in range(4) for z in range(4)]
        self.assertFalse(check.is_kakeya(plane, 3, 4)[0])
        # every line of one direction (1, 0, 0) removed from the full space by deleting a
        # transversal plane x = 2: no line in direction (1, 0, 0) can survive
        cut = [p for p in full if p[0] != 2]
        ok, why = check.is_kakeya(cut, 3, 4)
        self.assertFalse(ok)
        self.assertIn("(1, 0, 0)", why.replace("[", "(").replace("]", ")"))

    def test_local_search_planes(self):
        for (n, q), k in sorted(KNOWN.items()):
            if n != 2:
                continue
            best, sel, _st = kq.local_search(n, q, 4.0, seed=1)
            pts, _d, _l = kq.geometry(n, q)
            self.assertTrue(check.is_kakeya([pts[p] for p in sel], n, q)[0])
            self.assertEqual(len(sel), best)
            self.assertEqual(best, k, (n, q))
            note("ls_%d_%d" % (n, q), best)

    def test_milp_known(self):
        ok, detail = kq.have_scipy()
        note("engine", detail)
        if not ok:
            self.skipTest(detail)
        for (n, q), k in sorted(KNOWN.items()):
            for form in ("A", "B"):
                t0 = time.time()
                r = kq.solve_milp(n, q, form, 60)
                self.assertEqual(r["status"], 0, r)
                self.assertEqual(r["best"], k, (n, q, form))
                self.assertTrue(check.is_kakeya(r["set"], n, q)[0])
                note("milp_%d_%d_%s" % (n, q, form), [r["best"], round(time.time() - t0, 1)])
            if n >= 3:
                vals = []
                for form in ("C1", "C2"):
                    r = kq.solve_milp(n, q, form, 60)
                    self.assertIn(r["status"], (0, 2), r)   # 2 = infeasible is allowed
                    if r["status"] == 0:
                        self.assertTrue(check.is_kakeya(r["set"], n, q)[0])
                        vals.append(r["best"])
                self.assertEqual(min(vals), k, (n, q, "C"))
                note("milp_%d_%d_C" % (n, q), vals)


if __name__ == "__main__":
    unittest.main()
