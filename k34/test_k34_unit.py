# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Controls for the slice search (slices.py): field axioms, group orders, orbit counts, the
28-point Kopparty-Saraf-Sudan set of F_4^3 through the leaf evaluator, and the complete search
in F_3^3, which must reproduce K(3, 3) = 13 (nothing below 13, and a 13-point set found).
Writes gate-out/k34/controls.json."""
import json
import math
import os
import sys
import time
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import slices, verify
except ImportError:  # pragma: no cover
    import slices
    import verify

OUT = os.environ.get("K34_OUT") or r"E:\MV2-Pursuit\work\20261128T050555Z-mathematics\gate-out\k34"

CONTROLS = {"made_with": "AI agents working in MV2's name; not checked by a human mathematician"}


def _save():
    try:
        os.makedirs(OUT, exist_ok=True)
        with open(os.path.join(OUT, "controls.json"), "w") as fh:
            json.dump(CONTROLS, fh, indent=1)
    except OSError:
        pass


class TestK34Unit(unittest.TestCase):
    def test_1_fields(self):
        for q in (3, 4, 5):
            add, mul, frob, gen = slices.field(q)
            E = range(q)
            for x in E:
                for y in E:
                    for z in E:
                        self.assertEqual(mul[x][add[y][z]], add[mul[x][y]][mul[x][z]])
                        self.assertEqual(mul[mul[x][y]][z], mul[x][mul[y][z]])
            for x in range(1, q):
                self.assertTrue(any(mul[x][y] == 1 for y in E))
            # gen generates the multiplicative group
            seen, v = set(), 1
            for _ in range(q - 1):
                seen.add(v)
                v = mul[v][gen]
            self.assertEqual(seen, set(range(1, q)))
            # Frobenius is a field automorphism
            for x in E:
                for y in E:
                    self.assertEqual(frob[add[x][y]], add[frob[x]][frob[y]])
                    self.assertEqual(frob[mul[x][y]], mul[frob[x]][frob[y]])
        # the independent checker's F_4 agrees with slices' F_4
        add, mul, _f, _g = slices.field(4)
        vadd, vmul = verify.ops(4)
        for x in range(4):
            for y in range(4):
                self.assertEqual(mul[x][y], vmul(x, y))
                self.assertEqual(add[x][y], vadd(x, y))

    def test_2_group_orders_and_orbits(self):
        g3, g4 = slices.Geo(3), slices.Geo(4)
        self.assertEqual(slices.group_order(g3), 9 * 8 * 6)          # |AGL(2,3)| = 432
        self.assertEqual(slices.group_order(g4), 16 * 15 * 12 * 2)   # |AGL(2,4)| * 2 = 5760
        counts = {}
        for geo, rmax in ((g3, 4), (g4, 6)):
            for r in range(1, rmax + 1):
                orbs = slices.orbits(geo, r)
                self.assertEqual(sum(sz for _rep, sz in orbs), math.comb(geo.Q, r))
                order = slices.group_order(geo)
                for rep, sz in orbs:
                    self.assertEqual(order % sz, 0)
                counts["q%d_r%d" % (geo.q, r)] = len(orbs)
        # small cases by hand: 1 orbit of points, 1 of pairs, 2 of triples (collinear or not)
        self.assertEqual(counts["q4_r1"], 1)
        self.assertEqual(counts["q4_r2"], 1)
        self.assertEqual(counts["q4_r3"], 2)
        self.assertEqual(counts["q3_r3"], 2)
        CONTROLS["orbit_counts"] = counts
        _save()

    def test_3_kss_28(self):
        K = verify.kss_set_q4()
        self.assertEqual(len(K), 28)
        self.assertTrue(verify.is_kakeya3(K, 4)[0])
        geo = slices.Geo(4)
        fr = geo.frob1
        fvals = [geo.idx(fr[x], fr[y]) for (x, y) in geo.xy]   # f(u) = (u1^2, u2^2)
        val, s = slices.leaf_value(geo, fvals)
        self.assertEqual(val, 28)
        pts = s.realize()
        self.assertEqual(len(pts), 28)
        self.assertTrue(verify.is_kakeya3(pts, 4)[0])
        CONTROLS["kss"] = {"size": 28, "leaf_value": val, "plane_min": verify.plane_min(K, 4)}
        _save()

    def test_4_f3_search_reproduces_13(self):
        t0 = time.time()
        rec12 = slices.full_search(3, 13)
        self.assertTrue(all(r["complete"] for r in rec12))
        self.assertEqual(sum(len(r["solutions"]) for r in rec12), 0)
        rec13 = slices.full_search(3, 14)
        sols = [s for r in rec13 for s in r["solutions"]]
        self.assertTrue(sols, "the F_3^3 search must find a 13-point set below T = 14")
        for s in sols:
            self.assertEqual(s["size"], 13)
            self.assertEqual(len(s["points"]), 13)
            self.assertTrue(verify.is_kakeya3(s["points"], 3)[0])
        mins = [r["leaf_min"] for r in rec13 if r["leaf_min"] is not None]
        self.assertEqual(min(mins), 13)
        CONTROLS["f3"] = {
            "T13": {"items": len(rec12), "nodes": sum(r["nodes"] for r in rec12),
                    "leaves": sum(r["leaves"] for r in rec12), "solutions": 0},
            "T14": {"items": len(rec13), "nodes": sum(r["nodes"] for r in rec13),
                    "leaves": sum(r["leaves"] for r in rec13), "leaf_min": min(mins),
                    "example": sols[0]["points"]},
            "seconds": round(time.time() - t0, 1)}
        _save()


if __name__ == "__main__":
    unittest.main()
