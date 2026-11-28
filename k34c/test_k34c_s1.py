# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""k34c phase 1, session s1: controls, then the first session of the resumable listing of every
28-point Kakeya set of F_4^3 (progress in gate-out/k34c, committed later behind a checker).

Controls: the enumeration over F_3 (threshold 14, r' <= 4) finds 13-point sets, never fewer, and
every set it lists is a Kakeya set of exactly 13 points by k34b's own checker; the 28-point
Kopparty-Saraf-Sudan set round-trips through the mask encoding and passes the checker; the
counting lemma behind r' <= 6 holds (84 planes, 21 through a point, 5 through a line)."""
import json
import os
import sys
import time
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import classify  # noqa: E402
import indep  # noqa: E402

OUT = os.environ.get("K34C_OUT") or r"E:\MV2-Pursuit\work\20261128T130947Z-mathematics\gate-out\k34c"
LABEL = "c-run-1"
BUDGET = 420.0
T_START = time.time()


def planes_q4():
    """All 84 planes of AG(3, 4) as 64-bit masks, from pairs of independent directions."""
    A, M, _N, _F = indep.field_tables(4)
    pts = [(x, y, z) for x in range(4) for y in range(4) for z in range(4)]
    vecs = [v for v in pts if v != (0, 0, 0)]
    subs = set()
    for u in vecs:
        for v in vecs:
            span = frozenset((A[M[s][u[0]]][M[t][v[0]]], A[M[s][u[1]]][M[t][v[1]]],
                              A[M[s][u[2]]][M[t][v[2]]]) for s in range(4) for t in range(4))
            if len(span) == 16:
                subs.add(span)
    out = set()
    for span in subs:
        for p in pts:
            m = 0
            for w in span:
                m |= 1 << (16 * A[p[2]][w[2]] + 4 * A[p[0]][w[0]] + A[p[1]][w[1]])
            out.add(m)
    return sorted(out)


class TestK34cS1(unittest.TestCase):
    def test_a_controls(self):
        res = {"made_with": classify.MADE_WITH}
        kss = indep.kss_q4()
        m = classify.points_mask(kss, 4)
        self.assertEqual(bin(m).count("1"), 28)
        self.assertEqual(sorted(classify.mask_points(m, 4)), sorted([list(p) for p in kss]))
        self.assertTrue(indep.kakeya_ok(classify.mask_points(m, 4), 4))
        PL = planes_q4()
        self.assertEqual(len(PL), 84)
        through_pt = sum(1 for pl in PL if pl & 1)
        self.assertEqual(through_pt, 21)
        through_line = sum(1 for pl in PL if (pl & 1) and (pl & 2))
        self.assertEqual(through_line, 5)
        self.assertNotEqual(84 * 7 * 6, 28 * 27 * 5)
        kss_planes = sorted(bin(pl & m).count("1") for pl in PL)
        res["kss_plane_sizes"] = {str(k): kss_planes.count(k) for k in sorted(set(kss_planes))}
        self.assertEqual(sum(kss_planes), 28 * 21)
        # F_3 control
        sets3, recs3 = classify.enumerate_all(3, 14, 4)
        self.assertTrue(sets3)
        mins = [x["leaf_min"] for x in recs3 if x["leaf_min"] is not None]
        self.assertEqual(min(mins), 13)
        for s in sets3:
            self.assertEqual(bin(s).count("1"), 13)
            self.assertTrue(indep.kakeya_ok(classify.mask_points(s, 3), 3))
        res["f3"] = {"T": 14, "rmax": 4, "items": len(recs3), "distinct_13_point_sets_listed": len(sets3),
                     "nodes": sum(x["nodes"] for x in recs3)}
        os.makedirs(OUT, exist_ok=True)
        with open(os.path.join(OUT, "controls-c.json"), "w") as fh:
            json.dump(res, fh, indent=1)

    def test_b_session(self):
        budget = max(30.0, BUDGET - (time.time() - T_START))
        st = classify.queue(OUT, budget, LABEL, item_cap=300.0)
        self.assertEqual((st["q"], st["T"], st["rmax"]), (4, 29, 6))
        self.assertEqual(st["group_order"], 5760)
        if st["leaf_min"] is not None:
            self.assertGreaterEqual(st["leaf_min"], 28)
        sets = classify.load_sets(OUT)
        self.assertEqual(len(sets), st["n_sets"])
        for s in sets:
            self.assertEqual(bin(s).count("1"), 28)
        for s in sorted(sets)[:40]:
            self.assertTrue(indep.kakeya_ok(classify.mask_points(s, 4), 4))


if __name__ == "__main__":
    unittest.main()
