# SPDX-License-Identifier: Apache-2.0
"""quad_census.py - exhaustive census of quadratic maps of F_q^2, q = 3, 5, 7 (note a162).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Needs numpy. Run by job kakeya-quad-v1:

    python quad_census.py selftest
    python quad_census.py census --q 5 --out-dir /out

A quadratic map is P = (P1, P2) with each Pi = a x1^2 + b x1 x2 + c x2^2 + d x1 + e x2
(constants change nothing). Lambda is invariant under P -> P + cI, so P1's x1-coefficient
d is fixed to 0: q^9 maps. For each map the score S = sum_t sum_F |F| log2 |F| is computed;
Lambda = S / q^2 and the threshold of C_q(2) is S = 2 (q - 1) q^2. Every map within 1e-6 of
the threshold (or above it) is re-checked exactly in integers with oval_rigidity.score_int.

Pre-registered in notes/a162.md (Q1, Q2):
  Q1. No quadratic map of F_q^2 (q = 3, 5, 7) has Lambda > 2 (q - 1).
  Q2. The quadratic maps with Lambda = 2 (q - 1) are exactly the frame products of
      nondegenerate quadratics: 72, 1,200 and 7,056 maps under this normalisation.
"""

import argparse
import itertools
import json
import math
import os
import sys
import time

import numpy as np

import oval_rigidity as orr


def monomials(q):
    pts = orr.points(q, 2)  # index i = x1 * q + x2
    M = np.array([[a * a % q, a * b % q, b * b % q, a, b] for a, b in pts], dtype=np.int64)
    return pts, M


def coeff_rows(q, fix_d):
    rows = [r for r in itertools.product(range(q), repeat=5) if not (fix_d and r[3] != 0)]
    return np.array(rows, dtype=np.int64)


def as_map(c1, c2, M, q):
    v1 = (M @ np.array(c1, dtype=np.int64)) % q
    v2 = (M @ np.array(c2, dtype=np.int64)) % q
    return [(int(a), int(b)) for a, b in zip(v1, v2)]


def census(q, out_dir, log_every=50):
    t0 = time.time()
    pts, M = monomials(q)
    N = q * q
    X1 = M[:, 3]
    X2 = M[:, 4]
    C1 = coeff_rows(q, True)
    C2 = coeff_rows(q, False)
    V1 = (C1 @ M.T) % q  # (n1, N)
    V2 = (C2 @ M.T) % q  # (n2, N)
    n1, n2 = len(C1), len(C2)
    # value tables -> coefficient index (monomials of degree < q in each variable are
    # independent functions for q >= 3, so this is a bijection)
    idx2 = {tuple(int(v) for v in row): j for j, row in enumerate(V2)}
    assert len(idx2) == n2
    Y2 = [((V2 + t * X2[None, :]) % q) for t in range(q)]
    offs = (np.arange(n2, dtype=np.int64) * N)[:, None]
    xlogx = np.array([c * math.log2(c) if c > 1 else 0.0 for c in range(N + 1)])
    target = 2 * (q - 1) * N
    near = []  # (i, j) with S >= target - 1e-6
    top = {}  # rounded S -> count
    for i in range(n1):
        S = np.zeros(n2)
        for t in range(q):
            y1 = (V1[i] + t * X1) % q
            key = (y1[None, :] * q + Y2[t]) + offs
            cnt = np.bincount(key.ravel(), minlength=n2 * N).reshape(n2, N)
            S += xlogx[cnt].sum(axis=1)
        hit = np.nonzero(S >= target - 1e-6)[0]
        for j in hit:
            near.append((i, int(j)))
        # full histogram of S (rounded to 1e-6); only the largest values are reported
        vals, counts = np.unique(np.round(S, 6), return_counts=True)
        for v, c in zip(vals.tolist(), counts.tolist()):
            top[v] = top.get(v, 0) + c
        if log_every and i % log_every == 0:
            print("q", q, "row", i, "of", n1, "near", len(near), "elapsed",
                  round(time.time() - t0, 1), flush=True)

    # exact re-check of every near-threshold map
    exact_max, exceed = [], []
    for i, j in near:
        P = as_map(C1[i], C2[j], M, q)
        s = orr.score_int(P, q, 2)
        thr = 2 ** (2 * (q - 1) * N)
        if s > thr:
            exceed.append((C1[i].tolist(), C2[j].tolist()))
        elif s == thr:
            exact_max.append((i, j))

    # the frame products, normalised (P1 has no x1 term), as (i, j) index pairs
    fp = orr.frame_products(q, sorted(orr.quadratics_fixed0(q)))
    idx1 = {tuple(int(v) for v in row): i for i, row in enumerate(V1)}
    fp_pairs = set()
    for P in fp:
        r1 = tuple(p[0] for p in P)
        r2 = tuple(p[1] for p in P)
        if r1 in idx1:
            fp_pairs.add((idx1[r1], idx2[r2]))
    max_set = set(exact_max)
    second = sorted(v for v in top if v < target - 1e-6)
    res = {
        "q": q,
        "maps": n1 * n2,
        "normalisation": "constants dropped; P1 has no x1 term (P -> P + cI)",
        "threshold_S": target,
        "max_S_float": max(top) if top else None,
        "distinct_S_values": len(top),
        "largest_S_values_with_counts": [[v, top[v]] for v in sorted(top, reverse=True)[:12]],
        "second_largest_S": second[-1] if second else None,
        "second_largest_Lambda": (second[-1] / N) if second else None,
        "n_exact_max": len(max_set),
        "n_exceed": len(exceed),
        "exceed_examples": exceed[:20],
        "n_frame_products_normalised": len(fp_pairs),
        "max_set_equals_frame_products": max_set == fp_pairs,
        "max_not_frame": [[C1[i].tolist(), C2[j].tolist()] for i, j in sorted(max_set - fp_pairs)][:50],
        "frame_not_max": [[C1[i].tolist(), C2[j].tolist()] for i, j in sorted(fp_pairs - max_set)][:50],
        "seconds": round(time.time() - t0, 1),
    }
    expect = {3: 72, 5: 1200, 7: 7056}[q]
    res["grade"] = {
        "Q1_no_exceed": len(exceed) == 0,
        "Q2_max_set_is_frame_products": max_set == fp_pairs and len(fp_pairs) == expect,
    }
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "quad_census_q%d.json" % q), "w") as fh:
        json.dump(res, fh, indent=1)
    print("SUMMARY quad_census q", q, json.dumps({k: res[k] for k in (
        "maps", "n_exact_max", "n_exceed", "n_frame_products_normalised",
        "max_set_equals_frame_products", "second_largest_Lambda", "grade", "seconds")}))
    return res


def selftest():
    import random
    rng = random.Random(7)
    for q in (3, 5):
        pts, M = monomials(q)
        N = q * q
        xlogx = np.array([c * math.log2(c) if c > 1 else 0.0 for c in range(N + 1)])
        for _ in range(30):
            c1 = [rng.randrange(q) for _ in range(5)]
            c2 = [rng.randrange(q) for _ in range(5)]
            P = as_map(c1, c2, M, q)
            v1 = np.array([p[0] for p in P], dtype=np.int64)
            v2 = np.array([p[1] for p in P], dtype=np.int64)
            S = 0.0
            for t in range(q):
                key = ((v1 + t * M[:, 3]) % q) * q + (v2 + t * M[:, 4]) % q
                S += xlogx[np.bincount(key, minlength=N)].sum()
            assert abs(S - q ** 2 * orr.loss(P, q, 2)) < 1e-7, (q, c1, c2)
        # the coordinatewise square map is a frame product and attains the threshold
        P = as_map([1, 0, 0, 0, 0], [0, 0, 1, 0, 0], M, q)
        assert orr.is_max(P, q, 2)
    small = census(3, "/tmp/quad_selftest", log_every=0)
    assert small["grade"]["Q1_no_exceed"], small
    print("SELFTEST ok; q = 3 control:", small["grade"], "n_exact_max", small["n_exact_max"])


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("selftest")
    c = sub.add_parser("census")
    c.add_argument("--q", type=int, required=True)
    c.add_argument("--out-dir", default="out")
    a = ap.parse_args()
    if a.cmd == "selftest":
        selftest()
    else:
        if a.q not in (3, 5, 7):
            sys.exit("q must be 3, 5 or 7")
        census(a.q, a.out_dir)


if __name__ == "__main__":
    main()
