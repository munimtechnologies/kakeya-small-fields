# SPDX-License-Identifier: Apache-2.0
"""survey3.py - pre-registered search for note a164 (degree-2 blocks in dimension 3).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only. Usage: python survey3.py --out OUTDIR [--seconds N]

Pre-registered predictions (written before any run, 2026-11-17):
  S1  No degree-2 map of F_5^3 or F_7^3 found here has Lambda > 3(q-1) (C_q(3) holds).
  S2  Every map found with Lambda = 3(q-1) respects a nonzero proper subspace
      (Theorem 40 (a) case), and is a frame product.
  S3  Among uniformly random degree-2 maps the residual case of Theorem 40 never occurs.
  S4  A hill climb that maximises the number of cylinder directions |D| among maps with
      no invariant subspace reaches the residual case (|D| >= 2q+2, D in no plane) at
      q = 5; every residual map it finds has Lambda < 3(q-1).
A map that violates S1 would be a new record Kakeya block (a new upper bound for Kakeya
sets over F_q as n grows) and must be checked with exact arithmetic (score_int).
"""

import argparse
import json
import math
import os
import random
import time

import quad3 as q3


def build(q, c):
    Qc = [c[9 * i: 9 * i + 6] for i in range(3)]
    Lm = [c[9 * i + 6: 9 * i + 9] for i in range(3)]
    return q3.quad_map3(q, Qc, Lm)


def lam(q, c):
    return math.log2(q3.score_int(q, build(q, c))) / q ** 3


def summary(q, c):
    P = build(q, c)
    k = q3.classify(q, P)
    s = q3.score_int(q, P)
    return {"coeffs": c, "lambda": math.log2(s) / q ** 3,
            "exceeds": s > q3.bound_int(q), "equals": s == q3.bound_int(q),
            "inv": k["inv"], "D": len(k["D"]), "Z0": len(k["Z0"]),
            "residual": k["residual"]}


def climb(q, rng, f, start, steps):
    c, v = start, f(start)
    for _ in range(steps):
        d = list(c)
        for _ in range(rng.choice((1, 1, 2))):
            d[rng.randrange(27)] = rng.randrange(q)
        w = f(d)
        if w >= v:
            c, v = d, w
    return c, v


def d_score(q, c):
    P = build(q, c)
    k = q3.classify(q, P)
    if k["inv"]:
        return -1
    return len(k["D"]) + (100 if k["residual"] else 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="out")
    ap.add_argument("--seconds", type=float, default=3000)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    rng = random.Random(164)
    t0 = time.time()
    res = {"random": {}, "lambda_climb": {}, "d_climb": {}}
    for q, n in ((5, 400), (7, 60)):
        tally = {"inv": 0, "residual": 0, "max_lambda": 0.0, "exceeds": 0}
        for _ in range(n):
            c = [rng.randrange(q) for _ in range(27)]
            s = summary(q, c)
            tally["inv"] += s["inv"]
            tally["residual"] += s["residual"]
            tally["exceeds"] += s["exceeds"]
            tally["max_lambda"] = max(tally["max_lambda"], s["lambda"])
        res["random"][str(q)] = tally
    budget = a.seconds
    for q, steps, reps in ((5, 3000, 20), (7, 600, 4)):
        best = []
        for _ in range(reps):
            if time.time() - t0 > budget * 0.6:
                break
            c0 = [rng.randrange(q) for _ in range(27)]
            c, v = climb(q, rng, lambda c: lam(q, c), c0, steps)
            best.append(summary(q, c))
        best.sort(key=lambda s: -s["lambda"])
        res["lambda_climb"][str(q)] = best[:10]
    for q, steps, reps in ((5, 400, 10),):
        found = []
        for _ in range(reps):
            if time.time() - t0 > budget * 0.95:
                break
            c0 = [rng.randrange(q) for _ in range(27)]
            c, v = climb(q, rng, lambda c: d_score(q, c), c0, steps)
            found.append(summary(q, c))
        res["d_climb"][str(q)] = found
    res["seconds"] = time.time() - t0
    with open(os.path.join(a.out, "survey3.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "d_climb"}, indent=1)[:4000])


if __name__ == "__main__":
    main()
