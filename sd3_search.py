# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Search for characteristic-3 sums-differences configurations beating Ruzsa (note a181).

Conjecture R3 (notes/a181.md): every configuration (mu, P) in every F_3^N has
H(D) <= R0 * avg_t H(P(D) + tD), R0 = log 27 / log(27/4). It would give the exact
Kakeya growth base (27/4)^(1/3) = 1.88988 for F_3.

For a fixed map P the objective F(mu) = H(mu) - (R0/3) sum_t H(law of Y_t) is
concave + convex in mu, so the concave-convex procedure
    mu_new(d)  proportional to  prod_t P(Y_t = Y_t(d))^(R0/3)
never decreases F (cccp below). F > 0 means H(D) / avg_t H(Y_t) > R0, i.e. a
counterexample to Conjecture R3 (and, by the rotated triple product, to the max form).

Pre-registered reading (a181): a configuration with F > 1e-9 found here is re-evaluated
from its printed weights; if it still has R_avg > R0 + 1e-9 it refutes Conjecture R3 in
that dimension. Otherwise the run is evidence only: the best R_avg over the maps tried.

Standard library only; self-contained.
"""

import argparse
import itertools
import json
import math
import random
import time

R0 = math.log(27.0) / math.log(27.0 / 4.0)


def f3_vectors(k):
    return list(itertools.product(range(3), repeat=k))


def slice_value(base, d, t):
    return tuple((b + t * x) % 3 for b, x in zip(base, d))


def entropy(vals):
    tot = float(sum(vals))
    return -sum((v / tot) * math.log(v / tot) for v in vals if v > 0)


def evaluate(P, mu, R=R0):
    """Return (F, H(D), [H(Y_t)], R_avg) for weights mu (dict d -> float)."""
    laws = [dict(), dict(), dict()]
    for d, w in mu.items():
        if w <= 0:
            continue
        for t in range(3):
            y = slice_value(P[d], d, t)
            laws[t][y] = laws[t].get(y, 0.0) + w
    hd = entropy(list(mu.values()))
    hs = [entropy(list(law.values())) for law in laws]
    avg = sum(hs) / 3.0
    r_avg = hd / avg if avg > 0 else float("inf")
    return hd - R * avg, hd, hs, r_avg


def cccp_step(P, mu, R=R0):
    laws = [dict(), dict(), dict()]
    for d, w in mu.items():
        if w <= 0:
            continue
        for t in range(3):
            y = slice_value(P[d], d, t)
            laws[t][y] = laws[t].get(y, 0.0) + w
    new = {}
    for d, w in mu.items():
        if w <= 0:
            new[d] = 0.0
            continue
        lp = 0.0
        for t in range(3):
            lp += math.log(laws[t][slice_value(P[d], d, t)])
        new[d] = math.exp((R / 3.0) * lp)
    z = sum(new.values())
    return {d: v / z for d, v in new.items()}


def cccp(P, mu0, iters=300, R=R0):
    mu = dict(mu0)
    for _ in range(iters):
        mu = cccp_step(P, mu, R)
    return mu


def random_map(big_n, rng):
    pts = f3_vectors(big_n)
    return {d: rng.choice(pts) for d in pts}


def quadratic_map(big_n, rng):
    """P(d)_i = d^T A_i d + b_i . d with random coefficients (frame maps are of this kind)."""
    dirs = f3_vectors(big_n)
    coef = [([[rng.randrange(3) for _ in range(big_n)] for _ in range(big_n)],
             [rng.randrange(3) for _ in range(big_n)]) for _ in range(big_n)]
    out = {}
    for d in dirs:
        val = []
        for a, b in coef:
            s = sum(a[i][j] * d[i] * d[j] for i in range(big_n) for j in range(big_n))
            s += sum(b[i] * d[i] for i in range(big_n))
            val.append(s % 3)
        out[d] = tuple(val)
    return out


def perturbed_ruzsa(big_n, rng, k):
    dirs = f3_vectors(big_n)
    out = {d: tuple((x * x) % 3 for x in d) for d in dirs}
    pts = f3_vectors(big_n)
    for d in rng.sample(dirs, k):
        out[d] = rng.choice(pts)
    return out


def starts(dirs, rng, count):
    out = [{d: 1.0 / len(dirs) for d in dirs}]
    for _ in range(count - 1):
        raw = {d: rng.random() ** 3 + 1e-6 for d in dirs}
        z = sum(raw.values())
        out.append({d: v / z for d, v in raw.items()})
    return out


def search(big_n, minutes, seed, iters=300, restarts=3, keep=20):
    rng = random.Random(seed)
    dirs = f3_vectors(big_n)
    t_end = time.time() + 60.0 * minutes
    best = []
    best_ratio = []          # nondegenerate (H(D) > 0.3 nats), ranked by R_avg
    tried = 0
    kinds = {"random": 0, "quadratic": 0, "perturbed": 0}
    while time.time() < t_end:
        u = rng.random()
        if u < 0.4:
            P, kind = random_map(big_n, rng), "random"
        elif u < 0.7:
            P, kind = quadratic_map(big_n, rng), "quadratic"
        else:
            P, kind = perturbed_ruzsa(big_n, rng, rng.randint(1, max(1, len(dirs) // 3))), "perturbed"
        kinds[kind] += 1
        tried += 1
        for mu0 in starts(dirs, rng, restarts):
            mu = cccp(P, mu0, iters)
            F, hd, hs, r_avg = evaluate(P, mu)
            rec = {"F": F, "R_avg": r_avg, "H_D": hd, "H_slices": hs, "kind": kind,
                   "P": {"".join(map(str, d)): "".join(map(str, P[d])) for d in dirs},
                   "mu": {"".join(map(str, d)): mu[d] for d in dirs if mu[d] > 1e-12}}
            best.append(rec)
            best.sort(key=lambda r: -r["F"])
            del best[keep:]
            if hd > 0.3:
                best_ratio.append(rec)
                best_ratio.sort(key=lambda r: -r["R_avg"])
                del best_ratio[keep:]
    return {"N": big_n, "seed": seed, "minutes": minutes, "iters": iters,
            "restarts": restarts, "maps_tried": tried, "kinds": kinds, "R0": R0,
            "max_F": best[0]["F"] if best else None,
            "max_R_avg_nondegenerate": best_ratio[0]["R_avg"] if best_ratio else None,
            "counterexample": bool(best and best[0]["F"] > 1e-9),
            "best": best, "best_ratio": best_ratio}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=2)
    ap.add_argument("--minutes", type=float, default=10.0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--iters", type=int, default=300)
    ap.add_argument("--restarts", type=int, default=3)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    res = search(a.N, a.minutes, a.seed, a.iters, a.restarts)
    with open(a.out, "w") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps({k: res[k] for k in ("N", "maps_tried", "kinds", "max_F",
                                          "max_R_avg_nondegenerate", "counterexample")}))


if __name__ == "__main__":
    main()
