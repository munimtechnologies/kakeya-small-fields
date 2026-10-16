# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for the robust cube bound (draft for kakeya-small-fields 1.7).

Claim (G abelian of order N, r >= 1). For d uniform on a set D of r-tuples and any base point
A(d), the points Y_t = A + t_1 d_1 + ... + t_r d_r satisfy

    sum over t in {0,1}^r of H(Y_t) >= ((2^r - 1) / r) log2 |D|.

So a set K containing a translate of the cube of every d in D has |K|^(r 2^r) >= |D|^(2^r - 1).

For a set K let cov_r(K) be the set of d in G^r whose cube has a translate inside K. Every D that
K serves lies in cov_r(K), so the set bound for all D at once is equivalent to
|K|^(r 2^r) >= |cov_r(K)|^(2^r - 1) for every subset K of G. `exhaustive` checks this for every
K, which covers every D. Non-abelian groups are reported, not asserted: the proof needs to peel
the generators in any order.

    python robust_cubes.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os
import random
from collections import Counter


def _group(name, elems, op, abelian):
    idx = {e: i for i, e in enumerate(elems)}
    mul = [[idx[op(x, y)] for y in elems] for x in elems]
    e = next(i for i in range(len(elems)) if all(mul[i][j] == j for j in range(len(elems))))
    return {"name": name, "n": len(elems), "mul": mul, "e": e, "abelian": abelian}


def abelian(*mods):
    elems = list(itertools.product(*[range(m) for m in mods]))
    return _group("x".join("Z%d" % m for m in mods), elems,
                  lambda x, y: tuple((a + b) % m for a, b, m in zip(x, y, mods)), True)


def symmetric3():
    elems = list(itertools.permutations(range(3)))
    return _group("S3", elems, lambda x, y: tuple(x[y[i]] for i in range(3)), False)


def dihedral4():
    elems = [(k, s) for s in range(2) for k in range(4)]
    return _group("D4", elems, lambda x, y: ((x[0] + (-1) ** x[1] * y[0]) % 4, (x[1] + y[1]) % 2), False)


def quaternion8():
    # units 0..3 = 1, i, j, k; (sign, unit)
    table = {(0, 0): (1, 0), (0, 1): (1, 1), (0, 2): (1, 2), (0, 3): (1, 3),
             (1, 0): (1, 1), (1, 1): (-1, 0), (1, 2): (1, 3), (1, 3): (-1, 2),
             (2, 0): (1, 2), (2, 1): (-1, 3), (2, 2): (-1, 0), (2, 3): (1, 1),
             (3, 0): (1, 3), (3, 1): (1, 2), (3, 2): (-1, 1), (3, 3): (-1, 0)}

    def op(x, y):
        s, u = table[(x[1], y[1])]
        return (x[0] * y[0] * s, u)
    elems = [(s, u) for s in (1, -1) for u in range(4)]
    return _group("Q8", elems, op, False)


def groups():
    gs = [abelian(m) for m in range(2, 13)]
    gs += [abelian(2, 2), abelian(2, 4), abelian(2, 2, 2), abelian(3, 3), abelian(2, 6)]
    gs += [symmetric3(), dihedral4(), quaternion8()]
    return gs


def is_group(G):
    n, mul, e = G["n"], G["mul"], G["e"]
    for x in range(n):
        if mul[e][x] != x or mul[x][e] != x or e not in mul[x]:
            return False
        for y in range(n):
            for z in range(n):
                if mul[mul[x][y]][z] != mul[x][mul[y][z]]:
                    return False
    return True


def word(G, d, t):
    w = G["e"]
    for di, ti in zip(d, t):
        if ti:
            w = G["mul"][w][di]
    return w


def translate_masks(G, d):
    r = len(d)
    ws = [word(G, d, t) for t in itertools.product((0, 1), repeat=r)]
    masks = set()
    for a in range(G["n"]):
        m = 0
        for w in ws:
            m |= 1 << G["mul"][a][w]
        masks.add(m)
    return sorted(masks)


def exhaustive(G, r):
    """Every K in G against cov_r(K). Returns the check and the tightest K."""
    tuples = list(itertools.product(range(G["n"]), repeat=r))
    masks = [translate_masks(G, d) for d in tuples]
    m = 2 ** r
    ok, worst = True, None
    for K in range(1, 1 << G["n"]):
        k = bin(K).count("1")
        c = sum(1 for ms in masks if any(x & K == x for x in ms))
        if k ** (r * m) < c ** (m - 1):
            ok = False
        if c > 1:
            # the exponent e with |K| = |cov|^e; the claim is e >= (1 - 2^-r)/r
            e = math.log(k) / math.log(c)
            if worst is None or e < worst[0] - 1e-12:
                worst = (e, k, c, K)
    return {"group": G["name"], "n": G["n"], "abelian": G["abelian"], "r": r, "holds": ok,
            "claimed_exponent": (1 - 2 ** -r) / r,
            "least_exponent": worst[0] if worst else None,
            "tight_K_size": worst[1] if worst else None,
            "tight_cov_size": worst[2] if worst else None,
            "tight_K": [i for i in range(G["n"]) if worst and worst[3] >> i & 1]}


def entropy(counter, total):
    return -sum(c / total * math.log2(c / total) for c in counter.values())


def entropy_sum(G, D, A, ws):
    total = len(D)
    s = 0.0
    for j in range(len(ws[0])):
        s += entropy(Counter(G["mul"][A[i]][ws[i][j]] for i in range(total)), total)
    return s


def descend(G, D, rng, sweeps=4):
    """Local search over base points A(d) for the least entropy sum."""
    r = len(D[0])
    ts = list(itertools.product((0, 1), repeat=r))
    ws = [[word(G, d, t) for t in ts] for d in D]
    A = [rng.randrange(G["n"]) for _ in D]
    best = entropy_sum(G, D, A, ws)
    for _ in range(sweeps):
        improved = False
        for i in range(len(D)):
            keep = A[i]
            for a in range(G["n"]):
                if a == keep:
                    continue
                A[i] = a
                v = entropy_sum(G, D, A, ws)
                if v < best - 1e-12:
                    best, keep, improved = v, a, True
            A[i] = keep
        if not improved:
            break
    return best


def entropy_trials(G, r, trials, rng):
    tuples = list(itertools.product(range(G["n"]), repeat=r))
    worst = None
    for _ in range(trials):
        p = rng.choice((0.1, 0.25, 0.5, 0.75, 1.0))
        D = [d for d in tuples if rng.random() < p] or [tuples[0]]
        v = descend(G, D, rng)
        bound = (2 ** r - 1) / r * math.log2(len(D))
        if worst is None or v - bound < worst[0]:
            worst = (v - bound, len(D), v, bound)
    return {"group": G["name"], "abelian": G["abelian"], "r": r, "trials": trials,
            "least_slack": worst[0], "size_D": worst[1], "sum": worst[2], "bound": worst[3]}


MAX_N = {1: 12, 2: 12, 3: 8, 4: 6}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--seed", type=int, default=20261015)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    out = {"exhaustive": [], "entropy": []}
    for r in (1, 2, 3, 4):
        for G in groups():
            if G["n"] <= MAX_N[r]:
                res = exhaustive(G, r)
                out["exhaustive"].append(res)
                print("exhaustive", res["group"], "r=%d" % r, "holds" if res["holds"] else "FAILS",
                      "least exponent %.4f (claim %.4f)" % (res["least_exponent"], res["claimed_exponent"]),
                      flush=True)
    for G in groups():
        for r in (1, 2, 3):
            if G["n"] ** r <= 64:
                res = entropy_trials(G, r, 20, rng)
                out["entropy"].append(res)
                print("entropy", res["group"], "r=%d" % r, "least slack %.6f" % res["least_slack"], flush=True)
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "robust_cubes.json"), "w") as f:
        json.dump(out, f, indent=1)
    bad = [x for x in out["exhaustive"] if x["abelian"] and not x["holds"]]
    bad += [x for x in out["entropy"] if x["abelian"] and x["least_slack"] < -1e-9]
    print("abelian failures:", len(bad))
    nonab = [(x["group"], x["r"]) for x in out["exhaustive"] if not x["abelian"] and not x["holds"]]
    print("non-abelian (group, r) where the set bound fails:", nonab)


if __name__ == "__main__":
    main()
