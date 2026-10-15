"""Searches for maps P : F_q^k -> F_q^k with a large fibre score (README section 8).

S(P) = sum over t in F_q and over the fibres of x -> P(x) + t x (x in F_q^k) of s log2 s, and
h(P) = k log2 q - S(P) / q^(k+1). A map with S(P) > k (q - 1) q^k would give a Kakeya bound below
q * 2^(-(q-1)/q) (Theorem 2); the lower bound q^2/(2q - 1) caps S(P) at score_ceiling(q, k).

  python search_h2.py exhaustive --q 3 --k 2 --out-dir OUT    every P with P(0) = 0 (needs numpy)
  python search_h2.py anneal --plan 3:2:600 4:2:600 --out-dir OUT    q:k:seconds, pure Python

Fixing P(0) = 0 loses nothing: P -> P + c does not change S. By MV2 of Munim, Inc., 2026-10-14.
Researched and written with AI agents working in MV2's name. Code Apache-2.0.
"""
import argparse
import json
import math
import os
import random
import time
from itertools import product

from kakeya_entropy import (Field, exponent, improvement_threshold, score_ceiling, slice_counts,
                            vectors, witness_score)


def tables(q, k):
    """Vectors of F_q^k as the integers 0..q^k - 1 (in the order of vectors(q, k)), with the
    addition table add[u][v] and the table tx[t][v] of t * v."""
    F = Field(q)
    vs = vectors(q, k)
    index = {v: i for i, v in enumerate(vs)}
    add = [[index[tuple(F.add[a][b] for a, b in zip(u, v))] for v in vs] for u in vs]
    tx = [[index[tuple(F.mul[t][a] for a in v)] for v in vs] for t in range(q)]
    return F, vs, index, add, tx


def score_codes(q, k, add, tx, codes):
    """S(P) for P given as a list of vector codes (codes[x] = code of P(x))."""
    n = q ** k
    total = 0.0
    for t in range(q):
        counts = [0] * n
        for x in range(n):
            counts[add[codes[x]][tx[t][x]]] += 1
        total += sum(c * math.log2(c) for c in counts if c > 1)
    return total


def as_dict(vs, codes):
    return {vs[x]: vs[c] for x, c in enumerate(codes)}


def describe(F, q, k, vs, codes):
    P = as_dict(vs, codes)
    return {"map": [[list(vs[x]), list(vs[c])] for x, c in enumerate(codes)],
            "score_rechecked": witness_score(F, k, P),
            "fibres_by_slice": [slice_counts(F, k, P, t) for t in range(q)]}


def exhaustive(q, k, inner=4, keep=20):
    """Every map with P(0) = 0; the last `inner` values are enumerated with numpy."""
    import numpy as np
    F, vs, index, add, tx = tables(q, k)
    n = q ** k
    A = np.array(add, dtype=np.int64)
    TX = np.array(tx, dtype=np.int64)
    cl = np.array([c * math.log2(c) if c > 1 else 0.0 for c in range(n + 1)])
    free = list(range(1, n))
    inner = min(inner, len(free))
    inner_pos, outer_pos = free[len(free) - inner:], free[:len(free) - inner]
    grid = np.array(list(product(range(n), repeat=inner)), dtype=np.int64).reshape(-1, inner)
    rows = grid.shape[0]
    base = []
    for t in range(q):
        oh = np.zeros((rows, n), dtype=np.int64)
        for j, pos in enumerate(inner_pos):
            oh[np.arange(rows), A[grid[:, j], TX[t, pos]]] += 1
        oh[:, add[0][tx[t][0]]] += 1  # x = 0, with P(0) = 0
        base.append(oh)
    threshold = improvement_threshold(q, k)
    best, n_best, n_above, n_checked = -1.0, 0, 0, 0
    examples, hist = [], {}
    started = time.time()
    for outer in product(range(n), repeat=len(outer_pos)):
        S = np.zeros(rows)
        for t in range(q):
            extra = np.zeros(n, dtype=np.int64)
            for pos, code in zip(outer_pos, outer):
                extra[add[code][tx[t][pos]]] += 1
            S += cl[base[t] + extra].sum(axis=1)
        n_checked += rows
        n_above += int((S > threshold + 1e-9).sum())
        top = float(S.max())
        if top > best + 1e-9:
            best, n_best, examples = top, 0, []
        if top > best - 1e-9:
            hits = np.nonzero(S > best - 1e-9)[0]
            n_best += len(hits)
            for i in hits[:max(0, keep - len(examples))]:
                codes = [0] * n
                for pos, code in zip(outer_pos, outer):
                    codes[pos] = code
                for pos, code in zip(inner_pos, grid[i]):
                    codes[pos] = int(code)
                examples.append(codes)
        vals, cnts = np.unique(np.round(S, 6), return_counts=True)
        for v, c in zip(vals.tolist(), cnts.tolist()):
            hist[v] = hist.get(v, 0) + c
    return {"q": q, "k": k, "mode": "exhaustive", "normalisation": "P(0) = 0",
            "maps_checked": n_checked, "seconds": round(time.time() - started, 1),
            "threshold": threshold, "ceiling": score_ceiling(q, k), "max_score": best,
            "maps_at_max": n_best, "maps_above_threshold": n_above,
            "h_min": k * math.log2(q) - best / q ** (k + 1), "k_times_c_q": k * exponent(q),
            "examples": [describe(F, q, k, vs, c) for c in examples],
            "score_histogram_top": [[v, c] for v, c in sorted(hist.items(), reverse=True)[:30]]}


def anneal(q, k, seconds, seed=1):
    """Simulated annealing on S(P), restarting from the best map or a random one each epoch."""
    F, vs, index, add, tx = tables(q, k)
    n = q ** k
    rng = random.Random(seed)
    cl = [c * math.log2(c) if c > 1 else 0.0 for c in range(n + 1)]
    square = [index[tuple(F.mul[a][a] for a in v)] for v in vs]
    best_codes = list(square)
    best = score_codes(q, k, add, tx, best_codes)
    epochs = 10
    epoch_len = seconds / epochs
    moves = 0
    started = time.time()
    for epoch in range(epochs):
        codes = list(best_codes) if epoch % 2 == 0 else [rng.randrange(n) for _ in range(n)]
        counts = [[0] * n for _ in range(q)]
        for t in range(q):
            for x in range(n):
                counts[t][add[codes[x]][tx[t][x]]] += 1
        score = sum(cl[c] for row in counts for c in row)
        epoch_start = time.time()
        temp = 2.0
        while True:
            for _ in range(1000):
                x = rng.randrange(n)
                new = rng.randrange(n)
                old = codes[x]
                if new == old:
                    continue
                delta = 0.0
                for t in range(q):
                    ca = counts[t][add[old][tx[t][x]]]
                    cb = counts[t][add[new][tx[t][x]]]
                    delta += cl[ca - 1] - cl[ca] + cl[cb + 1] - cl[cb]
                if delta >= 0 or rng.random() < math.exp(delta / temp):
                    for t in range(q):
                        counts[t][add[old][tx[t][x]]] -= 1
                        counts[t][add[new][tx[t][x]]] += 1
                    codes[x] = new
                    score += delta
                    if score > best + 1e-9:
                        exact = score_codes(q, k, add, tx, codes)
                        score = exact
                        if exact > best + 1e-9:
                            best, best_codes = exact, list(codes)
            moves += 1000
            frac = (time.time() - epoch_start) / epoch_len
            if frac >= 1:
                break
            temp = 2.0 * (0.01 / 2.0) ** frac
    out = {"q": q, "k": k, "mode": "anneal", "seconds": round(time.time() - started, 1),
           "moves": moves, "threshold": improvement_threshold(q, k),
           "ceiling": score_ceiling(q, k), "max_score": best,
           "h": k * math.log2(q) - best / q ** (k + 1), "k_times_c_q": k * exponent(q),
           "beats_threshold": best > improvement_threshold(q, k) + 1e-9}
    out.update(describe(F, q, k, vs, best_codes))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["exhaustive", "anneal"])
    ap.add_argument("--q", type=int, default=3)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--inner", type=int, default=4)
    ap.add_argument("--plan", nargs="*", default=[])
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.mode == "exhaustive":
        results = [exhaustive(args.q, args.k, args.inner)]
        path = os.path.join(args.out_dir, f"exhaustive-q{args.q}k{args.k}.json")
    else:
        results = []
        path = os.path.join(args.out_dir, "anneal.json")
        for i, item in enumerate(args.plan):
            q, k, seconds = (int(v) for v in item.split(":"))
            results.append(anneal(q, k, seconds, seed=args.seed + i))
            with open(path, "w") as fh:
                json.dump(results, fh, indent=1)
    with open(path, "w") as fh:
        json.dump(results, fh, indent=1)
    for r in results:
        print(json.dumps({key: r[key] for key in r if key not in ("examples", "map")}))


if __name__ == "__main__":
    main()
