# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma L census for the Kakeya block problem (note a159, Theorem 35).

By MV2 of Munim, Inc., 2026-11-17. Researched and written with AI agents working in MV2's name.
No human mathematician has checked this.

Notation (note a159). q a prime power, k >= 1, X uniform on V = F_q^k, P : V -> V any map,
Y_t = P(X) + t X. The information loss of P is

    Lambda(P) = sum_{t in F_q} H(X | Y_t)          (bits),

so h(P) = k log2 q - Lambda(P)/q and S(P) = q^k Lambda(P). Conjecture C_q(k): Lambda(P) <= k (q - 1)
for every P (equivalently h_k = k h_1). For a nonzero functional l put

    Lambda_l(P) = sum_t H(l(X) | Y_t).

Theorem 35: for l, a vector v with l(v) = 1, W = ker l, pi(x) = x - l(x) v and
Q_a(w) = pi(P(a v + w)) (a map W -> W),

    Lambda(P) <= Lambda_l(P) + (1/q) sum_a Lambda(Q_a)            ("chain bound").

Lemma L_q(k) (open): every P on F_q^k has some l with Lambda_l(P) <= q - 1. With C_q(k - 1) it
gives C_q(k). Lemma L'_q(k) (weaker, also open): every P has some (l, v) whose chain bound is at
most k (q - 1); it gives C_q(k) directly.

This module tests L and L' by exhaustive enumeration (numpy) and by adversarial annealing.

    python lemma_l.py exhaustive --q 3 --k 2 --out-dir out
    python lemma_l.py additive --q 4 --k 2 --out-dir out      (all F_2-linear maps, q = 2^m)
    python lemma_l.py anneal --q 4 --k 2 --seconds 900 --seed 1 --out-dir out
"""
import argparse
import itertools
import json
import math
import os
import random
import sys
import time
from collections import Counter

# Monic irreducible polynomials, coefficients from degree 0 up (same table as additive_maps.py
# and kakeya_entropy.py).
MODULI = {4: (2, (1, 1, 1)), 8: (2, (1, 1, 0, 1)), 9: (3, (1, 0, 1)), 16: (2, (1, 1, 0, 0, 1)),
          25: (5, (2, 1, 1)), 27: (3, (1, 2, 0, 1))}
PRIMES = (2, 3, 5, 7, 11, 13)
TOL = 1e-9


class Field:
    """F_q as the integers 0..q-1 (base-p digits = polynomial coefficients)."""

    def __init__(self, q):
        if q in MODULI:
            p, mod = MODULI[q]
            m = len(mod) - 1
        elif q in PRIMES:
            p, mod, m = q, None, 1
        else:
            raise ValueError(f"unsupported field size {q}")
        self.q, self.p, self.m, self.mod = q, p, m, mod
        D = [self.digits(a) for a in range(q)]
        self.add = [[self.number([(x + y) % p for x, y in zip(D[a], D[b])]) for b in range(q)]
                    for a in range(q)]
        self.neg = [self.number([(-x) % p for x in D[a]]) for a in range(q)]
        self.mul = [[self._mul(a, b) for b in range(q)] for a in range(q)]

    def digits(self, a):
        return [(a // self.p ** i) % self.p for i in range(self.m)]

    def number(self, ds):
        return sum(c * self.p ** i for i, c in enumerate(ds))

    def _mul(self, a, b):
        p, m = self.p, self.m
        if m == 1:
            return a * b % p
        prod = [0] * (2 * m - 1)
        for i, x in enumerate(self.digits(a)):
            for j, y in enumerate(self.digits(b)):
                prod[i + j] = (prod[i + j] + x * y) % p
        for deg in range(2 * m - 2, m - 1, -1):
            c = prod[deg]
            if c:
                for i, coeff in enumerate(self.mod):
                    prod[deg - m + i] = (prod[deg - m + i] - c * coeff) % p
        return self.number(prod[:m])


class Space:
    """F_q^k with vectors encoded as integers sum_i c_i q^i, plus tables for +, scalars and
    the projective set of nonzero functionals (first nonzero coefficient 1)."""

    def __init__(self, q, k):
        F = Field(q)
        self.F, self.q, self.k = F, q, k
        N = q ** k
        self.N = N
        C = [[(x // q ** i) % q for i in range(k)] for x in range(N)]
        self.coords = C

        def enc(c):
            return sum(ci * q ** i for i, ci in enumerate(c))

        self.enc = enc
        self.vadd = [[enc([F.add[a][b] for a, b in zip(C[x], C[y])]) for y in range(N)]
                     for x in range(N)]
        self.smul = [[enc([F.mul[t][a] for a in C[x]]) for x in range(N)] for t in range(q)]
        self.vneg = [enc([F.neg[a] for a in C[x]]) for x in range(N)]
        self.funcs = []
        for c in itertools.product(range(q), repeat=k):
            nz = [ci for ci in c if ci]
            if nz and nz[0] == 1:
                self.funcs.append(list(c))
        self.lval = []
        for c in self.funcs:
            row = []
            for x in range(N):
                s = 0
                for ci, xi in zip(c, C[x]):
                    s = F.add[s][F.mul[ci][xi]]
                row.append(s)
            self.lval.append(row)
        self.threshold = k * (q - 1)

    def ys(self, P, t):
        st = self.smul[t]
        va = self.vadd
        return [va[P[x]][st[x]] for x in range(self.N)]


def cond_ent(keys):
    """H(X | key(X)) in bits, X uniform on the positions: (1/n) sum over classes s log2 s."""
    n = len(keys)
    return sum(s * math.log2(s) for s in Counter(keys).values() if s > 1) / n


def profile(sp, P):
    """(Lambda(P), [Lambda_l(P) for each projective functional l])."""
    lam = 0.0
    lams = [0.0] * len(sp.funcs)
    for t in range(sp.q):
        Y = sp.ys(P, t)
        h = cond_ent(Y)
        lam += h
        for i, L in enumerate(sp.lval):
            lams[i] += h - cond_ent(list(zip(Y, L)))
    return lam, lams


def loss(sp, P):
    return sum(cond_ent(sp.ys(P, t)) for t in range(sp.q))


def chain_bound(sp, P, li, v, lam_l=None):
    """Right side of Theorem 35 for the functional sp.funcs[li] and v with l(v) = 1."""
    L = sp.lval[li]
    if L[v] != 1:
        raise ValueError("need l(v) = 1")
    q = sp.q
    if lam_l is None:
        lam_l = profile(sp, P)[1][li]
    W = [w for w in range(sp.N) if L[w] == 0]
    va, sm, vn = sp.vadd, sp.smul, sp.vneg

    def pi(x):
        return va[x][vn[sm[L[x]][v]]]

    rest = 0.0
    for a in range(q):
        base = sm[a][v]
        Q = {w: pi(P[va[base][w]]) for w in W}
        for t in range(q):
            rest += cond_ent([va[Q[w]][sm[t][w]] for w in W])
    return lam_l + rest / q


def best_chain(sp, P):
    """min over (l, v) of the chain bound, with the minimising (l index, v)."""
    _, lams = profile(sp, P)
    best = None
    for li, L in enumerate(sp.lval):
        for v in range(sp.N):
            if L[v] == 1:
                c = chain_bound(sp, P, li, v, lams[li])
                if best is None or c < best[0]:
                    best = (c, li, v)
    return best


def exact_beats(sp, P):
    """True iff S(P) > k (q - 1) q^k, decided exactly: prod s^s > 2^(k (q-1) q^k)."""
    prod = 1
    for t in range(sp.q):
        for s in Counter(sp.ys(P, t)).values():
            prod *= s ** s
    return prod > 2 ** (sp.threshold * sp.N)


def frobenius_product(sp):
    """Coordinatewise x -> x^p (k = 1 optimum for p = 2; for odd q use square_product)."""
    F = sp.F
    f = []
    for a in range(sp.q):
        r = 1
        for _ in range(F.p):
            r = F.mul[r][a]
        f.append(r)
    return [sp.enc([f[c] for c in sp.coords[x]]) for x in range(sp.N)]


def square_product(sp):
    F = sp.F
    return [sp.enc([F.mul[c][c] for c in sp.coords[x]]) for x in range(sp.N)]


# ---------------------------------------------------------------- numpy evaluator

def np_tables(sp):
    import numpy as np
    N = sp.N
    same = np.array([[[L[x] == L[y] for y in range(N)] for x in range(N)] for L in sp.lval],
                    dtype=bool)
    log2 = np.array([0.0] + [math.log2(s) for s in range(1, N + 1)])
    return {"np": np, "vadd": np.array(sp.vadd, dtype=np.int32),
            "smul": np.array(sp.smul, dtype=np.int32), "same": same, "log2": log2}


def np_profile(sp, M, tabs):
    """Vectorised profile for a batch M of maps (shape (B, N)): (Lambda (B,), Lambda_l (nf, B))."""
    np = tabs["np"]
    vadd, smul, same, log2 = tabs["vadd"], tabs["smul"], tabs["same"], tabs["log2"]
    B = M.shape[0]
    lam = np.zeros(B)
    lams = np.zeros((len(sp.funcs), B))
    for t in range(sp.q):
        Y = vadd[M, smul[t][None, :]]
        eq = Y[:, :, None] == Y[:, None, :]
        h = log2[eq.sum(axis=2)].mean(axis=1)
        lam += h
        for i in range(len(sp.funcs)):
            c = (eq & same[i][None, :, :]).sum(axis=2)
            lams[i] += h - log2[c].mean(axis=1)
    return lam, lams


class Tally:
    """Collects the census statistics for one (q, k) family of maps."""

    def __init__(self, sp, max_chain=200000, max_examples=20):
        self.sp = sp
        self.maps = 0
        self.max_lam = -1.0
        self.at_threshold = 0
        self.above_threshold = 0
        self.c_counterexamples = []
        self.l_fail = 0
        self.max_v = -1.0
        self.max_v_map = None
        self.l_fail_examples = []
        self.chain_checked = 0
        self.chain_fail = 0
        self.max_chain_excess = None
        self.chain_fail_examples = []
        self.max_chain = max_chain
        self.max_examples = max_examples

    def add_batch(self, M, lam, lams):
        sp = self.sp
        q1 = sp.q - 1
        thr = sp.threshold
        v = lams.min(axis=0)
        self.maps += M.shape[0]
        bl = float(lam.max())
        if bl > self.max_lam:
            self.max_lam = bl
        self.at_threshold += int(((lam > thr - TOL) & (lam < thr + TOL)).sum())
        above = (lam >= thr + TOL).nonzero()[0]
        self.above_threshold += len(above)
        for j in above[:self.max_examples]:
            P = [int(a) for a in M[j]]
            if len(self.c_counterexamples) < self.max_examples:
                self.c_counterexamples.append({"P": P, "lambda": float(lam[j]),
                                               "exact_beats": exact_beats(sp, P)})
        bv = int(v.argmax())
        if float(v[bv]) > self.max_v:
            self.max_v = float(v[bv])
            self.max_v_map = [int(a) for a in M[bv]]
        fails = (v > q1 + TOL).nonzero()[0]
        self.l_fail += len(fails)
        need = max(self.max_chain - self.chain_checked,
                   self.max_examples - len(self.l_fail_examples), 0)
        for j in fails[:need]:
            P = [int(a) for a in M[j]]
            if len(self.l_fail_examples) < self.max_examples:
                self.l_fail_examples.append({"P": P, "lambda": float(lam[j]),
                                             "min_lambda_l": float(v[j])})
            if self.chain_checked < self.max_chain:
                self.chain_checked += 1
                c, li, vv = best_chain(sp, P)
                ex = c - thr
                if self.max_chain_excess is None or ex > self.max_chain_excess:
                    self.max_chain_excess = ex
                if ex > TOL:
                    self.chain_fail += 1
                    if len(self.chain_fail_examples) < self.max_examples:
                        self.chain_fail_examples.append({"P": P, "lambda": float(lam[j]),
                                                         "best_chain": c, "l": sp.funcs[li],
                                                         "v": vv})

    def report(self):
        sp = self.sp
        return {"q": sp.q, "k": sp.k, "threshold": sp.threshold, "maps": self.maps,
                "max_lambda": self.max_lam, "maps_at_threshold": self.at_threshold,
                "maps_above_threshold": self.above_threshold,
                "C_counterexamples": self.c_counterexamples,
                "L_fail": self.l_fail, "max_min_lambda_l": self.max_v,
                "max_min_lambda_l_map": self.max_v_map,
                "L_fail_examples": self.l_fail_examples,
                "chain_checked": self.chain_checked, "chain_fail": self.chain_fail,
                "max_chain_excess_over_threshold": self.max_chain_excess,
                "chain_fail_examples": self.chain_fail_examples}


def write_json(out_dir, name, obj):
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, name)
    with open(path + ".tmp", "w") as f:
        json.dump(obj, f, indent=1)
    os.replace(path + ".tmp", path)
    return path


def run_exhaustive(q, k, out_dir, batch=100000, seconds=None):
    """Every map with P(0) = 0 (constants change nothing), N^(N-1) of them."""
    sp = Space(q, k)
    tabs = np_tables(sp)
    np = tabs["np"]
    N = sp.N
    total = N ** (N - 1)
    tally = Tally(sp)
    t0 = time.time()
    done = 0
    complete = True
    name = f"lemmal_exhaustive_q{q}k{k}.json"
    while done < total:
        end = min(total, done + batch)
        idx = np.arange(done, end, dtype=np.int64)
        M = np.zeros((end - done, N), dtype=np.int32)
        for j in range(1, N):
            M[:, j] = idx % N
            idx //= N
        lam, lams = np_profile(sp, M, tabs)
        tally.add_batch(M, lam, lams)
        done = end
        if seconds is not None and time.time() - t0 > seconds and done < total:
            complete = False
            break
        if (done // batch) % 25 == 0:
            rep = tally.report()
            rep.update({"mode": "exhaustive", "total": total, "complete": False,
                        "seconds": round(time.time() - t0, 1)})
            write_json(out_dir, name, rep)
    rep = tally.report()
    rep.update({"mode": "exhaustive", "total": total, "complete": complete and done == total,
                "seconds": round(time.time() - t0, 1)})
    write_json(out_dir, name, rep)
    return rep


def run_additive(q, k, out_dir, batch=8192):
    """Every F_2-linear map of F_q^k (q = 2^m): vectors are bit strings, + is XOR."""
    sp = Space(q, k)
    if sp.F.p != 2:
        raise ValueError("additive mode needs q = 2^m")
    tabs = np_tables(sp)
    np = tabs["np"]
    N = sp.N
    n = N.bit_length() - 1
    total = N ** n
    tally = Tally(sp)
    t0 = time.time()
    done = 0
    bits = np.array([[(x >> i) & 1 for i in range(n)] for x in range(N)], dtype=np.int32)
    while done < total:
        end = min(total, done + batch)
        idx = np.arange(done, end, dtype=np.int64)
        cols = np.zeros((end - done, n), dtype=np.int32)
        for i in range(n):
            cols[:, i] = idx % N
            idx //= N
        M = np.zeros((end - done, N), dtype=np.int32)
        for i in range(n):
            M ^= bits[None, :, i] * cols[:, i:i + 1]
        lam, lams = np_profile(sp, M, tabs)
        tally.add_batch(M, lam, lams)
        done = end
    rep = tally.report()
    rep.update({"mode": "additive", "total": total, "complete": done == total,
                "seconds": round(time.time() - t0, 1)})
    write_json(out_dir, f"lemmal_additive_q{q}k{k}.json", rep)
    return rep


def run_anneal(q, k, seconds, seed, out_dir):
    """Adversarial search: maximise V(P) = min_l Lambda_l(P), the quantity Lemma L bounds by
    q - 1. Every map that breaks L gets its best chain bound (L') checked; any map with
    Lambda(P) above k (q - 1) would be a counterexample to C_q(k), decided exactly."""
    sp = Space(q, k)
    rng = random.Random(seed)
    N, q1, thr = sp.N, q - 1, sp.threshold
    t0 = time.time()
    best = {"v": -1.0}
    l_fail_maps = {}
    chain_fail = []
    c_fail = []
    max_chain_excess = None
    restarts = 0
    evals = 0

    def evaluate(P):
        lam, lams = profile(sp, P)
        return lam, min(lams)

    def check(P, lam, v):
        nonlocal max_chain_excess
        key = tuple(P)
        if v > q1 + TOL and key not in l_fail_maps and len(l_fail_maps) < 2000:
            c, li, vv = best_chain(sp, P)
            ex = c - thr
            l_fail_maps[key] = ex
            if max_chain_excess is None or ex > max_chain_excess:
                max_chain_excess = ex
            if ex > TOL and len(chain_fail) < 20:
                chain_fail.append({"P": P[:], "lambda": lam, "min_lambda_l": v, "best_chain": c,
                                   "l": sp.funcs[li], "v": vv})
        if lam > thr + TOL and len(c_fail) < 20:
            c_fail.append({"P": P[:], "lambda": lam, "exact_beats": exact_beats(sp, P)})

    starts = [frobenius_product(sp) if sp.F.p == 2 else square_product(sp)]
    while time.time() - t0 < seconds:
        restarts += 1
        if starts:
            P = starts.pop()
        else:
            P = [0] + [rng.randrange(N) for _ in range(N - 1)]
        lam, v = evaluate(P)
        evals += 1
        T0, T1 = 0.3, 0.003
        steps = 20000
        for s in range(steps):
            if time.time() - t0 >= seconds:
                break
            T = T0 * (T1 / T0) ** (s / steps)
            x = rng.randrange(1, N)
            old = P[x]
            P[x] = rng.randrange(N)
            lam2, v2 = evaluate(P)
            evals += 1
            if v2 >= v or rng.random() < math.exp((v2 - v) / T):
                lam, v = lam2, v2
                check(P, lam, v)
                if v > best["v"] + TOL:
                    best = {"v": v, "lambda": lam, "P": P[:]}
            else:
                P[x] = old
    excess = sorted(l_fail_maps.values())
    rep = {"mode": "anneal", "q": q, "k": k, "seed": seed, "seconds": round(time.time() - t0, 1),
           "threshold": thr, "restarts": restarts, "evals": evals,
           "max_min_lambda_l": best.get("v"), "best_map": best.get("P"),
           "best_map_lambda": best.get("lambda"),
           "L_fail_distinct_maps": len(l_fail_maps),
           "max_chain_excess_over_threshold": max_chain_excess,
           "chain_fail_examples": chain_fail, "C_counterexamples": c_fail,
           "chain_excess_quantiles": [excess[int(f * (len(excess) - 1))] for f in (0, .5, .9, 1)]
           if excess else []}
    write_json(out_dir, f"lemmal_anneal_q{q}k{k}_s{seed}.json", rep)
    return rep


def summary_line(rep):
    keys = ["mode", "q", "k", "maps", "complete", "max_lambda", "maps_at_threshold",
            "maps_above_threshold", "L_fail", "L_fail_distinct_maps", "max_min_lambda_l",
            "chain_checked", "chain_fail", "max_chain_excess_over_threshold", "seconds"]
    return "SUMMARY " + json.dumps({k: rep[k] for k in keys if k in rep})


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["exhaustive", "additive", "anneal"])
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--seconds", type=float, default=None)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out-dir", default="out")
    a = ap.parse_args(argv)
    if a.mode == "exhaustive":
        rep = run_exhaustive(a.q, a.k, a.out_dir, seconds=a.seconds)
    elif a.mode == "additive":
        rep = run_additive(a.q, a.k, a.out_dir)
    else:
        rep = run_anneal(a.q, a.k, a.seconds or 600, a.seed, a.out_dir)
    print(summary_line(rep), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
