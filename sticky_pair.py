# sticky_pair.py -- search over PAIRS of sticky trees for the pair operation of note a196
# (pre-registration notes/prereg-sticky-pair.md, job sticky-pair-v1).
#
# Pair operation (a196, section 4).  For full sticky trees A, B of height h over F_3 and a
# translation v, the tree N of height h+1 with root x^2 over (A + v, B, B(-e)) has
#   N_0 = {0} x A_0 u {1} x B_0,
#   N_1 = {0} x ((A_1 + v) u B_2) u {2} x B_1,   N_2 = {0} x ((A_2 + v) u B_2) u {2} x B_1,
# and its cyclic triangle (Proposition 89, i = 0, w = 0) has three slices of size
#   lambda(A, B) = |A_0| + |B_0| + |B_1| + min_v |B_2 u ((A_1 u A_2) + v)|,
# so pi_{h+2} <= lambda^3 and the sticky Kakeya base beta_s <= lambda^(1/(h+2)).
# Theorem 79 is lambda = 31 at h = 3 (base 31^(1/5) = 1.98734).  To improve it one needs
# lambda <= 30 at h = 3, or lambda <= 61 at h = 4 (61^(1/6) = 1.98407).
#
# Method: simulated annealing over the value tables of A and B (one entry per coordinate j and
# prefix d_1..d_j), seeded with the a196 trees, their products with the height-1 tree x^2, and
# random trees.  Every best pair is rebuilt as explicit maps N and triangle(N) and its slices are
# counted by brute force (sticky_s7.slices); the verdict uses only the rebuilt counts.
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only.

import collections
import json
import math
import random
import sys
import time

import sticky_s7 as s7


class Shape:
    def __init__(self, h):
        self.h = h
        self.dom = s7.domain(h)
        self.N = 3 ** h
        self.pow3 = [3 ** j for j in range(h)]
        self.sizes = [3 ** (j + 1) for j in range(h)]
        self.pidx = [[prefix_index(d, j) for d in self.dom] for j in range(h)]
        dec = [self.decode(c) for c in range(self.N)]
        self.ADD = [[self.encode(tuple((x + y) % 3 for x, y in zip(dec[a], dec[b])))
                     for b in range(self.N)] for a in range(self.N)]

    def encode(self, p):
        return sum(x * self.pow3[j] for j, x in enumerate(p))

    def decode(self, c):
        return tuple((c // self.pow3[j]) % 3 for j in range(self.h))


def prefix_index(d, j):
    c = 0
    for i in range(j + 1):
        c = c * 3 + d[i]
    return c


def table_of(P, shape):
    """Value table of a sticky map: tbl[j][prefix_index(d, j)] = P(d)[j]."""
    tbl = [[0] * shape.sizes[j] for j in range(shape.h)]
    for di, d in enumerate(shape.dom):
        v = P(d)
        for j in range(shape.h):
            tbl[j][shape.pidx[j][di]] = v[j] % 3
    return tbl


def fn_of(tbl, shape, shift=None):
    def P(d):
        out = []
        for j in range(shape.h):
            x = tbl[j][prefix_index(d, j)]
            if shift is not None:
                x = (x + shift[j]) % 3
            out.append(x)
        return tuple(out)
    return P


def copy_tbl(tbl):
    return [row[:] for row in tbl]


def random_table(shape, rng):
    return [[rng.randrange(3) for _ in range(shape.sizes[j])] for j in range(shape.h)]


def slice_codes(tbl, shape):
    out = []
    for t in range(3):
        s = set()
        for di, d in enumerate(shape.dom):
            c = 0
            for j in range(shape.h):
                c += ((tbl[j][shape.pidx[j][di]] + t * d[j]) % 3) * shape.pow3[j]
            s.add(c)
        out.append(s)
    return out


def lam(tblA, tblB, shape):
    """(lambda(A, B), best translation code v)."""
    SA = slice_codes(tblA, shape)
    SB = slice_codes(tblB, shape)
    U = list(SA[1] | SA[2])
    B2 = SB[2]
    base = len(SA[0]) + len(SB[0]) + len(SB[1])
    best = None
    bv = 0
    for v in range(shape.N):
        row = shape.ADD[v]
        n = len(B2.union([row[u] for u in U]))
        if best is None or n < best:
            best, bv = n, v
            if best == len(B2):
                break
    return base + best, bv


def verify_pair(tblA, tblB, v_code, shape):
    """Rebuild N (height h+1) and its cyclic triangle (height h+2) as maps; count slices."""
    h = shape.h
    v = shape.decode(v_code)
    PA = fn_of(tblA, shape, v)
    PB = fn_of(tblB, shape)

    def PC(e):
        return PB(tuple((-x) % 3 for x in e))
    kids = (PA, PB, PC)

    def N(d):
        return (d[0] * d[0] % 3,) + kids[d[0]](d[1:])
    kidsT = (N, s7.rho(N, 2), s7.rho(N, 1))

    def T(d):
        return (d[0] * d[0] % 3,) + kidsT[d[0]](d[1:])
    SN = s7.slices(N, h + 1)
    ST = s7.slices(T, h + 2)
    return {"sticky": s7.is_sticky(N, h + 1) and s7.is_sticky(T, h + 2),
            "N_slices": [len(s) for s in SN], "triangle_slices": [len(s) for s in ST]}


def seeds_for(h, shape):
    q = lambda d: (d[0] * d[0] % 3,)
    out = []
    if h == 3:
        out.append(("a196 (A, B)", s7.tree_A, s7.tree_B))
        out.append(("classical", s7.classical, s7.classical))
    elif h == 4:
        out.append(("(H, H)", s7.tree_H, s7.tree_H))
        out.append(("(A x q, B x q)", lambda d: s7.tree_A(d[:3]) + q(d[3:]),
                    lambda d: s7.tree_B(d[:3]) + q(d[3:])))
        out.append(("(H, H(-d))", s7.tree_H, lambda d: s7.tree_H(tuple((-x) % 3 for x in d))))
        out.append(("classical", s7.classical, s7.classical))
    return [(name, table_of(PA, shape), table_of(PB, shape)) for name, PA, PB in out]


def anneal(shape, seeds, rng, seconds, steps=20000, T0=1.5, T1=0.05):
    t_end = time.time() + seconds
    best = None
    finals = collections.Counter()
    restarts = 0
    while time.time() < t_end:
        if restarts < len(seeds):
            A, B = copy_tbl(seeds[restarts][1]), copy_tbl(seeds[restarts][2])
        elif best is not None and rng.random() < 0.5:
            A, B = copy_tbl(best[1]), copy_tbl(best[2])
            for _ in range(rng.randint(1, 6)):
                X = A if rng.random() < 0.5 else B
                j = rng.randrange(shape.h)
                k = rng.randrange(shape.sizes[j])
                X[j][k] = rng.randrange(3)
        else:
            A, B = random_table(shape, rng), random_table(shape, rng)
        cur, _ = lam(A, B, shape)
        if best is None or cur < best[0]:
            best = (cur, copy_tbl(A), copy_tbl(B))
        for step in range(steps):
            if step % 256 == 0 and time.time() > t_end:
                break
            T = T0 * (T1 / T0) ** (step / float(steps))
            X = A if rng.random() < 0.5 else B
            j = rng.randrange(shape.h)
            k = rng.randrange(shape.sizes[j])
            old = X[j][k]
            X[j][k] = (old + rng.randint(1, 2)) % 3
            new, _ = lam(A, B, shape)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
                if cur < best[0]:
                    best = (cur, copy_tbl(A), copy_tbl(B))
            else:
                X[j][k] = old
        finals[cur] += 1
        restarts += 1
    return best, restarts, finals


def run(out_path, minutes=100.0, seed=20261120):
    t0 = time.time()
    rng = random.Random(seed)
    res = {"job": "sticky-pair-v1",
           "made_with": "AI agents working in MV2's name; no human has checked this",
           "heights": {}}
    bugs = []
    plan = {3: 0.3 * minutes * 60.0, 4: 0.7 * minutes * 60.0}
    target = {3: 30, 4: 61}
    for h in (3, 4):
        shape = Shape(h)
        seeds = seeds_for(h, shape)
        seed_vals = {}
        for name, A, B in seeds:
            seed_vals[name] = lam(A, B, shape)[0]
        best, restarts, finals = anneal(shape, seeds, rng, plan[h])
        val, A, B = best
        lv, v = lam(A, B, shape)
        ver = verify_pair(A, B, v, shape)
        if lv != val:
            bugs.append("h=%d: stored best %d but recomputed %d" % (h, val, lv))
        if not ver["sticky"]:
            bugs.append("h=%d: rebuilt tree is not sticky" % h)
        if ver["triangle_slices"] != [lv, lv, lv]:
            bugs.append("h=%d: rebuilt triangle slices %s differ from lambda %d"
                        % (h, ver["triangle_slices"], lv))
        res["heights"][str(h)] = {
            "seed_values": seed_vals, "best_lambda": lv, "restarts": restarts,
            "final_value_histogram": {str(k): c for k, c in sorted(finals.items())},
            "verification": ver, "translation_v": list(shape.decode(v)),
            "base_bound": round(lv ** (1.0 / (h + 2)), 6),
            "improves_31_over_5": lv <= target[h],
            "A_table": A, "B_table": B}
        print("h=%d best lambda %d (restarts %d) verification %s" % (h, lv, restarts, ver),
              flush=True)
    if seed_vals and res["heights"]["3"]["seed_values"].get("a196 (A, B)") != 31:
        bugs.append("a196 seed pair does not give lambda = 31")
    improved = [h for h in ("3", "4") if res["heights"][h]["improves_31_over_5"]]
    if bugs:
        verdict = "BUG"
    elif improved:
        verdict = "BASE-IMPROVED"
    else:
        verdict = "NOT-FOUND"
    res["bugs"] = bugs
    res["verdict"] = verdict
    res["seconds"] = round(time.time() - t0, 1)
    with open(out_path, "w") as fh:
        json.dump(res, fh, indent=1)
    print("verdict", verdict, flush=True)
    return res


if __name__ == "__main__":
    args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
    run(args.get("--out", "pair.json"), float(args.get("--minutes", 100)))
