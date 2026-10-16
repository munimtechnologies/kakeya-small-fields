# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for robust-cubes-v5m/v5n (draft for kakeya-small-fields 1.7): Theorems 29, 29' and 27,
Proposition 28 and the r = 3 peeling LP of Proposition 30. Y_t = A d_1^(t_1) ... d_r^(t_r),
[a, b] = a^-1 b^-1 a b, b(G) = the largest conjugacy class size (Theorem 34: b may replace |G'|).

Theorem 29. If d_2, ..., d_r commute pairwise almost surely, then for every random (A, d)
    sum_t H(Y_t) >= ((2^r - 1)/r) H(d) - ((2^r - 1 - r)/r) log b(G).
Theorem 29' (r = 3, set form). If K contains a left translate of the 3-cube of every d in D, then
    |K|^24 |G12| |G13|^2 |G1,23| |G23|^2 >= |D|^7,
G12, G13, G1,23, G23 = the sets of values of [d_1, d_2], [d_1, d_3], [d_1, d_2 d_3], [d_2, d_3].
Theorem 27 + 34 (r = 3, no hypothesis): |K|^24 b^6 >= |D|^7.
Proposition 28. K = S L (L any subgroup), D = (K^-1 K) x L^(r-1): every d in D is served and
    |K|^(r 2^r) m^(2^r - 1 - r) >= |D|^(2^r - 1) for m = |G'| and for m = b (|L g L| <= |L| b).
G(p, k) with D = (G minus HZ) x H x H: the six peeling orders (321, 312, 231, 213, 132, 123) exceed
8 log|K| by w log(p - 1) - 8 log|S| + (w - 1) k log p, w = 2^(3 - pos(1)) = (1, 2, 1, 2, 4, 4),
and the order-sigma peeling inequality (losses (0, 1, 0, 1, 3, 3) times log|G'|) holds.
Proposition 30: the six-constraint LP has maximum E = 4 + 2 lambda, attained only at
x = 1 - 4 lambda/7, y = 1 + 2 lambda/7 (exact rationals).
Proposition 35 (robust-cubes-v5q): in the tensor Heisenberg group F_p^2 x F_p^k x (F_p^2 (x) F_p^k),
b = p^(k+1) but |G'| = p^(2k); the coset design S = {0, e_1, e_2}, L = H has |K| = 3 p^k,
|K^-1 K| = (|S - S| - 1) p^(2k) + p^k, K^-1 K generates G, and Theorems 25 and 29 in the b form
are tight up to constants while the |G'| form is off by p^(k-1) (resp. p^(4(k-1))).
Exploratory (no assertion): the least value of (sum H(Y_t) - (7/3) H(d)) / log b over laws with
NON-commuting d_2, d_3 found by local search, and how many sets in small groups break
|K|^24 b^4 >= |D|^7 (exponent 1/6). Theorem 27 + 34 force the first to be >= -2; a value below -4/3
would show the entropy form of exponent 1/6 fails without the commuting hypothesis.

    python theorem29.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os
import random
from fractions import Fraction

from prop31_cubes import cube_in, generated, groups, inverses, perm_group, table_from
from twosided import commutator_subgroup, cube_points, design_law, entropy, gpk, max_class

ORDERS = ("321", "312", "231", "213", "132", "123")
D1_LOSSES = {"321": 0, "312": 1, "231": 0, "213": 1, "132": 3, "123": 3}


def comm(T, inv, a, b):
    return T[T[T[inv[a]][inv[b]]][a]][b]


def centraliser(T, x):
    return [y for y in range(len(T)) if T[x][y] == T[y][x]]


def named_groups():
    named = dict(groups())
    named["S_4"] = perm_group([(1, 0, 2, 3), (1, 2, 3, 0)])
    named["G(3,1)"] = gpk(3, 1)[1]
    return named


# ---- Theorem 29: random laws with commuting late generators -------------------------------

def commuting_law(T, r, rng, size):
    """Random law on (A, d_1, ..., d_r) whose d_2, ..., d_r commute pairwise on the support."""
    n, support = len(T), []
    for _ in range(size):
        late = []
        for _ in range(r - 1):
            pool = [y for y in range(n) if all(T[y][z] == T[z][y] for z in late)]
            late.append(rng.choice(pool))
        support.append((rng.randrange(n), rng.randrange(n)) + tuple(reversed(late)))
    weights = [rng.random() for _ in support]
    s = sum(weights)
    return [(x / s, o) for x, o in zip(weights, support)]


def cube_sum(T, law):
    r = len(law[0][1]) - 1
    return sum(entropy(law, lambda o, n=n: cube_points(T, o)[n]) for n in range(2 ** r))


def theorem29_slack(T, law, logm):
    r = len(law[0][1]) - 1
    hd = entropy(law, lambda o: o[1:])
    return cube_sum(T, law) - (2 ** r - 1) / r * hd + (2 ** r - 1 - r) / r * logm


# ---- Theorem 29' and Theorem 27 (set forms) ------------------------------------------------

def served_all(T, K, r):
    """Every r-tuple d having a left translate of its cube inside K."""
    inv, out = inverses(T), set()
    for A in K:
        right = sorted(T[inv[A]][k] for k in K)
        for d in itertools.product(right, repeat=r):
            if d not in out and cube_in(T, K, A, d):
                out.add(d)
    return out


def gamma_product(T, D):
    inv = inverses(T)
    g12 = {comm(T, inv, a, b) for a, b, c in D}
    g13 = {comm(T, inv, a, c) for a, b, c in D}
    g123 = {comm(T, inv, a, T[b][c]) for a, b, c in D}
    g23 = {comm(T, inv, b, c) for a, b, c in D}
    return len(g12) * len(g13) ** 2 * len(g123) * len(g23) ** 2


def set_forms(T, K, D, b):
    """(Theorem 29' holds, its log2 slack, Theorem 27 + 34 holds, exponent-1/6 form holds)."""
    k, d, gp = len(K), len(D), gamma_product(T, D)
    slack = 24 * math.log2(k) + math.log2(gp) - 7 * math.log2(d)
    return k ** 24 * gp >= d ** 7, slack, k ** 24 * b ** 6 >= d ** 7, k ** 24 * b ** 4 >= d ** 7


def exhaustive(T, rng, subsamples=4):
    n, b = len(T), max_class(T)
    out = {"sets": 0, "thm29p_violations": 0, "thm27b_violations": 0, "sixth_breaks": 0,
           "least_slack": None, "subsets_checked": 0}
    for mask in range(1, 2 ** n):
        K = frozenset(x for x in range(n) if mask >> x & 1)
        D = sorted(served_all(T, K, 3))
        if not D:
            continue
        ok, slack, ok27, ok6 = set_forms(T, K, D, b)
        out["sets"] += 1
        out["thm29p_violations"] += not ok
        out["thm27b_violations"] += not ok27
        out["sixth_breaks"] += not ok6
        if out["least_slack"] is None or slack < out["least_slack"][0]:
            out["least_slack"] = (slack, sorted(K), len(D))
        for _ in range(subsamples if len(D) > 1 else 0):
            sub = rng.sample(D, rng.randint(1, len(D)))
            ok, _, ok27, _ = set_forms(T, K, sub, b)
            out["subsets_checked"] += 1
            out["thm29p_violations"] += not ok
            out["thm27b_violations"] += not ok27
    return out


# ---- G(p, k): the excess of every peeling order --------------------------------------------

def gpk_design(p, k):
    elems, T = gpk(p, k)
    index = {x: n for n, x in enumerate(elems)}
    vecs = list(itertools.product(range(p), repeat=k))
    zero = tuple([0] * k)
    S = (0, 1)
    K = frozenset(index[(t, h, tuple(t * x % p for x in h))] for t in S for h in vecs)
    H = [index[(0, h, zero)] for h in vecs]
    first = [n for n, x in enumerate(elems) if x[0] != 0]
    D = [(a,) + hs for a in first for hs in itertools.product(H, repeat=2)]
    return T, K, D, len(S)


def order_main(law, sigma):
    """T + 2 H(x_1) + H(x_1, x_2) for the order sigma (x_i = d_(sigma_i)), the lossless main term."""
    i, j = int(sigma[0]), int(sigma[1])
    return (entropy(law, lambda o: o) + 2 * entropy(law, lambda o: o[i])
            + entropy(law, lambda o: (o[i], o[j])))


def gpk_excess(p, k):
    T, K, D, s = gpk_design(p, k)
    law = design_law(T, K, D)
    lhs, cap = cube_sum(T, law), 8 * math.log2(len(K))
    g = math.log2(len(commutator_subgroup(T)))
    rows = {}
    for sigma in ORDERS:
        w = 2 ** (3 - sigma.index("1") - 1)
        main = order_main(law, sigma)
        predicted = w * math.log2(p - 1) - 8 * math.log2(s) + (w - 1) * k * math.log2(p)
        rows[sigma] = {"excess": main - cap, "predicted": predicted,
                       "matches": abs(main - cap - predicted) < 1e-9,
                       "peeling_holds": lhs >= main - D1_LOSSES[sigma] * g - 1e-9}
    return {"K": len(K), "D": len(D), "lhs": lhs, "cap": cap, "lhs_le_cap": lhs <= cap + 1e-9,
            "orders": rows}


# ---- Proposition 28 ------------------------------------------------------------------------

def subgroups(T):
    n = len(T)
    return sorted({generated(T, (x, y)) for x in range(n) for y in range(x, n)},
                  key=lambda L: (len(L), sorted(L)))


def proposition28(T, rng, sample=60):
    """Every subgroup L, every S = {1} or {1, s}; r = 2 (every d served) and r = 3 (sampled)."""
    n, inv = len(T), inverses(T)
    gd, b = len(commutator_subgroup(T)), max_class(T)
    out = {"designs": 0, "unserved": 0, "violations_derived": 0, "violations_b": 0,
           "double_coset_ok": True, "least_ratio_b": None}
    for L in subgroups(T):
        out["double_coset_ok"] &= all(len({T[T[l][g]][m] for l in L for m in L}) <= len(L) * b
                                      for g in range(n))
        for K in {frozenset(T[s][l] for s in S for l in L) for S in [(0,)] + [(0, x) for x in range(1, n)]}:
            diffs = sorted({T[inv[a]][c] for a in K for c in K})
            for r in (2, 3):
                D = [(x,) + h for x in diffs for h in itertools.product(sorted(L), repeat=r - 1)]
                check = D if r == 2 else rng.sample(D, min(sample, len(D)))
                out["unserved"] += sum(not any(cube_in(T, K, A, d) for A in K) for d in check)
                lhs = len(K) ** (r * 2 ** r)
                out["designs"] += 1
                out["violations_derived"] += lhs * gd ** (2 ** r - 1 - r) < len(D) ** (2 ** r - 1)
                out["violations_b"] += lhs * b ** (2 ** r - 1 - r) < len(D) ** (2 ** r - 1)
                ratio = (r * 2 ** r * math.log2(len(K)) + (2 ** r - 1 - r) * math.log2(b)) \
                    / ((2 ** r - 1) * math.log2(len(D))) if len(D) > 1 else None
                if ratio is not None and (out["least_ratio_b"] is None or ratio < out["least_ratio_b"]):
                    out["least_ratio_b"] = ratio
    return out


# ---- Proposition 30: the six-constraint LP --------------------------------------------------

def lp_constraints(lam):
    """E <= c0 + cx x + cy y for the six orders (v5n section 1)."""
    return {"321": (0, -1, 5), "312": (3, -4, 5), "231": (6 * lam, 5, -1),
            "213": (3 + 6 * lam, 5, -4), "132": (9, -4, -1), "123": (9 + 3 * lam, -1, -4)}


def peeling_lp(lam):
    """Exact vertex enumeration; returns (max E, optimal points, dual certificate value)."""
    lam = Fraction(lam)
    cons = {k: tuple(Fraction(v) for v in c) for k, c in lp_constraints(lam).items()}
    vertices = set()
    for a, b, c in itertools.combinations(cons.values(), 3):
        # c0_a + cx_a x + cy_a y = c0_b + ... = c0_c + ...
        p1, q1, r1 = a[1] - b[1], a[2] - b[2], b[0] - a[0]
        p2, q2, r2 = a[1] - c[1], a[2] - c[2], c[0] - a[0]
        det = p1 * q2 - p2 * q1
        if det == 0:
            continue
        x, y = (r1 * q2 - r2 * q1) / det, (p1 * r2 - p2 * r1) / det
        E = a[0] + a[1] * x + a[2] * y
        if all(E <= c0 + cx * x + cy * y for c0, cx, cy in cons.values()):
            vertices.add((E, x, y))
    best = max(v[0] for v in vertices)
    points = sorted((x, y) for E, x, y in vertices if E == best)
    mu = {"321": Fraction(1, 3), "213": Fraction(1, 3), "132": Fraction(1, 3)}
    grad = [sum(m * cons[k][i] for k, m in mu.items()) for i in (1, 2)]
    dual = sum(m * cons[k][0] for k, m in mu.items()) if grad == [0, 0] else None
    return best, points, dual


# ---- Proposition 35: the tensor Heisenberg group, where b(G) is sharp and |G'| is not -------

def tensor_heisenberg(p, j, k):
    """F_p^j x F_p^k x (F_p^j (x) F_p^k), (e, h, z)(e', h', z') = (e + e', h + h', z + z' + e (x) h')."""
    E = list(itertools.product(range(p), repeat=j))
    V = list(itertools.product(range(p), repeat=k))
    Z = list(itertools.product(range(p), repeat=j * k))
    elems = [(e, h, z) for e in E for h in V for z in Z]

    def mul(a, b):
        return (tuple((x + y) % p for x, y in zip(a[0], b[0])),
                tuple((x + y) % p for x, y in zip(a[1], b[1])),
                tuple((a[2][n] + b[2][n] + a[0][n // k] * b[1][n % k]) % p for n in range(j * k)))
    return elems, table_from(elems, mul)


def tensor_design(p, k, rng, sample=200):
    """j = 2, S = {0, e_1, e_2}, K = {(t, h, t (x) h) : t in S}, L = H = {(0, h, 0)}, D = (K^-1 K) x H^(r-1)."""
    j = 2
    elems, T = tensor_heisenberg(p, j, k)
    index = {x: n for n, x in enumerate(elems)}
    inv = inverses(T)
    V = list(itertools.product(range(p), repeat=k))
    zk, zz = tuple([0] * k), tuple([0] * (j * k))
    S = [(0, 0), (1, 0), (0, 1)]
    K = frozenset(index[(t, h, tuple(t[n // k] * h[n % k] % p for n in range(j * k)))] for t in S for h in V)
    H = sorted(index[((0, 0), h, zz)] for h in V)
    diffs = sorted({T[inv[a]][c] for a in K for c in K})
    sdiff = len({tuple((x - y) % p for x, y in zip(s, t)) for s in S for t in S})
    unserved = 0
    for r in (2, 3):
        for _ in range(sample):
            d = (rng.choice(diffs),) + tuple(rng.choice(H) for _ in range(r - 1))
            unserved += not any(cube_in(T, K, A, d) for A in K)
    b, gd = max_class(T), len(commutator_subgroup(T))
    kk, d2, d3 = len(K), len(diffs) * len(H), len(diffs) * len(H) ** 2
    return {"order": len(T), "K": kk, "K^-1K": len(diffs), "b": b, "derived": gd,
            "predicted": [len(S) * p ** k, (sdiff - 1) * p ** (2 * k) + p ** k, p ** (k + j - 1), p ** (j * k)],
            "generates_G": len(generated(T, diffs)) == len(T), "unserved_in_sample": unserved,
            "thm25_b_holds": kk ** 8 * b >= d2 ** 3, "thm29_b_holds": kk ** 24 * b ** 4 >= d3 ** 7,
            "log2_slack_25_b": 8 * math.log2(kk) + math.log2(b) - 3 * math.log2(d2),
            "log2_slack_25_derived": 8 * math.log2(kk) + math.log2(gd) - 3 * math.log2(d2),
            "log2_slack_29_b": 24 * math.log2(kk) + 4 * math.log2(b) - 7 * math.log2(d3),
            "log2_slack_29_derived": 24 * math.log2(kk) + 4 * math.log2(gd) - 7 * math.log2(d3)}


# ---- exploratory: non-commuting laws --------------------------------------------------------

def ratio_sixth(T, law, logb):
    hd = entropy(law, lambda o: o[1:])
    return (cube_sum(T, law) - 7 / 3 * hd) / logb


def local_search(T, rng, restarts, steps):
    n, logb = len(T), math.log2(max_class(T))
    best = (float("inf"), None)
    for _ in range(restarts):
        size = rng.choice((2, 3, 4, 6, 8))
        support = [tuple(rng.randrange(n) for _ in range(4)) for _ in range(size)]
        weights = [rng.random() + 0.05 for _ in support]

        def value(sup, wts):
            s = sum(wts)
            return ratio_sixth(T, [(x / s, o) for x, o in zip(wts, sup)], logb)
        cur = value(support, weights)
        for _ in range(steps):
            sup, wts = list(support), list(weights)
            i = rng.randrange(len(sup))
            if rng.random() < 0.5:
                o = list(sup[i])
                o[rng.randrange(4)] = rng.randrange(n)
                sup[i] = tuple(o)
            else:
                wts[i] *= math.exp(rng.gauss(0, 0.7))
            v = value(sup, wts)
            if v <= cur:
                support, weights, cur = sup, wts, v
        if cur < best[0]:
            s = sum(weights)
            best = (cur, [(round(x / s, 6), o) for x, o in zip(weights, support)])
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    rng, report = random.Random(29), {}
    named = named_groups()

    t29 = {}
    for name in ("S_3", "D_4", "Q_8", "A_4", "S_4", "G(3,1)"):
        T = named[name]
        logd, logb = math.log2(len(commutator_subgroup(T))), math.log2(max_class(T))
        least_d, least_b = float("inf"), float("inf")
        for trial in range(600):
            r = 3 if trial % 4 else 4
            law = commuting_law(T, r, rng, rng.choice((3, 6, 12, 24)))
            least_d = min(least_d, theorem29_slack(T, law, logd))
            least_b = min(least_b, theorem29_slack(T, law, logb))
        t29[name] = {"least_slack_derived": least_d, "least_slack_b": least_b}
        print(f"Theorem 29 {name}: least slack with log|G'| {least_d:.6f}, with log b {least_b:.6f}")
    report["theorem29_random"] = t29

    sets = {}
    for name in ("S_3", "D_4", "Q_8"):
        sets[name] = exhaustive(named[name], rng)
        print(f"Theorem 29'/27 every K in {name}: {sets[name]}")
    report["set_forms"] = sets

    excess = {}
    for p, k in ((2, 1), (2, 2), (2, 3), (3, 1)):
        excess[f"{p},{k}"] = gpk_excess(p, k)
        rows = excess[f"{p},{k}"]["orders"]
        print(f"G({p},{k}) excess: " + ", ".join(f"{s} {rows[s]['excess']:.4f}" for s in ORDERS)
              + f"; all match {all(v['matches'] for v in rows.values())}, peeling holds "
              f"{all(v['peeling_holds'] for v in rows.values())}")
    report["gpk_excess"] = excess

    p28 = {}
    for name in ("S_3", "D_4", "Q_8", "A_4", "S_4"):
        p28[name] = proposition28(named[name], rng)
        print(f"Proposition 28 {name}: {p28[name]}")
    report["proposition28"] = p28

    lp = {}
    for lam in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(1)):
        best, points, dual = peeling_lp(lam)
        expected = (1 - Fraction(4, 7) * lam, 1 + Fraction(2, 7) * lam)
        lp[str(lam)] = {"max_E": str(best), "points": [[str(x), str(y)] for x, y in points],
                        "dual": str(dual), "as_predicted": best == 4 + 2 * lam == dual
                        and points == [expected]}
        print(f"Proposition 30 lambda={lam}: max E = {best}, points {points}, dual {dual}")
    report["proposition30_lp"] = lp

    tensor = {}
    for p, k in ((2, 1), (2, 2), (2, 3), (3, 1)):
        tensor[f"{p},{k}"] = tensor_design(p, k, rng)
        print(f"Proposition 35 p={p} k={k}: {tensor[f'{p},{k}']}")
    report["proposition35_tensor"] = tensor

    explore = {}
    for name in ("S_3", "D_4", "Q_8", "A_4", "S_4", "AGL(1,5)"):
        value, law = local_search(named[name], rng, restarts=40, steps=150)
        explore[name] = {"least_ratio": value, "law": law, "below_minus_4_3": value < -4 / 3 - 1e-9,
                         "above_minus_2": value >= -2 - 1e-9}
        print(f"non-commuting {name}: least (sum H - 7/3 H(d)) / log b = {value:.6f}")
    report["noncommuting_search"] = explore

    with open(os.path.join(args.out_dir, "theorem29.json"), "w") as f:
        json.dump(report, f, indent=1, default=str)


if __name__ == "__main__":
    main()
