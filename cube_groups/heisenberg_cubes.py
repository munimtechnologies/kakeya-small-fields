# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks that the robust cube bound fails already in nilpotent groups of class 2 (draft for
kakeya-small-fields 1.7).

G(p, k) for a prime p and k >= 1: triples (e, h, z) with e in Z_p and h, z in F_p^k, multiplied by

    (e, h, z)(e', h', z') = (e + e', h + h', z + z' + e h').

It has order p^(2k+1), centre and derived subgroup Z = {(0, 0, z)}, and class 2 (k = 1 is the
Heisenberg group mod p; p = 2, k = 1 is the dihedral group of order 8). H = {(0, h, 0)}.
For S in Z_p with S - S = Z_p let K = {(t, h, t h) : t in S} = union of the cosets x^t H with
x = (1, 0, 0), so |K| = |S| p^k.

Claim. K contains a left translate of the cube {a d_1^(t_1) ... d_r^(t_r)} of every d in
D = (G minus HZ) x H^(r-1), so |D| = (p - 1) p^(k(r+1)) and |K| = |S| p^k. For fixed p and r >= 2
this beats the abelian bound |K| >= |D|^((1 - 2^-r)/r) once k is large.

Reduction used for large k: if KH = K and every g outside HZ is k^(-1) k' with k, k' in K, take
a = k; then a d_1 = k' and the cube points lie in kH u k'H, inside K.

The second half checks Proposition 6 on direct powers: for a subgroup L, an element y with
L^y != L and I = L n y L y^(-1), K = L u yL serves D = LyL x L^(r-1).

    python heisenberg_cubes.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os


# ---- G(p, k) -------------------------------------------------------------------------------

def mul(p, x, y):
    e, h, z = x
    e2, h2, z2 = y
    return ((e + e2) % p,
            tuple((a + b) % p for a, b in zip(h, h2)),
            tuple((a + b + e * c) % p for a, b, c in zip(z, z2, h2)))


def inv(p, x):
    e, h, z = x
    return (-e % p, tuple(-a % p for a in h), tuple((-a + e * b) % p for a, b in zip(z, h)))


def identity(k):
    return (0, (0,) * k, (0,) * k)


def vectors(p, k):
    return list(itertools.product(range(p), repeat=k))


def group(p, k):
    V = vectors(p, k)
    return [(e, h, z) for e in range(p) for h in V for z in V]


def subgroup_h(p, k):
    return [(0, h, (0,) * k) for h in vectors(p, k)]


def difference_cover(p):
    """A smallest S in Z_p containing 0 with S - S = Z_p (exhaustive; fine for p <= 13)."""
    for s in range(1, p + 1):
        for rest in itertools.combinations(range(1, p), s - 1):
            S = (0,) + rest
            if len({(a - b) % p for a in S for b in S}) == p:
                return S
    return None


def k_set(p, k, S):
    return [(t, h, tuple(t * a % p for a in h)) for t in S for h in vectors(p, k)]


def reduction_holds(p, k, S):
    """KH = K and K^(-1) K contains every element with e != 0, which give the cube claim."""
    K = set(k_set(p, k, S))
    if any(mul(p, a, h) not in K for a in K for h in subgroup_h(p, k)):
        return False
    quotients = {mul(p, ai, b) for ai in [inv(p, a) for a in K] for b in K}
    return sum(1 for g in quotients if g[0]) == (p - 1) * p ** (2 * k)


def word(mulf, one, d, t):
    w = one
    for di, ti in zip(d, t):
        if ti:
            w = mulf(w, di)
    return w


def brute_cover_generic(mulf, one, K, D, r):
    """Directly: every d in D has a left translate a * cube(d) inside K with a in K."""
    K = set(K)
    ts = list(itertools.product((0, 1), repeat=r))
    for d in D:
        ws = [word(mulf, one, d, t) for t in ts]
        if not any(all(mulf(a, w) in K for w in ws) for a in K):
            return False
    return True


def brute_cover(p, k, r, S):
    outside = [g for g in group(p, k) if g[0]]
    D = itertools.product(outside, *[subgroup_h(p, k)] * (r - 1))
    return brute_cover_generic(lambda x, y: mul(p, x, y), identity(k), k_set(p, k, S), D, r)


def sizes(p, k, r, s):
    return s * p ** k, (p - 1) * p ** (k * (r + 1))


def abelian_bound_fails_sizes(ksize, dsize, r):
    """Exact integer test of |K|^(r 2^r) < |D|^(2^r - 1), i.e. |K| < |D|^((1 - 2^-r)/r)."""
    return ksize ** (r * 2 ** r) < dsize ** (2 ** r - 1)


def abelian_bound_fails(p, k, r, s):
    return abelian_bound_fails_sizes(*sizes(p, k, r, s), r)


def least_k(p, r, s, limit=60):
    for k in range(1, limit):
        if abelian_bound_fails(p, k, r, s):
            return k
    return None


def derived_bound_holds(ksize, dsize, g, r):
    """Theorem 9': |K| >= (|D|^(1/r) / |G'|)^(1 - 2^-r), as |K|^(r 2^r) g^(r(2^r-1)) >= |D|^(2^r-1)."""
    return ksize ** (r * 2 ** r) * g ** (r * (2 ** r - 1)) >= dsize ** (2 ** r - 1)


# ---- Proposition 6: direct powers of a non-Dedekind group ----------------------------------

def s3_mul(x, y):
    return tuple(x[i] for i in y)


Q8_TABLE = {(1, 1): (-1, 0), (2, 2): (-1, 0), (3, 3): (-1, 0),
            (1, 2): (1, 3), (2, 3): (1, 1), (3, 1): (1, 2),
            (2, 1): (-1, 3), (3, 2): (-1, 1), (1, 3): (-1, 2)}


def q8_mul(x, y):
    """Quaternion units as (sign, unit) with unit 0, 1, 2, 3 for 1, i, j, k."""
    (s, a), (t, b) = x, y
    if a == 0:
        return (s * t, b)
    if b == 0:
        return (s * t, a)
    u, c = Q8_TABLE[(a, b)]
    return (s * t * u, c)


def power_mul(mulf):
    return lambda x, y: tuple(mulf(a, b) for a, b in zip(x, y))


def closure(mulf, gens, one):
    S = {one}
    frontier = [one]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mulf(x, g)
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return sorted(S)


def prop6_instance(mulf, invf, one, L, y, r):
    """Returns (|K|, |D|, |I|, covers) for K = L u yL and D = LyL x L^(r-1)."""
    L = list(L)
    I = set(L) & {mulf(mulf(y, l), invf(y)) for l in L}
    LyL = {mulf(mulf(a, y), b) for a in L for b in L}
    K = set(L) | {mulf(y, l) for l in L}
    D = list(itertools.product(sorted(LyL), *[L] * (r - 1)))
    return len(K), len(D), len(I), brute_cover_generic(mulf, one, K, D, r)


def least_power(lsize, isize, r, limit=200):
    """Least m with 2 |L|^m < (|L|^(r+1)/|I|)^(m (1 - 2^-r)/r) in G^m, exact integers."""
    unit = lsize ** (r + 1) // isize
    for m in range(1, limit):
        if abelian_bound_fails_sizes(2 * lsize ** m, unit ** m, r):
            return m
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"covers": {}, "brute": [], "reduction": [], "least_k": {}, "examples": [], "prop6": []}
    for p in (2, 3, 5, 7, 11, 13):
        out["covers"][p] = difference_cover(p)
    for p, k, r in ((2, 1, 2), (2, 2, 2), (2, 2, 3), (2, 3, 2), (3, 1, 2), (3, 2, 2), (3, 2, 3),
                    (5, 1, 2), (7, 1, 2)):
        ok = brute_cover(p, k, r, difference_cover(p))
        out["brute"].append({"p": p, "k": k, "r": r, "covers": ok})
        print("brute p=%d k=%d r=%d" % (p, k, r), "covers" if ok else "FAILS", flush=True)
    for p, k in ((2, 9), (3, 3), (3, 4), (5, 3), (7, 2)):
        ok = reduction_holds(p, k, difference_cover(p))
        out["reduction"].append({"p": p, "k": k, "holds": ok})
        print("reduction p=%d k=%d" % (p, k), "holds" if ok else "FAILS", flush=True)
    for p in (2, 3, 5, 7, 11, 13):
        s = len(difference_cover(p))
        for r in range(2, 6):
            out["least_k"]["%d,%d" % (p, r)] = least_k(p, r, s)
            print("p=%d r=%d |S|=%d least k:" % (p, r, s), out["least_k"]["%d,%d" % (p, r)], flush=True)
    for p, k, r in ((2, 9, 2), (3, 4, 2), (7, 2, 2), (3, 3, 3), (2, 6, 4)):
        s = len(difference_cover(p))
        ks, ds = sizes(p, k, r, s)
        out["examples"].append({
            "p": p, "k": k, "r": r, "group_order": p ** (2 * k + 1), "K": ks, "D": ds,
            "abelian_bound": ds ** ((1 - 2 ** -r) / r), "exponent": math.log(ks) / math.log(ds),
            "abelian_bound_fails": abelian_bound_fails(p, k, r, s),
            "counting_bound_holds": ds <= ks ** (r + 1),
            "derived_bound_holds": derived_bound_holds(ks, ds, p ** k, r)})
        print("p=%d k=%d r=%d |K|=%d |D|^((1-2^-r)/r)=%.2f" % (p, k, r, ks, out["examples"][-1]["abelian_bound"]),
              flush=True)
    s3_inv = lambda x: tuple(sorted(range(3), key=lambda i: x[i]))
    q8_inv = lambda x: (x[0], 0) if x[1] == 0 else (-x[0], x[1])
    for name, mulf, invf, one, L, y, r in (
            ("S3", s3_mul, s3_inv, (0, 1, 2), [(0, 1, 2), (1, 0, 2)], (2, 1, 0), 2),
            ("Q8xQ8", power_mul(q8_mul), lambda x: tuple(q8_inv(a) for a in x), ((1, 0), (1, 0)),
             closure(power_mul(q8_mul), [((1, 1), (1, 2))], ((1, 0), (1, 0))), ((1, 2), (1, 0)), 3)):
        ks, ds, isz, ok = prop6_instance(mulf, invf, one, L, y, r)
        m = least_power(len(L), isz, r)
        out["prop6"].append({"group": name, "r": r, "L": len(L), "I": isz, "K": ks, "D": ds,
                             "covers": ok, "least_power": m})
        print("prop6 %s r=%d |L|=%d |I|=%d covers=%s least m=%s" % (name, r, len(L), isz, ok, m), flush=True)
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "heisenberg_cubes.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
