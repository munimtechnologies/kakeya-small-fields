# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks that the robust cube bound fails in non-abelian groups (draft for kakeya-small-fields 1.7).

G = AGL(1, q) for a prime q: the maps x -> a x + b with a != 0, of order N = q (q - 1), written
(a, b) and multiplied by composition, (a, b)(c, e) = (a c, a e + b). H = {(a, 0)} fixes 0 and
K = {(a, b) : b in {0, 1}} = H u tH with t = (1, 1), so |K| = 2 (q - 1).

Claim. K contains a left translate of the cube {a d_1^(t_1) ... d_r^(t_r)} of every d in
D = G x H^(r-1), so |D| = q (q - 1)^r and |K| <= 2 |D|^(1/(r+1)). Every group has
|D| <= |K|^(r+1), so the exponent 1/(r+1) is sharp in general, while abelian groups have
|K| >= |D|^((1 - 2^-r)/r).

Reduction used for large q: if KH = K and every g in G is k^(-1) k' with k, k' in K, take
a = k; then a d_1 = k' and the cube points lie in kH u k'H, inside K.

    python frobenius_cubes.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, int(n ** 0.5) + 1))


def mul(q, x, y):
    return (x[0] * y[0] % q, (x[0] * y[1] + x[1]) % q)


def inv(q, x):
    ai = pow(x[0], q - 2, q)
    return (ai, -ai * x[1] % q)


def group(q):
    return [(a, b) for a in range(1, q) for b in range(q)]


def subgroup_h(q):
    return [(a, 0) for a in range(1, q)]


def k_set(q):
    return [(a, b) for a in range(1, q) for b in (0, 1)]


def reduction_holds(q):
    """KH = K and K^(-1) K = G, which together give the cube claim."""
    K = set(k_set(q))
    if any(mul(q, k, h) not in K for k in K for h in subgroup_h(q)):
        return False
    quotients = {mul(q, inv(q, k), k2) for k in K for k2 in K}
    return len(quotients) == q * (q - 1)


def word(q, d, t):
    w = (1, 0)
    for di, ti in zip(d, t):
        if ti:
            w = mul(q, w, di)
    return w


def brute_cover(q, r):
    """Directly: every d in G x H^(r-1) has a translate of its cube inside K."""
    K = set(k_set(q))
    ts = list(itertools.product((0, 1), repeat=r))
    for d in itertools.product(group(q), *[subgroup_h(q)] * (r - 1)):
        ws = [word(q, d, t) for t in ts]
        if not any(all(mul(q, a, w) in K for w in ws) for a in K):
            return False
    return True


def sizes(q, r):
    return 2 * (q - 1), q * (q - 1) ** r


def abelian_bound_fails(q, r):
    """Exact integer test of |K|^(r 2^r) < |D|^(2^r - 1), i.e. |K| < |D|^((1 - 2^-r)/r)."""
    k, dsize = sizes(q, r)
    return k ** (r * 2 ** r) < dsize ** (2 ** r - 1)


def counting_bound_holds(q, r):
    k, dsize = sizes(q, r)
    return dsize <= k ** (r + 1)


def least_failing_prime(r, limit=5000):
    for q in range(3, limit):
        if is_prime(q) and abelian_bound_fails(q, r):
            return q
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"brute": [], "reduction": [], "least_failing_prime": {}, "examples": []}
    for q, r in ((3, 2), (3, 3), (5, 2), (5, 3), (7, 2), (7, 3), (11, 2)):
        ok = brute_cover(q, r)
        out["brute"].append({"q": q, "r": r, "covers": ok})
        print("brute q=%d r=%d" % (q, r), "covers" if ok else "FAILS", flush=True)
    for q in (3, 5, 7, 11, 59, 67, 257):
        ok = reduction_holds(q)
        out["reduction"].append({"q": q, "holds": ok})
        print("reduction q=%d" % q, "holds" if ok else "FAILS", flush=True)
    for r in range(2, 7):
        p = least_failing_prime(r)
        out["least_failing_prime"][r] = p
        print("r=%d least prime q with |K| < |D|^((1-2^-r)/r):" % r, p, flush=True)
    for q, r in ((257, 2), (67, 3), (4099, 2)):
        k, dsize = sizes(q, r)
        out["examples"].append({
            "q": q, "r": r, "K": k, "D": dsize,
            "abelian_bound": dsize ** ((1 - 2 ** -r) / r),
            "exponent": math.log(k) / math.log(dsize),
            "abelian_bound_fails": abelian_bound_fails(q, r),
            "counting_bound_holds": counting_bound_holds(q, r)})
        print("q=%d r=%d |K|=%d |D|^((1-2^-r)/r)=%.2f" % (q, r, k, out["examples"][-1]["abelian_bound"]),
              flush=True)
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "frobenius_cubes.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
