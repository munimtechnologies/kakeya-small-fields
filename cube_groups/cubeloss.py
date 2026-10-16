# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for Theorem 25 (draft for kakeya-small-fields 1.7; notes/robust-cubes-v5k.md).

Theorem 25 (r = 2). Let G be a finite group with derived subgroup G'. For any random (A, d_1, d_2)
with Y_00 = A, Y_10 = A d_1, Y_01 = A d_2, Y_11 = A d_1 d_2, c = d_2^(-1) d_1 d_2 and
z = [d_1, d_2] = d_1^(-1) d_2^(-1) d_1 d_2,

    sum_t H(Y_t) >= H(d) + max(H(d_2), I(d_1 ; c)) >= (3/2) H(d) - (1/2) H(z | c).

Hence if K contains a left translate of the 2-cube {A, A d_1, A d_2, A d_1 d_2} of every pair in D,

    |K|^8 |G'| >= |D|^3.

Sharp up to a factor 2 in |K| for G(p, k) (every k) and AGL(1, q): the exponent 1/8 on |G'| is best
possible. Theorem 9' gave |G'|^6 in place of |G'|. For general r the same peeling, averaged over
orders, loses l_r = 2^r - 1 - sum_(k=1..r) (2^k - 1)/k pairs (l_2 = 1/2, l_3 = 13/6).

    python cubeloss.py --out-dir OUT
"""
import argparse
import itertools
import json
import os
import random
from fractions import Fraction
from math import log2


# ---- groups given by elements, a multiplication function, identity and generators ---------

def perm_group(gens):
    n = len(gens[0])
    return None, (lambda a, b: tuple(a[b[i]] for i in range(n))), tuple(range(n)), gens


def quaternion8():
    def mul(p, q):
        a1, b1, c1, d1 = p
        a2, b2, c2, d2 = q
        return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
                a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)
    return None, mul, (1, 0, 0, 0), [(0, 1, 0, 0), (0, 0, 1, 0)]


def gpk(p, k):
    """G(p, k): (e, h, z), e in Z_p, h, z in F_p^k, (e, h, z)(e', h', z') = (e+e', h+h', z+z'+e h')."""
    elems = [(e, h, z) for e in range(p) for h in itertools.product(range(p), repeat=k)
             for z in itertools.product(range(p), repeat=k)]

    def mul(u, v):
        e, h, z = u
        e2, h2, z2 = v
        return ((e + e2) % p, tuple((x + y) % p for x, y in zip(h, h2)),
                tuple((x + y + e * w) % p for x, y, w in zip(z, z2, h2)))
    return elems, mul, elems[0], None


def agl1(q):
    """AGL(1, q), q prime: (a, b) is x -> a x + b; (a, b)(c, e) = (a c, a e + b)."""
    elems = [(a, b) for a in range(1, q) for b in range(q)]
    return elems, (lambda u, v: (u[0] * v[0] % q, (u[0] * v[1] + u[1]) % q)), (1, 0), None


class Table:
    def __init__(self, spec):
        elems, mul, one, gens = spec
        if elems is None:
            elems = closure(gens, mul, one)
        self.el = list(elems)
        self.idx = {g: i for i, g in enumerate(self.el)}
        self.n = n = len(self.el)
        self.t = [[self.idx[mul(a, b)] for b in self.el] for a in self.el]
        self.e = self.idx[one]
        self.inv = [self.t[i].index(self.e) for i in range(n)]

    def comm(self, a, b):
        t, inv = self.t, self.inv
        return t[t[t[inv[a]][inv[b]]][a]][b]

    def derived_order(self):
        H = {self.comm(a, b) for a in range(self.n) for b in range(self.n)}
        while True:
            new = {self.t[a][b] for a in H for b in H}
            if new <= H:
                return len(H)
            H |= new


def closure(gens, mul, one):
    S = {one, *gens}
    while True:
        new = {mul(a, b) for a in S for b in S} - S
        if not new:
            return sorted(S)
        S |= new


def d_max(G, K):
    """All (g, h) whose 2-cube has a left translate {A, A g, A h, A g h} inside K."""
    t, Ks, D = G.t, set(K), set()
    for A in K:
        S = [g for g in range(G.n) if t[A][g] in Ks]
        for g in S:
            Ag = t[A][g]
            for h in S:
                if t[Ag][h] in Ks:
                    D.add((g, h))
    return D


def exhaustive(G):
    """Every nonempty K: check |K|^8 |G'| >= |D_max(K)|^3; report the least ratios."""
    g = G.derived_order()
    worst, worst_abelian = None, None
    for mask in range(1, 2 ** G.n):
        K = [i for i in range(G.n) if mask >> i & 1]
        D = len(d_max(G, K))
        r = Fraction(len(K) ** 8 * g, D ** 3)
        ra = Fraction(len(K) ** 8, D ** 3)
        if worst is None or r < worst[0]:
            worst = (r, len(K), D)
        if worst_abelian is None or ra < worst_abelian[0]:
            worst_abelian = (ra, len(K), D)
    return g, worst, worst_abelian


# ---- entropy form --------------------------------------------------------------------------

def H(dist):
    tot = sum(dist.values())
    return -sum(w / tot * log2(w / tot) for w in dist.values() if w)


def marg(joint, f):
    out = {}
    for x, w in joint.items():
        k = f(x)
        out[k] = out.get(k, 0) + w
    return out


def entropy_sides(G, joint):
    """joint: {(A, d1, d2): weight}. Returns (S, H(d), H(d_2), I(d_1; c), H(z | c))."""
    t, inv = G.t, G.inv
    S = sum(H(marg(joint, f)) for f in (lambda x: x[0], lambda x: t[x[0]][x[1]],
                                        lambda x: t[x[0]][x[2]], lambda x: t[t[x[0]][x[1]]][x[2]]))
    c = lambda x: t[t[inv[x[2]]][x[1]]][x[2]]
    z = lambda x: G.comm(x[1], x[2])
    Hd = H(marg(joint, lambda x: (x[1], x[2])))
    Hd2 = H(marg(joint, lambda x: x[2]))
    I = (H(marg(joint, lambda x: x[1])) + H(marg(joint, c))
         - H(marg(joint, lambda x: (x[1], c(x)))))
    Hzc = H(marg(joint, lambda x: (z(x), c(x)))) - H(marg(joint, c))
    return S, Hd, Hd2, I, Hzc


def random_joint(G, rng, size):
    return {(rng.randrange(G.n), rng.randrange(G.n), rng.randrange(G.n)): rng.randint(1, 9)
            for _ in range(size)}


def l_r(r):
    return 2 ** r - 1 - sum(Fraction(2 ** k - 1, k) for k in range(1, r + 1))


SMALL = {
    "S3": perm_group([(1, 0, 2), (1, 2, 0)]),
    "Z4xZ2": perm_group([(1, 2, 3, 0, 4, 5), (0, 1, 2, 3, 5, 4)]),
    "D4": perm_group([(1, 2, 3, 0), (0, 3, 2, 1)]),
    "Q8": quaternion8(),
    "A4": perm_group([(1, 2, 0, 3), (0, 2, 3, 1)]),
    "D6": perm_group([(1, 2, 3, 4, 5, 0), (0, 5, 4, 3, 2, 1)]),
}


def construction_gpk(p, k, s):
    """Proposition 6(b): K = {(t, h, t h) : t in S}, D = (G minus HZ) x H. Returns |K|, |D|, |D_max|."""
    G = Table(gpk(p, k))
    K = [G.idx[(t, h, tuple(t * x % p for x in h))] for t in s
         for h in itertools.product(range(p), repeat=k)]
    zero = tuple([0] * k)
    D = {(G.idx[(e, h, z)], G.idx[(0, h2, zero)]) for (e, h, z) in G.el if e
         for h2 in itertools.product(range(p), repeat=k)}
    Dm = d_max(G, K)
    return G, K, D, Dm


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    res = {"exhaustive": {}, "gpk": {}, "agl": {}, "entropy_min_slack": {}, "l_r": {}}
    for name, spec in SMALL.items():
        G = Table(spec)
        g, w, wa = exhaustive(G)
        res["exhaustive"][name] = {"order": G.n, "derived": g, "least_ratio": str(w[0]),
                                   "at_K_D": w[1:], "least_ratio_without_G'": str(wa[0]),
                                   "abelian_exponent_fails": wa[0] < 1}
    for p, k, s in [(2, 1, (0, 1)), (2, 2, (0, 1)), (3, 1, (0, 1)), (2, 3, (0, 1))]:
        G, K, D, Dm = construction_gpk(p, k, s)
        g = G.derived_order()
        res["gpk"]["%d,%d" % (p, k)] = {"K": len(K), "D": len(D), "D_max": len(Dm),
                                        "derived": g, "served": D <= Dm,
                                        "ratio_D": str(Fraction(len(K) ** 8 * g, len(D) ** 3)),
                                        "ratio_D_max": str(Fraction(len(K) ** 8 * g, len(Dm) ** 3))}
    for q in (5, 7, 11):
        G = Table(agl1(q))
        K = [G.idx[(a, b)] for a in range(1, q) for b in (0, 1)]
        Dm = d_max(G, K)
        g = G.derived_order()
        res["agl"][q] = {"K": len(K), "D_max": len(Dm), "derived": g,
                         "ratio_D_max": str(Fraction(len(K) ** 8 * g, len(Dm) ** 3))}
    rng = random.Random(2026)
    for name in ("S3", "D4", "Q8", "A4"):
        G = Table(SMALL[name])
        slack = None
        for _ in range(3000):
            S, Hd, Hd2, I, Hzc = entropy_sides(G, random_joint(G, rng, rng.randint(1, 40)))
            v = S - (Hd + max(Hd2, I))
            slack = v if slack is None else min(slack, v)
        res["entropy_min_slack"][name] = slack
    res["l_r"] = {r: str(l_r(r)) for r in range(1, 7)}
    with open(os.path.join(args.out_dir, "cubeloss.json"), "w") as f:
        json.dump(res, f, indent=1, default=str)
    print(json.dumps(res, indent=1, default=str))


if __name__ == "__main__":
    main()
