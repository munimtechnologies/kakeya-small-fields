# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for Proposition 15 and Theorem 16 (drafts for kakeya-small-fields 1.7).

lambda*(G) = inf over m, L != 1 in G^m and y in G^m of log|L n yLy^(-1)| / log|L|. Proposition 6(c)
breaks the abelian r-cube exponent in powers of G iff some lambda < (2^r - 1 - r)/(2^r - 1).

Proposition 15. lambda*(G) = inf over m and L != 1 in G^m of log|L n Z(G)^m| / log|L|.
(>=: central elements of L lie in every conjugate. <=: if g_1, ..., g_d generate G^m, the diagonal
copy of L in (G^m)^(d+1) and y = (1, g_1, ..., g_d) give L n yLy^(-1) = diagonal of L n Z(G^m).)

Theorem 16. Let p be odd and G a finite p-group of exponent p^e in which every element of order p is
central. Then every subgroup L satisfies |L| <= |Omega_1(L)|^e, so lambda*(G) >= 1/e. Sharp: in
M(p, e) = Z_(p^e) x| Z_(p^e), y x y^(-1) = x^(1+p), L = <y> and conjugation by x give 1/e.
(Proof uses Xu's theorem: such groups are strongly semi-p-abelian.)

Corollary. The gap of Proposition 14 closes: the generalised quaternion group Q_(2^n) has every
involution central but lambda* <= 1/n (diagonal Q_(2^n) in Q_(2^n)^3), so powers of Q_16 break
r = 2 (Q_16^27) and r = 3 (Q_16^9). For odd p, powers of M(p, 4) break r = 2 (M(3, 4)^6).

    python central_density.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os


# ---- groups given by elements and a multiplication function ------------------------------

def quaternion(n):
    """Q_(2^n) = <a, b | a^(2^(n-1)) = 1, b^2 = a^(2^(n-2)), b a b^(-1) = a^(-1)>, pairs a^i b^j."""
    N, h = 2 ** (n - 1), 2 ** (n - 2)
    elems = [(i, j) for j in range(2) for i in range(N)]

    def mul(u, v):
        i, j = u
        k, l = v
        i2 = (i + (-1) ** j * k) % N
        if j and l:
            i2 = (i2 + h) % N
        return (i2, (j + l) % 2)
    return elems, mul, (0, 0), [(1, 0), (0, 1)]


def metacyclic(p, e):
    """M(p, e) = <x, y | x^(p^e) = y^(p^e) = 1, y x y^(-1) = x^(1+p)>, pairs (i, k) = x^i y^k with
    (i, k)(j, l) = (i + (1+p)^k j, k + l). Order p^(2e); generators x = (1, 0), y = (0, 1)."""
    q = p ** e
    powers = [pow(1 + p, k, q) for k in range(q)]
    elems = [(i, k) for i in range(q) for k in range(q)]

    def mul(u, v):
        return ((u[0] + powers[u[1]] * v[0]) % q, (u[1] + v[1]) % q)
    return elems, mul, (0, 0), [(1, 0), (0, 1)]


def p_group(p):
    """P(p) of run 24: (a, b, c), a, b mod p^2, c mod p, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+b a')."""
    q = p * p
    elems = [(a, b, c) for a in range(q) for b in range(q) for c in range(p)]

    def mul(u, v):
        return ((u[0] + v[0]) % q, (u[1] + v[1]) % q, (u[2] + v[2] + u[1] * v[0]) % p)
    return elems, mul, (0, 0, 0), [(1, 0, 0), (0, 1, 0)]


def direct_power(group, m):
    elems, mul, one, gens = group
    pelems = list(itertools.product(elems, repeat=m))

    def pmul(a, b):
        return tuple(mul(x, y) for x, y in zip(a, b))
    pgens = [tuple(g if c == k else one for c in range(m)) for k in range(m) for g in gens]
    return pelems, pmul, (one,) * m, pgens


def power(mul, one, g, k):
    x = one
    for _ in range(k):
        x = mul(x, g)
    return x


def inverse(mul, one, g):
    x, prev = g, one
    while x != one:
        prev, x = x, mul(x, g)
    return prev


def element_order(mul, one, g):
    k, x = 1, g
    while x != one:
        x = mul(x, g)
        k += 1
    return k


def centre(group):
    elems, mul, _, gens = group
    return frozenset(z for z in elems if all(mul(z, g) == mul(g, z) for g in gens))


# ---- tables for subgroup enumeration (small groups only) ----------------------------------

def table(group):
    elems, mul, one, gens = group
    index = {x: n for n, x in enumerate(elems)}
    T = [[index[mul(a, b)] for b in elems] for a in elems]
    return T, index[one], [index[g] for g in gens]


def closure(T, start, gens):
    S = set(start)
    frontier = list(S)
    while frontier:
        new = []
        for x in frontier:
            row = T[x]
            for g in gens:
                y = row[g]
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return frozenset(S)


def all_subgroups(T, one):
    """Every subgroup, by adjoining one element at a time; one closure per left coset gS."""
    n = len(T)
    trivial = frozenset([one])
    gens = {trivial: []}
    stack = [trivial]
    while stack:
        S = stack.pop()
        seen = set(S)
        for g in range(n):
            if g in seen:
                continue
            seen.update(T[g][s] for s in S)
            U = closure(T, S, gens[S] + [g])
            if U not in gens:
                gens[U] = gens[S] + [g]
                stack.append(U)
    return list(gens)


def omega_bound_summary(group, p, k):
    """Over all subgroups L: does |L| <= |Omega_1(L)|^k hold, and the least log|Omega_1(L)|/log|L|.
    Omega_1(L) is counted as the set of elements of order 1 or p (a subgroup in these groups)."""
    elems, mul, one, _ = group
    T, i1, _ = table(group)
    small = frozenset(n for n, g in enumerate(elems) if element_order(mul, one, g) in (1, p))
    Z = {elems.index(z) for z in centre(group)}
    rows = [(len(L), len(L & small)) for L in all_subgroups(T, i1)]
    nontrivial = [(s, w) for s, w in rows if s > 1]
    return {
        "order": len(elems),
        "subgroups": len(rows),
        "order_p_central": small <= Z,
        "bound_holds": all(w ** k >= s for s, w in rows),
        "equality_cases": sorted({(s, w) for s, w in nontrivial if w ** k == s and w < s}),
        "least_ratio": min(math.log(w) / math.log(s) for s, w in nontrivial),
    }


# ---- Proposition 15: the diagonal trick ---------------------------------------------------

def diagonal_intersection(group, L):
    """Diagonal copy of L in G^(d+1), y = (1, g_1, ..., g_d). Returns |L n yLy^(-1)| there."""
    _, mul, one, gens = group
    ginv = [inverse(mul, one, g) for g in gens]
    # (z, g_1 z g_1^-1, ...) with z in L is diagonal iff z commutes with every generator
    return sum(1 for z in L if all(mul(mul(g, z), gi) == z for g, gi in zip(gens, ginv)))


def subgroup_from(group, gens):
    _, mul, one, _ = group
    S, frontier = {one}, [one]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return frozenset(S)


def diagonal_matches_centre(group):
    """For every subgroup L (by enumeration): diagonal |I| equals |L n Z(G)|."""
    elems, _, one, _ = group
    T, i1, _ = table(group)
    Z = centre(group)
    for Lidx in all_subgroups(T, i1):
        L = frozenset(elems[n] for n in Lidx)
        if diagonal_intersection(group, L) != len(L & Z):
            return False
    return True


# ---- the sharp examples -------------------------------------------------------------------

def metacyclic_example(p, e):
    """L = <y> in M(p, e), conjugated by x: returns (|L|, |L n xLx^(-1)|)."""
    group = metacyclic(p, e)
    _, mul, one, (x, y) = group
    L = subgroup_from(group, [y])
    xi = inverse(mul, one, x)
    return len(L), sum(1 for z in L if mul(mul(x, z), xi) in L)


def quaternion_diagonal(n):
    """Diagonal Q_(2^n) in Q_(2^n)^3, y = (1, a, b): returns (|L|, |I|)."""
    group = quaternion(n)
    return len(group[0]), diagonal_intersection(group, frozenset(group[0]))


def abelian_bound_fails_sizes(ksize, dsize, r):
    """Exact integer test of |K|^(r 2^r) < |D|^(2^r - 1), i.e. |K| < |D|^((1 - 2^-r)/r)."""
    return ksize ** (r * 2 ** r) < dsize ** (2 ** r - 1)


def least_power(lsize, isize, r, limit=200):
    """Least m with 2 |L|^m < (|L|^(r+1)/|I|)^(m (1 - 2^-r)/r) (Proposition 6(c)), exact integers."""
    unit = lsize ** (r + 1) // isize
    for m in range(1, limit):
        if abelian_bound_fails_sizes(2 * lsize ** m, unit ** m, r):
            return m
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"theorem16": {}, "p2_question": {}, "prop15": {}, "examples": {}, "least_power": {}}
    for name, group, p, e in (("M(3,2)", metacyclic(3, 2), 3, 2), ("M(5,2)", metacyclic(5, 2), 5, 2),
                              ("M(3,3)", metacyclic(3, 3), 3, 3), ("P(3)", p_group(3), 3, 2)):
        out["theorem16"][name] = omega_bound_summary(group, p, e)
        print("Theorem 16", name, out["theorem16"][name], flush=True)
    # p = 2 is open: is |L| <= |Omega_1(L)|^(e+1) when every involution is central? (reported only)
    for name, group, e in (("Q16", quaternion(4), 3), ("Q32", quaternion(5), 4),
                           ("Q8xQ8", direct_power(quaternion(3), 2), 2),
                           ("Q16xQ8", None, 3)):
        if group is None:
            q16, q8 = quaternion(4), quaternion(3)
            elems = [(a, b) for a in q16[0] for b in q8[0]]
            group = (elems, lambda u, v: (q16[1](u[0], v[0]), q8[1](u[1], v[1])), ((0, 0), (0, 0)),
                     [((1, 0), (0, 0)), ((0, 1), (0, 0)), ((0, 0), (1, 0)), ((0, 0), (0, 1))])
        out["p2_question"][name] = omega_bound_summary(group, 2, e + 1)
        print("p = 2, exponent e + 1 =", e + 1, name, out["p2_question"][name], flush=True)
    for name, group in (("Q8", quaternion(3)), ("Q16", quaternion(4)), ("M(3,2)", metacyclic(3, 2))):
        out["prop15"][name] = diagonal_matches_centre(group)
        print("Proposition 15 diagonal = centre on every subgroup of", name, out["prop15"][name], flush=True)
    for n in (3, 4, 5, 6):
        out["examples"]["Q%d diagonal" % 2 ** n] = quaternion_diagonal(n)
        print("Q_%d diagonal (|L|, |I|) =" % 2 ** n, out["examples"]["Q%d diagonal" % 2 ** n], flush=True)
    for p, e in ((3, 2), (3, 3), (3, 4), (5, 4), (7, 3)):
        out["examples"]["M(%d,%d) <y>" % (p, e)] = metacyclic_example(p, e)
        print("M(%d,%d), L = <y> (|L|, |I|) =" % (p, e), out["examples"]["M(%d,%d) <y>" % (p, e)], flush=True)
    out["least_power"]["Q16 diagonal"] = {r: least_power(16, 2, r) for r in (2, 3, 4)}
    for p in (3, 5, 7):
        out["least_power"]["M(%d,4)" % p] = {r: least_power(p ** 4, p, r) for r in (2, 3, 4)}
    print("least powers", out["least_power"], flush=True)
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "central_density.json"), "w") as f:
        json.dump(out, f, indent=1, default=str)


if __name__ == "__main__":
    main()
