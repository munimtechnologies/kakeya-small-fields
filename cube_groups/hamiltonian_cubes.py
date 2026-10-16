# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for Lemma 11 (draft for kakeya-small-fields 1.7): Hamiltonian groups and the 3/8 exponent.

Lemma 11. Let G = Q_8^m x A with A abelian (every Hamiltonian group and every direct power of one
has this form) and Z = Z(G). Every subgroup L of G has |L n Z|^3 >= |L|, so
|L n yLy^(-1)| >= |L|^(1/3) for every y. Hence Proposition 6(a) (K = L u yL, D = LyL x L^(r-1))
never beats the abelian bound |K| >= |D|^(3/8) for r = 2 in these groups.

Proof idea: the squares of L are central, and their {+-1}^m parts span the supports of the elements
of U = LZ/Z inside (F_2^2)^m. A support is the zero pattern of degree-2 functions on U whose only
common zero is 0, so Chevalley-Warning gives dim span >= dim U / 2.

The bound is attained: in Q_8^3 the diagonal copy L of Q_8 and y = (i, j, 1) give |L| = 8 and
L n yLy^(-1) = {+-(1, 1, 1)}. Direct powers of this example break the abelian bound for r = 3 from
Q_8^15 and for r = 4 from Q_8^12.

The script also checks Theorem 9 for r = 2 exhaustively in Q_8 and Q_8 x Z_2 (every set K), and
the lemma on every subgroup of Q_8^2 and every 2-generated subgroup of Q_8^3.

    python hamiltonian_cubes.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os


# ---- Q_8 and its powers --------------------------------------------------------------------

Q8_TABLE = {(1, 1): (-1, 0), (2, 2): (-1, 0), (3, 3): (-1, 0),
            (1, 2): (1, 3), (2, 3): (1, 1), (3, 1): (1, 2),
            (2, 1): (-1, 3), (3, 2): (-1, 1), (1, 3): (-1, 2)}


def q8_mul_pair(x, y):
    """Quaternion units as (sign, unit) with unit 0, 1, 2, 3 for 1, i, j, k."""
    (s, a), (t, b) = x, y
    if a == 0:
        return (s * t, b)
    if b == 0:
        return (s * t, a)
    u, c = Q8_TABLE[(a, b)]
    return (s * t * u, c)


# Index n in 0..7: unit n % 4, sign - when n >= 4. So 0 is 1, 4 is -1, 1, 2, 3 are i, j, k.
Q8_ELEMS = [(s, u) for s in (1, -1) for u in range(4)]
Q8_INDEX = {x: n for n, x in enumerate(Q8_ELEMS)}
Q8 = [[Q8_INDEX[q8_mul_pair(a, b)] for b in Q8_ELEMS] for a in Q8_ELEMS]
I_, J_, K_ = 1, 2, 3


def q8_inv(n):
    return n if n % 4 == 0 else n ^ 4


def pmul(x, y):
    return tuple(Q8[a][b] for a, b in zip(x, y))


def pinv(x):
    return tuple(q8_inv(a) for a in x)


def is_central(x):
    return all(a % 4 == 0 for a in x)


def closure(gens, one):
    S = {one}
    frontier = [one]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = pmul(x, g)
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return frozenset(S)


def all_subgroups(m):
    """Every subgroup of Q_8^m, found by adjoining one element at a time (fine for m <= 2)."""
    one = (0,) * m
    G = list(itertools.product(range(8), repeat=m))
    trivial = frozenset([one])
    gens = {trivial: []}
    stack = [trivial]
    while stack:
        S = stack.pop()
        for g in G:
            if g in S:
                continue
            T = closure(gens[S] + [g], one)
            if T not in gens:
                gens[T] = gens[S] + [g]
                stack.append(T)
    return list(gens)


def two_generated_subgroups(m):
    one = (0,) * m
    G = list(itertools.product(range(8), repeat=m))
    found = set()
    for n, a in enumerate(G):
        for b in G[n:]:
            found.add(closure([a, b], one))
    return list(found)


# ---- Lemma 11 ------------------------------------------------------------------------------

def lemma_data(L, m):
    """(|L|, |L n Z|, least |L n y^(-1) L y| over y) in Q_8^m; y runs over G/Z."""
    centre = sum(1 for x in L if is_central(x))
    least = len(L)
    for y in itertools.product(range(4), repeat=m):
        yi = pinv(y)
        least = min(least, sum(1 for x in L if pmul(pmul(y, x), yi) in L))
    return len(L), centre, least


def lemma_summary(subgroups, m):
    rows = [lemma_data(L, m) for L in subgroups]
    nontrivial = [row for row in rows if row[0] > 1]
    return {
        "subgroups": len(rows),
        "centre_bound_holds": all(c ** 3 >= n for n, c, _ in rows),
        "intersection_bound_holds": all(i ** 3 >= n for n, _, i in rows),
        "non_normal_equality_cases": sorted({(n, i) for n, _, i in nontrivial if i ** 3 == n and i < n}),
        "least_exponent": min(math.log(i) / math.log(n) for n, _, i in nontrivial),
    }


# ---- Proposition 6(a) on the diagonal example ------------------------------------------------

def word(d, t, one):
    w = one
    for di, ti in zip(d, t):
        if ti:
            w = pmul(w, di)
    return w


def covers(K, D, r, one):
    """Directly: every d in D has a left translate a * cube(d) inside K with a in K."""
    K = set(K)
    ts = list(itertools.product((0, 1), repeat=r))
    for d in D:
        ws = [word(d, t, one) for t in ts]
        if not any(all(pmul(a, w) in K for w in ws) for a in K):
            return False
    return True


def prop6_instance(L, y, r):
    """Returns (|K|, |D|, |I|, covers) for K = L u yL and D = LyL x L^(r-1)."""
    one = (0,) * len(y)
    L = sorted(L)
    yi = pinv(y)
    I = set(L) & {pmul(pmul(y, x), yi) for x in L}
    LyL = {pmul(pmul(a, y), b) for a in L for b in L}
    K = set(L) | {pmul(y, x) for x in L}
    D = itertools.product(sorted(LyL), *[L] * (r - 1))
    return len(K), len(LyL) * len(L) ** (r - 1), len(I), covers(K, D, r, one)


def diagonal_example():
    """The diagonal Q_8 in Q_8^3 and y = (i, j, 1)."""
    return closure([(I_, I_, I_), (J_, J_, J_)], (0, 0, 0)), (I_, J_, 0)


def abelian_bound_fails_sizes(ksize, dsize, r):
    """Exact integer test of |K|^(r 2^r) < |D|^(2^r - 1), i.e. |K| < |D|^((1 - 2^-r)/r)."""
    return ksize ** (r * 2 ** r) < dsize ** (2 ** r - 1)


def least_power(lsize, isize, r, limit=200):
    """Least m with 2 |L|^m < (|L|^(r+1)/|I|)^(m (1 - 2^-r)/r) in G^m, exact integers."""
    unit = lsize ** (r + 1) // isize
    for m in range(1, limit):
        if abelian_bound_fails_sizes(2 * lsize ** m, unit ** m, r):
            return m
    return None


# ---- Theorem 9 for r = 2, every K, in small Hamiltonian groups ------------------------------

def q8_z2_table():
    """Q_8 x Z_2 with element q + 8 e."""
    return [[Q8[a % 8][b % 8] + 8 * ((a // 8 + b // 8) % 2) for b in range(16)] for a in range(16)]


def served_pairs(table, K):
    """|D_max(K)|: the pairs (d_1, d_2) with a, a d_1, a d_2, a d_1 d_2 in K for some a."""
    n = len(table)
    inK = [False] * n
    for x in K:
        inK[x] = True
    pairs = set()
    for a in K:
        row = table[a]
        ds = [d for d in range(n) if inK[row[d]]]
        for d1 in ds:
            r1 = table[row[d1]]
            for d2 in ds:
                if inK[r1[d2]]:
                    pairs.add(d1 * n + d2)
    return len(pairs)


def theorem9_r2_exhaustive(table):
    """|K|^8 >= |D_max(K)|^3 for every K containing the identity 0 (left translates of K have
    the same D_max, so this covers every K)."""
    n = len(table)
    worst = None
    violations = 0
    checked = 0
    for mask in range(1 << (n - 1)):
        K = [0] + [x + 1 for x in range(n - 1) if mask >> x & 1]
        dsize = served_pairs(table, K)
        checked += 1
        if len(K) ** 8 < dsize ** 3:
            violations += 1
        if dsize > 1:
            e = math.log(len(K)) / math.log(dsize)
            if worst is None or e < worst[0]:
                worst = (e, len(K), dsize)
    return {"sets": checked, "violations": violations, "least_exponent": worst}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"diagonal": {}, "least_power": {}, "theorem9_r2": {}, "lemma": {}}
    L, y = diagonal_example()
    for r in (2, 3):
        ks, ds, isz, ok = prop6_instance(L, y, r)
        out["diagonal"][r] = {"L": len(L), "I": isz, "K": ks, "D": ds, "covers": ok}
        print("diagonal r=%d |L|=%d |I|=%d |K|=%d |D|=%d covers=%s" % (r, len(L), isz, ks, ds, ok), flush=True)
    isz = out["diagonal"][2]["I"]
    for r in range(2, 7):
        m = least_power(len(L), isz, r)
        out["least_power"][r] = {"m": m, "group": None if m is None else "Q_8^%d" % (3 * m)}
        print("r=%d least power:" % r, out["least_power"][r], flush=True)
    for name, table in (("Q8", Q8), ("Q8xZ2", q8_z2_table())):
        out["theorem9_r2"][name] = theorem9_r2_exhaustive(table)
        print("theorem 9, r=2, every K in", name, out["theorem9_r2"][name], flush=True)
    for name, subs, m in (("Q8 all", all_subgroups(1), 1), ("Q8^2 all", all_subgroups(2), 2),
                          ("Q8^3 2-generated", two_generated_subgroups(3), 3)):
        out["lemma"][name] = lemma_summary(subs, m)
        print("lemma", name, out["lemma"][name], flush=True)
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "hamiltonian_cubes.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
