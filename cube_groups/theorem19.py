# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for Theorem 19 (draft for kakeya-small-fields 1.7).

Theorem 19. Let L be a finite 2-group of class <= 2 and exponent 2^e in which every involution is
central. Write Z(L) = prod_j (Z_(2^j))^(a_j), so k = sum_j a_j = rank Omega_1(L). Then

    log2 |L| <= e k + a_(e-1) <= (e + 1) k.

Equality for Q_8^m, Q_8 x Z_4 and Q_8 x Z_8 (and every cyclic group). Subgroups inherit all three
hypotheses, so the script checks the bound on every subgroup. Q_16 (class 3) shows that class 2 is
needed: log2 16 = 4 > 3 = e k + a_(e-1), although |Q_16| = |Omega_1|^(e+1) still holds there.

    python theorem19.py --out-dir OUT
"""
import argparse
import itertools
import json
import os


# ---- groups given by elements, a multiplication function, identity and generators ---------

def cyclic(m):
    return list(range(m)), (lambda u, v: (u + v) % m), 0, [1]


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


def metacyclic(nx, ny, r):
    """<x, y | x^nx = y^ny = 1, y x y^(-1) = x^r>, pairs (i, k) = x^i y^k with
    (i, k)(j, l) = (i + r^k j, k + l). Needs r^ny = 1 mod nx."""
    assert pow(r, ny, nx) == 1 % nx
    powers = [pow(r, k, nx) for k in range(ny)]
    elems = [(i, k) for i in range(nx) for k in range(ny)]

    def mul(u, v):
        return ((u[0] + powers[u[1]] * v[0]) % nx, (u[1] + v[1]) % ny)
    return elems, mul, (0, 0), [(1, 0), (0, 1)]


def direct_product(*groups):
    elems = list(itertools.product(*[g[0] for g in groups]))
    muls = [g[1] for g in groups]
    one = tuple(g[2] for g in groups)

    def mul(u, v):
        return tuple(m(x, y) for m, x, y in zip(muls, u, v))
    gens = [tuple(h if d == c else groups[d][2] for d in range(len(groups)))
            for c, g in enumerate(groups) for h in g[3]]
    return elems, mul, one, gens


# ---- index tables -------------------------------------------------------------------------

def table(group):
    elems, mul, one, gens = group
    index = {x: n for n, x in enumerate(elems)}
    T = [[index[mul(a, b)] for b in elems] for a in elems]
    return T, index[one], [index[g] for g in gens]


def orders(T, one):
    out = []
    for x in range(len(T)):
        o, y = 1, x
        while y != one:
            y = T[y][x]
            o += 1
        out.append(o)
    return out


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
    """Every subgroup with a generating list, adjoining one element at a time (one per coset gS)."""
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
    return gens


def log2_exact(n):
    assert n > 0 and n & (n - 1) == 0, n
    return n.bit_length() - 1


# ---- hypotheses and the bound ---------------------------------------------------------------

def involutions_central(T, order_of):
    n = len(T)
    return all(T[x][y] == T[y][x] for x in range(n) if order_of[x] == 2 for y in range(n))


def class_at_most_2(T, one, gens):
    """G' <= Z(G) iff every commutator of two generators is central (checked against generators)."""
    inv = [row.index(one) for row in T]
    for x in gens:
        for y in gens:
            c = T[T[T[inv[x]][inv[y]]][x]][y]
            if any(T[c][g] != T[g][c] for g in gens):
                return False
    return True


def abelian_invariants(Z, order_of):
    """a_j = number of Z_(2^j) factors of the abelian 2-group Z, from |Omega_j(Z)| = 2^(w_j)."""
    E = log2_exact(max(order_of[z] for z in Z))
    w = [log2_exact(sum(1 for z in Z if (2 ** j) % order_of[z] == 0)) for j in range(E + 1)]
    b = [w[j] - w[j - 1] for j in range(1, E + 1)] + [0]
    return {j: b[j - 1] - b[j] for j in range(1, E + 1) if b[j - 1] - b[j]}


def analyse(T, order_of, L, gens):
    e = log2_exact(max(order_of[x] for x in L))
    Z = [z for z in L if all(T[z][g] == T[g][z] for g in gens)]
    a = abelian_invariants(Z, order_of)
    k = log2_exact(sum(1 for x in L if order_of[x] <= 2))
    return {"log2_order": log2_exact(len(L)), "e": e, "k": k, "a": a, "bound": e * k + a.get(e - 1, 0)}


def check_group(group):
    T, one, gidx = table(group)
    order_of = orders(T, one)
    subs = all_subgroups(T, one)
    rows = [analyse(T, order_of, L, g) for L, g in subs.items()]
    return {
        "order": len(T),
        "class_le_2": class_at_most_2(T, one, gidx),
        "involutions_central": involutions_central(T, order_of),
        "whole": analyse(T, order_of, frozenset(range(len(T))), gidx),
        "subgroups": len(rows),
        "bound_holds": all(r["log2_order"] <= r["bound"] for r in rows),
        "omega_e_plus_1_holds": all(r["log2_order"] <= (r["e"] + 1) * r["k"] for r in rows),
        "equality_cases": sorted({(r["log2_order"], r["e"], r["k"]) for r in rows
                                  if r["log2_order"] == r["bound"] and r["log2_order"] > 0}),
        "counterexamples": [r for r in rows if r["log2_order"] > r["bound"]][:10],
    }


GROUPS = [
    ("Q8", lambda: quaternion(3)),
    ("Q8xZ4", lambda: direct_product(quaternion(3), cyclic(4))),
    ("Q8xZ8", lambda: direct_product(quaternion(3), cyclic(8))),
    ("Q8xQ8", lambda: direct_product(quaternion(3), quaternion(3))),
    ("<x,y|x^8=y^8=1,yxy^-1=x^5>", lambda: metacyclic(8, 8, 5)),
    ("<x,y|x^8=y^4=1,yxy^-1=x^5>", lambda: metacyclic(8, 4, 5)),
    ("<x,y|x^16=y^4=1,yxy^-1=x^9>", lambda: metacyclic(16, 4, 9)),
    ("Q16 (class 3, contrast)", lambda: quaternion(4)),
    ("Q8xQ8xZ2", lambda: direct_product(quaternion(3), quaternion(3), cyclic(2))),
    ("Q8xQ8xZ4", lambda: direct_product(quaternion(3), quaternion(3), cyclic(4))),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    out = {}
    for name, make in GROUPS:
        out[name] = check_group(make())
        print("Theorem 19", name, out[name], flush=True)
        with open(os.path.join(args.out_dir, "theorem19.json"), "w") as f:
            json.dump(out, f, indent=1, default=str)


if __name__ == "__main__":
    main()
