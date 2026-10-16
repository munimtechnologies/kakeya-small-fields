# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Exact checks for the linear-algebra steps behind Theorem 19 of finite-groups.md (version 1.8):
the case A ~ Z_4^4 x Z_2^2 of section 14.

Lemma 15. Let q be a non-zero quadratic form on V = F_2^n with polar form B, and pi a linear form
with q(h) pi(h') = B(h, h') (1 + pi(h)) for all h, h' in V. Then rank B <= 2, pi = B(h*, .) for every
h* with q(h*) = 1, pi = 0 if B = 0, and q vanishes on rad B if B != 0.
Vector form: if p : V -> F_2^a is linear, u != 0, and q(h) p(h') = B(h, h') (u + p(h)) for all
h, h', then p(V) lies in span(u).

Lemma 16. For C != 0 in M_(b x a)(F_2), the rank-1 matrices in C^perp = {M : tr(C^T M) = 0} span it.

Proposition 18. Let b >= 2 and W <= Hom(F_2^a, F_2^b) of codimension <= 1. Then no non-zero vector
is killed by all of W, and the only linear lam : W -> F_2^a with M lam(M) = 0 for every M in W is 0.
Control: keeping only the polar equations M lam(M') + M' lam(M) = 0, a hyperplane C^perp has
exactly one non-zero solution when b = 2 and rank C = 1, and none otherwise.

Witt bound (counting step of Proposition 17): a quadratic form on F_2^m whose polar form has rank
2 rho has a totally singular subspace of dimension >= m - rho - 2.

Exploratory (no prediction): dim Lam(W) = dim{lam : W -> F_2^a / N(W)} for every W of codimension
2, where N(W) is the common kernel, for the next open cases.

Matrices M in M_(b x a)(F_2) are bitmasks: entry (p, q) (row p, column q) is bit p * a + q.
Pure Python, no dependencies.

Usage: python case42.py [--out-dir DIR]
"""
import argparse
import itertools
import json
import os


def parity(x):
    return bin(x).count("1") & 1


def rank_f2(rows):
    """Rank of a list of int bitmasks over F_2."""
    pivots = {}
    r = 0
    for row in rows:
        x = row
        while x:
            hb = x.bit_length() - 1
            if hb in pivots:
                x ^= pivots[hb]
            else:
                pivots[hb] = x
                r += 1
                break
    return r


def nullspace(constraints, nbits):
    """Basis of {x in F_2^nbits : parity(c & x) = 0 for every c}, via reduced row echelon form."""
    pivots = []                                   # (pivot column, row); column is 0 in other rows
    for c in constraints:
        x = c
        for col, r in pivots:
            if (x >> col) & 1:
                x ^= r
        if x:
            col = x.bit_length() - 1
            pivots = [(pc, r ^ x if (r >> col) & 1 else r) for pc, r in pivots] + [(col, x)]
    pcols = {col for col, _ in pivots}
    basis = []
    for f in range(nbits):
        if f in pcols:
            continue
        v = 1 << f
        for col, r in pivots:
            if (r >> f) & 1:
                v |= 1 << col
        basis.append(v)
    return basis


def rows_of(M, a, b):
    mask = (1 << a) - 1
    return [(M >> (p * a)) & mask for p in range(b)]


def apply(M, w, a, b):
    """M applied to w (bitmask of length a); result is a bitmask of length b."""
    out = 0
    for p, row in enumerate(rows_of(M, a, b)):
        if parity(row & w):
            out |= 1 << p
    return out


def matrix_rank(M, a, b):
    return rank_f2(rows_of(M, a, b))


def full_basis(a, b):
    return [1 << t for t in range(a * b)]


def kernel_dim(basis, a, b):
    """dim N(W): vectors killed by every M in W = span(basis)."""
    rows = [r for M in basis for r in rows_of(M, a, b)]
    return a - rank_f2(rows)


def lam_nullity(basis, a, b, diagonal=True):
    """dim{lam : W -> F_2^a linear : M lam(M) = 0 for all M in W} (unknowns w_i = lam(basis_i)).

    Over F_2 this is: M_i w_i = 0 (diagonal) and M_i w_j + M_j w_i = 0 (polar) for i < j.
    With diagonal=False only the polar equations are kept (the control)."""
    d = len(basis)
    R = [rows_of(M, a, b) for M in basis]
    rows = []
    for i in range(d):
        if diagonal:
            for p in range(b):
                if R[i][p]:
                    rows.append(R[i][p] << (i * a))
        for j in range(i + 1, d):
            for p in range(b):
                row = (R[i][p] << (j * a)) ^ (R[j][p] << (i * a))
                if row:
                    rows.append(row)
    return d * a - rank_f2(rows)


def lam_dim(basis, a, b, diagonal=True):
    """dim Lam(W): solutions modulo those with values in N(W) (which solve trivially)."""
    return lam_nullity(basis, a, b, diagonal) - len(basis) * kernel_dim(basis, a, b)


def rank1_maps(a, b):
    out = []
    for u in range(1, 1 << b):
        for v in range(1, 1 << a):
            out.append(sum(v << (p * a) for p in range(b) if (u >> p) & 1))
    return out


def lemma16_ok(a, b):
    """Rank-1 maps in C^perp span C^perp, for every C != 0."""
    r1 = rank1_maps(a, b)
    for C in range(1, 1 << (a * b)):
        if rank_f2([M for M in r1 if not parity(C & M)]) != a * b - 1:
            return False
    return True


def hyperplane_report(a, b):
    """Proposition 18 and its polar-only control over every hyperplane C^perp."""
    nb = a * b
    out = {"hyperplanes": 0, "kernel_zero": 0, "lam_zero": 0, "polar_one": 0, "polar_match": 0}
    for C in range(1, 1 << nb):
        basis = nullspace([C], nb)
        k = kernel_dim(basis, a, b)
        lam = lam_nullity(basis, a, b) - len(basis) * k
        pol = lam_nullity(basis, a, b, diagonal=False) - len(basis) * k
        pred = 1 if (b == 2 and matrix_rank(C, a, b) == 1) else 0
        out["hyperplanes"] += 1
        out["kernel_zero"] += k == 0
        out["lam_zero"] += lam == 0
        out["polar_one"] += pol == 1
        out["polar_match"] += pol == pred
    return out


def codim2_report(a, b):
    """Histogram of (dim N(W), dim Lam(W)) over every W of codimension 2."""
    nb = a * b
    hist = {}
    for x in range(1, 1 << nb):
        for y in range(x + 1, 1 << nb):
            if x ^ y < y:                           # count each plane {x, y, x^y} once
                continue
            basis = nullspace([x, y], nb)
            k = kernel_dim(basis, a, b)
            lam = lam_nullity(basis, a, b) - len(basis) * k
            key = f"{k},{lam}"
            hist[key] = hist.get(key, 0) + 1
    return hist


# ---- quadratic forms on F_2^n (q(0) = 0, degree <= 2) ----

def monomials(n):
    return [1 << i for i in range(n)] + [(1 << i) | (1 << j)
                                         for i, j in itertools.combinations(range(n), 2)]


def tables(coef, n):
    """Truth table T of q and polar rows Brow (Brow[h] bit h' = B(h, h'))."""
    N = 1 << n
    monos = monomials(n)
    T = []
    for h in range(N):
        v = 0
        for t, m in enumerate(monos):
            if (coef >> t) & 1 and h & m == m:
                v ^= 1
        T.append(v)
    Brow = []
    for h in range(N):
        row = 0
        for h2 in range(N):
            if T[h ^ h2] ^ T[h] ^ T[h2]:
                row |= 1 << h2
        Brow.append(row)
    return T, Brow


def pi_table(pm, n):
    """Bitmask over h' of the linear form h' -> parity(pm & h')."""
    return sum(1 << h for h in range(1 << n) if parity(pm & h))


def form_rank(Brow, n):
    rows = []
    for i in range(n):
        rows.append(sum(((Brow[1 << i] >> (1 << j)) & 1) << j for j in range(n)))
    return rank_f2(rows)


def solves(T, Brow, pm, n):
    """q(h) pi(h') = B(h, h') (1 + pi(h)) for all h, h'."""
    P = pi_table(pm, n)
    for h in range(1 << n):
        lhs = P if T[h] else 0
        rhs = 0 if parity(pm & h) else Brow[h]
        if lhs != rhs:
            return False
    return True


def lemma15_check(n):
    N = 1 << n
    out = {"solutions": 0, "with_B_nonzero": 0, "violations": 0, "max_rank": 0}
    for coef in range(1, 1 << len(monomials(n))):
        T, Brow = tables(coef, n)
        for pm in range(N):
            if not solves(T, Brow, pm, n):
                continue
            P = pi_table(pm, n)
            r = form_rank(Brow, n)
            good = r <= 2 and all(P == Brow[h] for h in range(N) if T[h])
            if r == 0:
                good = good and pm == 0
            else:
                out["with_B_nonzero"] += 1
                good = good and all(T[h] == 0 for h in range(N) if Brow[h] == 0)
            out["solutions"] += 1
            out["max_rank"] = max(out["max_rank"], r)
            out["violations"] += not good
    return out


def vector_check(n, a):
    """Vector form of Lemma 15 with u = e_0: every solution p has p(V) inside {0, u}."""
    N = 1 << n
    u = 1
    out = {"solutions": 0, "outside_span": 0}
    for coef in range(1, 1 << len(monomials(n))):
        T, Brow = tables(coef, n)
        for imgs in itertools.product(range(1 << a), repeat=n):
            P = [0] * N
            for h in range(1, N):
                low = h & -h
                P[h] = P[h ^ low] ^ imgs[low.bit_length() - 1]
            ok = True
            for h in range(N):
                for h2 in range(N):
                    lhs = P[h2] if T[h] else 0
                    rhs = (u ^ P[h]) if (Brow[h] >> h2) & 1 else 0
                    if lhs != rhs:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                out["solutions"] += 1
                out["outside_span"] += any(P[h] not in (0, u) for h in range(N))
    return out


def max_singular_dim(T, Brow, n, cap=None):
    """Largest dimension of a totally singular subspace (q = 0 and B = 0 on it), stopping at cap."""
    Z = [h for h in range(1, 1 << n) if not T[h]]
    best = [0]
    cap = n if cap is None else cap

    def dfs(basis, span, start):
        if len(basis) > best[0]:
            best[0] = len(basis)
        for idx in range(start, len(Z)):
            if best[0] >= cap:
                return
            v = Z[idx]
            if v in span or any((Brow[v] >> w) & 1 for w in basis):
                continue
            dfs(basis + [v], span | {s ^ v for s in span}, idx + 1)

    dfs([], {0}, 0)
    return best[0]


def witt_check(m):
    out = {"forms": 0, "violations": 0, "min_slack": None}
    for coef in range(0, 1 << len(monomials(m))):
        T, Brow = tables(coef, m)
        rho = form_rank(Brow, m) // 2
        # a totally singular subspace is B-isotropic, so its dimension is at most m - rho
        slack = max_singular_dim(T, Brow, m, cap=m - rho) - (m - rho - 2)
        out["forms"] += 1
        out["violations"] += slack < 0
        if out["min_slack"] is None or slack < out["min_slack"]:
            out["min_slack"] = slack
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"lemma15": {}, "vector": {}, "lemma16": {}, "full": {}, "hyperplanes": {},
           "witt": {}, "codim2": {}}
    ok = True
    for n in range(1, 6):
        r = lemma15_check(n)
        out["lemma15"][str(n)] = r
        ok = ok and r["violations"] == 0
        print(f"lemma15 n={n}: {json.dumps(r)}", flush=True)
    for n, a in [(2, 2), (2, 3), (3, 2), (3, 3)]:
        r = vector_check(n, a)
        out["vector"][f"{n},{a}"] = r
        ok = ok and r["outside_span"] == 0
        print(f"vector n={n} a={a}: {json.dumps(r)}", flush=True)
    for a, b in [(1, 1), (2, 1), (1, 2), (2, 2), (3, 2), (2, 3), (4, 2), (3, 3)]:
        r = lemma16_ok(a, b)
        out["lemma16"][f"{a},{b}"] = r
        ok = ok and r
        print(f"lemma16 a={a} b={b}: {r}", flush=True)
    for a, b in [(2, 2), (3, 2), (4, 2), (5, 2), (2, 3), (3, 3), (2, 4)]:
        basis = full_basis(a, b)
        full = (lam_dim(basis, a, b), lam_dim(basis, a, b, diagonal=False))
        out["full"][f"{a},{b}"] = full
        ok = ok and full == (0, 0)
        r = hyperplane_report(a, b)
        out["hyperplanes"][f"{a},{b}"] = r
        h = r["hyperplanes"]
        match = r["kernel_zero"] == h and r["lam_zero"] == h and r["polar_match"] == h
        if b == 2:
            match = match and r["polar_one"] == 3 * ((1 << a) - 1)
        ok = ok and match
        print(f"prop18 a={a} b={b}: full {full}, {json.dumps(r)}, match {match}", flush=True)
    for m in range(1, 5):
        r = witt_check(m)
        out["witt"][str(m)] = r
        ok = ok and r["violations"] == 0
        print(f"witt m={m}: {json.dumps(r)}", flush=True)
    for a, b in [(2, 2), (3, 2), (2, 3), (4, 2), (3, 3), (5, 2)]:
        hist = codim2_report(a, b)
        out["codim2"][f"{a},{b}"] = hist
        print(f"codim2 a={a} b={b}: (dim N, dim Lam) -> count {json.dumps(hist, sort_keys=True)}",
              flush=True)
    out["all_match"] = ok
    print(f"SUMMARY all_match {ok}")
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "case42.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
