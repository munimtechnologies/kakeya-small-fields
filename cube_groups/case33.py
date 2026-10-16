# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Exact checks for the linear-algebra steps behind Theorem 20 of finite-groups.md (version 1.7.2):
the case A ~ Z_4^3 x Z_2^3 of section 14.

Proposition 19. Let b >= 2 and W <= Hom(F_2^a, F_2^b) of codimension c <= b - 1. Then no non-zero
vector is killed by all of W (N(W) = 0), and the only linear lam : W -> F_2^a with M lam(M) = 0 for
every M in W is 0 (Lam(W) = 0).
Control 1 (c = b): exactly 2^a - 1 subspaces W have N(W) != 0, namely the K_w = {M : M w = 0}.
Control 2 (c = b - 1): the "special" W = {M : M w in span(u)} number (2^a - 1)(2^b - 1), and on each
of them the polar equations M lam(M') + M' lam(M) = 0 alone have a non-zero solution
(lam(M) = (y^T M w) w with y^T u = 1), so the diagonal equations M lam(M) = 0 are needed.

Lemma 17 (linear core). If x != 0 in F_2^a, M x = 0 and M' x lies in Im M for every M' in
Hom(F_2^a, F_2^b), then a > b (and M is onto). So no such pair exists when a <= b, and for a > b
there are #onto(b x a) * (2^(a-b) - 1) of them.

Case bookkeeping: the bounds of Theorems 17 and 18, Propositions 17 and 19 and Lemma 17 over every
case (s, dim S, r), and whether they give n <= 2a + 3b. With the tools of version 1.7.1 only
(new=False), (3, 3) is open; with Proposition 19 and Lemma 17 it is settled.

Matrices M in M_(b x a)(F_2) are bitmasks: entry (p, q) (row p, column q) is bit p * a + q, as in
case42.py. Pure Python, no dependencies.

Usage: python case33.py [--out-dir DIR]
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
    pivots = []
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


def subspaces(nbits, c):
    """Every c-dimensional subspace of F_2^nbits, once each, as its reduced echelon basis."""
    for piv in itertools.combinations(range(nbits), c):
        pset = set(piv)
        frees = [[j for j in range(p) if j not in pset] for p in piv]
        for choice in itertools.product(*[range(1 << len(f)) for f in frees]):
            rows = []
            for p, f, x in zip(piv, frees, choice):
                row = 1 << p
                for t, j in enumerate(f):
                    if (x >> t) & 1:
                        row |= 1 << j
                rows.append(row)
            yield rows


def gaussian_binomial(n, k):
    num, den = 1, 1
    for i in range(k):
        num *= (1 << (n - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def kernel_of_w(w, a, b):
    """Basis of K_w = {M : M w = 0}."""
    return nullspace([w << (p * a) for p in range(b)], a * b)


def is_special(constraints, a, b):
    """W = C^perp contains some K_w (w != 0), i.e. W = {M : M w in a line} when c = b - 1."""
    for w in range(1, 1 << a):
        if all(not parity(C & M) for M in kernel_of_w(w, a, b) for C in constraints):
            return True
    return False


def prop19_report(a, b, c):
    """N(W) and Lam(W) over every W of codimension c in Hom(F_2^a, F_2^b)."""
    nb = a * b
    out = {"spaces": 0, "kernel_zero": 0, "lam_zero": 0, "kernel_nonzero": 0,
           "special": 0, "special_polar_nonzero": 0, "nonspecial_polar_nonzero": 0,
           "lam_hist": {}}
    for cons in subspaces(nb, c):
        basis = nullspace(cons, nb)
        k = kernel_dim(basis, a, b)
        lam = lam_nullity(basis, a, b) - len(basis) * k
        out["spaces"] += 1
        out["kernel_zero"] += k == 0
        out["kernel_nonzero"] += k != 0
        out["lam_zero"] += k == 0 and lam == 0
        key = f"{k},{lam}"
        out["lam_hist"][key] = out["lam_hist"].get(key, 0) + 1
        if c == b - 1:
            pol = lam_nullity(basis, a, b, diagonal=False) - len(basis) * k
            if is_special(cons, a, b):
                out["special"] += 1
                out["special_polar_nonzero"] += pol > 0
            else:
                out["nonspecial_polar_nonzero"] += pol > 0
    return out


def lemma17_core(a, b):
    """Pairs (M, x), x != 0, with M x = 0 and Hom(F_2^a, F_2^b) x inside Im M."""
    mats = range(1 << (a * b))
    hom_x = {x: {apply(M, x, a, b) for M in mats} for x in range(1, 1 << a)}
    count = 0
    for M in mats:
        image = {apply(M, y, a, b) for y in range(1 << a)}
        for x in range(1, 1 << a):
            if apply(M, x, a, b) == 0 and hom_x[x] <= image:
                count += 1
    return count


def lemma17_predicted(a, b):
    if a <= b:
        return 0
    onto = 1
    for i in range(b):
        onto *= (1 << a) - (1 << i)
    return onto * ((1 << (a - b)) - 1)


def case_bounds(a, b, new=True):
    """Largest bound on n = dim L/A over the cases left by the tools (b >= 2), versus 2a + 3b.

    Cases: dim S = 0 gives exponent 4 (settled); dim S = 1 gives n <= a + 2b + 3 (Proposition 17);
    dim S >= 2: n <= n_0 + r with r <= b(a - s) and n_0 <= a + s + 2b (Theorem 17), improved to
    a + 2b - dim S when s = 0 and beta(H, H_0) = 0 (Theorem 18's step), which holds when the
    codimension ab - r is 0, or <= 1 with b = 2 (Proposition 18), or <= b - 1 (Proposition 19, new),
    and to a + 2b when s = 1 and r = b(a - 1) (Theorem 19's s = 1 step). Lemma 17 (new): s = 0,
    r = ab and a <= b force S = 0."""
    need = 2 * a + 3 * b
    worst, open_cases = 0, []

    def note(s, dS, r, bound):
        nonlocal worst
        worst = max(worst, bound)
        if bound > need:
            open_cases.append([s, dS, r, bound])

    for dS in range(1, a + 1):
        for s in range(0, dS + 1):
            if dS == 1:
                note(s, dS, None, a + 2 * b + 3)
                continue
            for r in range(0, b * (a - s) + 1):
                codim = a * b - r
                if new and s == 0 and codim == 0 and a <= b:
                    continue
                n0 = a + s + 2 * b
                beta_zero = codim == 0 or (b == 2 and codim <= 1) or (new and codim <= b - 1)
                if s == 0 and beta_zero:
                    n0 = min(n0, a + 2 * b - dS)
                if s == 1 and r == b * (a - 1):
                    n0 = min(n0, a + 2 * b)
                note(s, dS, r, n0 + r)
    return {"need": need, "max_bound": worst, "settled": worst <= need, "open": open_cases}


PROP19_CASES = [(1, 2), (2, 2), (3, 2), (4, 2), (1, 3), (2, 3), (3, 3), (1, 4), (2, 4)]
CONTROL1_CASES = [(1, 2), (2, 2), (3, 2), (4, 2), (1, 3), (2, 3), (1, 4)]
LEMMA17_CASES = [(1, 1), (1, 2), (2, 2), (1, 3), (2, 3), (3, 3), (2, 1), (3, 1), (3, 2)]
BOUND_CASES = [(1, 2), (2, 2), (2, 3), (2, 5), (3, 2), (4, 2), (3, 3), (5, 2), (4, 3), (3, 4)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"prop19": {}, "control1": {}, "lemma17": {}, "bounds": {}}
    ok = True
    for a, b in PROP19_CASES:
        for c in range(0, b):
            r = prop19_report(a, b, c)
            match = (r["spaces"] == gaussian_binomial(a * b, c) and r["kernel_zero"] == r["spaces"]
                     and r["lam_zero"] == r["spaces"])
            if c == b - 1:
                special = ((1 << a) - 1) * ((1 << b) - 1)
                match = match and r["special"] == special and r["special_polar_nonzero"] == special
            out["prop19"][f"{a},{b},{c}"] = r
            ok = ok and match
            print(f"prop19 a={a} b={b} codim={c}: {json.dumps(r, sort_keys=True)}, match {match}",
                  flush=True)
    for a, b in CONTROL1_CASES:
        r = prop19_report(a, b, b)
        match = r["spaces"] == gaussian_binomial(a * b, b) and r["kernel_nonzero"] == (1 << a) - 1
        out["control1"][f"{a},{b}"] = r
        ok = ok and match
        print(f"control1 a={a} b={b} codim={b}: {json.dumps(r, sort_keys=True)}, match {match}",
              flush=True)
    for a, b in LEMMA17_CASES:
        got, pred = lemma17_core(a, b), lemma17_predicted(a, b)
        out["lemma17"][f"{a},{b}"] = [got, pred]
        ok = ok and got == pred
        print(f"lemma17 a={a} b={b}: pairs {got}, predicted {pred}", flush=True)
    for a, b in BOUND_CASES:
        new, old = case_bounds(a, b), case_bounds(a, b, new=False)
        out["bounds"][f"{a},{b}"] = {"new": new, "old": old}
        print(f"bounds a={a} b={b}: need {new['need']}, new max {new['max_bound']} "
              f"settled {new['settled']}, 1.7.1 max {old['max_bound']} settled {old['settled']}, "
              f"open (s, dim S, r, bound) {new['open']}", flush=True)
    b33 = out["bounds"]["3,3"]
    ok = ok and b33["new"]["settled"] and not b33["old"]["settled"]
    out["all_match"] = ok
    print(f"SUMMARY all_match {ok}")
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "case33.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
