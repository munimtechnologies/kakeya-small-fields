# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Exact checks for Lemma 20, Theorem 22 and Corollary 13 of finite-groups.md (version 1.7.4),
section 14: 2-groups whose involutions are all central, with a self-centralising normal
A ~ Z_4^a x Z_2^b.

Lemma 20 (squares in a plane). Let X = F_2^2, V = F_2^m, sigma : V -> X a quadratic map with polar
form beta, and alpha : V -> End(X) linear with

    alpha(h') sigma(h) = (I + alpha(h)) beta(h, h')     for all h, h' in V.

Put K = ker alpha. Then beta(K, K) = 0, so sigma is linear on K; every A in alpha(V) has
A^2 x = A x for x in sigma(K); rank alpha + dim sigma(K) <= 4; and sigma vanishes on
K_0 = K n ker sigma, of codimension <= 4.
Check: for every subspace C of M_2(F_2) (67 of them), every m = 2..8 with m >= dim C, and two random
linear maps alpha of V onto C, solve the identity for sigma (it is linear in sigma's coefficients and
it suffices to test h of weight <= 2 and h' in a basis), then check every solution sigma (or 64
random ones) against each claim. For m <= 5 the true least codimension of a subspace on which sigma
vanishes is also recorded (exploratory).
Table: for U <= X, the largest dim of a subspace C of M_2(F_2) with A^2 u = A u for all A in C and
u in U is 4, 3, 2 for dim U = 0, 1, 2 (the three cases of the proof).
Control: without the identity the conclusion fails: some of 200 random sigma on F_2^7 vanish on no
subspace of codimension <= 4.

Corollary 13 (case count). With Theorem 17, Proposition 17, Theorem 21 and Theorem 22 (n <= 2a + 2b + 2
when b >= 2 and dim S <= 2 or r >= b(a - 3) + 1), every case (s, dim S, r) has n <= 2a + 3b exactly
when b = 0 or (a - 4)(b - 1) <= 1; for (6, 2) and (5, 3) the only cases left have s = 3 and
r = b(a - 3).

Vectors of F_2^m are int bitmasks. A 2 x 2 matrix is a 4-bit mask with entry (r, c) at bit 2 r + c.
A quadratic map sigma = (q_1, q_2) is stored as two 2^m-bit masks (bit h of the first is q_1(h)).
Pure Python, no dependencies.

Usage: python thm22.py [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random


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


def span(basis):
    out = [0]
    for v in basis:
        out += [x ^ v for x in out]
    return out


def combine(basis, c):
    """XOR of basis[t] over the set bits t of c."""
    out = 0
    t = 0
    while c:
        if c & 1:
            out ^= basis[t]
        c >>= 1
        t += 1
    return out


# ---------- 2 x 2 matrices over F_2 ----------

IDENTITY = 0b1001


def mat_apply(A, x):
    return parity(A & 3 & x) | (parity((A >> 2) & 3 & x) << 1)


def mat_mul(A, B):
    out = 0
    for c in range(2):
        y = mat_apply(A, mat_apply(B, 1 << c))
        for r in range(2):
            if (y >> r) & 1:
                out |= 1 << (2 * r + c)
    return out


def m2_subspaces():
    """Every subspace of M_2(F_2), as (dim, list of its 2^dim elements)."""
    return [(d, span(B)) for d in range(5) for B in subspaces(4, d)]


def m2_table():
    """For each U <= F_2^2: the largest dim C <= M_2(F_2) with A^2 u = A u for A in C, u in U."""
    spaces = m2_subspaces()
    out = {}
    for du in range(3):
        vals = []
        for U in subspaces(2, du):
            us = span(U)
            vals.append(max(d for d, C in spaces
                            if all(mat_apply(mat_mul(A, A), u) == mat_apply(A, u)
                                   for A in C for u in us)))
        out[str(du)] = sorted(vals)
    return out


M2_TABLE_PREDICTED = {"0": [4], "1": [3, 3, 3], "2": [2]}


# ---------- quadratic maps V -> F_2^2 ----------

def monomials(m):
    return [(i, i) for i in range(m)] + list(itertools.combinations(range(m), 2))


def mon_tables(m):
    return [sum(1 << h for h in range(1 << m) if (h >> i) & 1 and (h >> j) & 1)
            for i, j in monomials(m)]


def sigma_from_coeffs(c, m, tabs):
    """(q_1 mask, q_2 mask) for the coefficient vector c (bits 0..N-1 for q_1, N..2N-1 for q_2)."""
    N = len(tabs)
    return (combine(tabs, c & ((1 << N) - 1)), combine(tabs, c >> N))


def sig(S, h):
    return ((S[0] >> h) & 1) | (((S[1] >> h) & 1) << 1)


def beta(S, h, hp):
    return sig(S, h ^ hp) ^ sig(S, h) ^ sig(S, hp)


def alpha_table(cols, m):
    return [combine(cols, h) for h in range(1 << m)]


def solve_sigma(cols, m):
    """Basis (coefficient vectors) of all sigma satisfying the identity of Lemma 20 for alpha.

    Both sides have degree <= 2 in h and are linear in h', so it suffices to test h of weight <= 2
    and h' in the standard basis."""
    mons = monomials(m)
    N = len(mons)
    at = alpha_table(cols, m)
    w2 = [0] + [1 << i for i in range(m)] + [(1 << i) | (1 << j)
                                            for i, j in itertools.combinations(range(m), 2)]
    pairs = [(h, 1 << i) for h in w2 for i in range(m)]
    rows = [0] * (2 * len(pairs))
    for u in range(2 * N):
        comp, (i, j) = divmod(u, N)[0], mons[u % N]
        bit = 1 << u
        for p, (h, hp) in enumerate(pairs):
            s = (((h >> i) & 1) & ((h >> j) & 1)) << comp
            pol = 0 if i == j else ((((h >> i) & 1) & ((hp >> j) & 1))
                                    ^ (((h >> j) & 1) & ((hp >> i) & 1)))
            bb = pol << comp
            e = mat_apply(at[hp], s) ^ bb ^ mat_apply(at[h], bb)
            if e & 1:
                rows[2 * p] |= bit
            if e & 2:
                rows[2 * p + 1] |= bit
    return nullspace(rows, 2 * N)


def identity_holds(at, S, m):
    """The identity of Lemma 20 on every pair (h, h')."""
    for h in range(1 << m):
        s = sig(S, h)
        for hp in range(1 << m):
            b = beta(S, h, hp)
            if mat_apply(at[hp], s) != b ^ mat_apply(at[h], b):
                return False
    return True


def lemma20_check(cols, at, S, m, Kbasis, Cspan):
    """Every claim of Lemma 20 for one (alpha, sigma)."""
    bkk = all(beta(S, x, y) == 0 for x, y in itertools.combinations(Kbasis, 2))
    vals = [sig(S, k) for k in Kbasis]
    dsig = rank_f2(vals)
    rows = [sum(((vals[t] >> r) & 1) << t for t in range(len(Kbasis))) for r in range(2)]
    K0 = [combine(Kbasis, c) for c in nullspace(rows, len(Kbasis))]
    k0_zero = all(sig(S, x) == 0 for x in span(K0))
    rank_alpha = m - len(Kbasis)
    sigK = [x for x in span(vals) if x]
    idem = all(mat_apply(mat_mul(A, A), x) == mat_apply(A, x) for A in Cspan for x in sigK)
    bound = rank_alpha + dsig <= 4 and rank_alpha <= (4, 3, 2)[dsig]
    return {"beta_KK_zero": bkk, "K0_singular": k0_zero, "idempotent_on_sigma_K": idem,
            "bound": bound, "rank_alpha": rank_alpha, "dim_sigma_K": dsig, "codim_K0": m - len(K0)}


def subspace_masks(m, d):
    """Each d-dimensional subspace of F_2^m as a 2^m-bit mask of its elements."""
    return [sum(1 << x for x in span(B)) for B in subspaces(m, d)]


def min_singular_codim(S, m, masks_by_dim):
    """Least codimension of a subspace of F_2^m on which sigma vanishes."""
    nz = S[0] | S[1]
    for d in range(m, -1, -1):
        if any(not (mk & nz) for mk in masks_by_dim[d]):
            return m - d
    return m


def lemma20_run(seed=20261016, m_list=(2, 3, 4, 5, 6, 7, 8), trials=2, cap=64, explore_m=5,
                explore_cap=16, full_checks=1, verbose=False):
    rng = random.Random(seed)
    spaces = [(d, B) for d in range(5) for B in subspaces(4, d)]
    tabs = {m: mon_tables(m) for m in m_list}
    masks = {m: {d: subspace_masks(m, d) for d in range(m + 1)} for m in m_list if m <= explore_m}
    st = {"systems": 0, "sigmas": 0, "sigmas_spanning_X": 0, "solution_dims": {},
          "rank_alpha_dim_sigma_K": {}, "codim_K0": {}, "true_min_codim": {},
          "violations": {"beta_KK_zero": 0, "K0_singular": 0, "idempotent_on_sigma_K": 0,
                         "bound": 0, "identity_full": 0}}
    for d, B in spaces:
        Cspan = span(B)
        for m in m_list:
            if m < d:
                continue
            for _ in range(trials):
                while True:
                    cols = [combine(B, rng.getrandbits(d) if d else 0) for _ in range(m)]
                    if rank_f2(cols) == d:
                        break
                at = alpha_table(cols, m)
                Kbasis = nullspace([sum(((cols[i] >> j) & 1) << i for i in range(m))
                                    for j in range(4)], m)
                sol = solve_sigma(cols, m)
                D = len(sol)
                st["systems"] += 1
                st["solution_dims"][str(D)] = st["solution_dims"].get(str(D), 0) + 1
                tables = [sigma_from_coeffs(c, m, tabs[m]) for c in sol]
                if (1 << D) <= cap:
                    combos = range(1 << D)
                else:
                    combos = [rng.getrandbits(D) for _ in range(cap)]
                for t, c in enumerate(combos):
                    S = (combine([x[0] for x in tables], c), combine([x[1] for x in tables], c))
                    st["sigmas"] += 1
                    if rank_f2([sig(S, h) for h in range(1 << m)]) == 2:
                        st["sigmas_spanning_X"] += 1
                    if t < full_checks and not identity_holds(at, S, m):
                        st["violations"]["identity_full"] += 1
                    r = lemma20_check(cols, at, S, m, Kbasis, Cspan)
                    for key in ("beta_KK_zero", "K0_singular", "idempotent_on_sigma_K", "bound"):
                        if not r[key]:
                            st["violations"][key] += 1
                    key = f"{r['rank_alpha']},{r['dim_sigma_K']}"
                    st["rank_alpha_dim_sigma_K"][key] = st["rank_alpha_dim_sigma_K"].get(key, 0) + 1
                    key = str(r["codim_K0"])
                    st["codim_K0"][key] = st["codim_K0"].get(key, 0) + 1
                    if m <= explore_m and t < explore_cap:
                        key = f"m={m}:{min_singular_codim(S, m, masks[m])}"
                        st["true_min_codim"][key] = st["true_min_codim"].get(key, 0) + 1
                if verbose:
                    print(f"lemma20 dimC={d} m={m}: solution dim {D}", flush=True)
    st["match"] = all(v == 0 for v in st["violations"].values())
    return st


def control_run(seed=7, m=7, count=200):
    """Random sigma on F_2^m with no identity: how many vanish on no subspace of codim <= 4."""
    rng = random.Random(seed)
    tabs = mon_tables(m)
    N = len(tabs)
    masks = subspace_masks(m, m - 4)
    none = 0
    for _ in range(count):
        S = sigma_from_coeffs(rng.getrandbits(2 * N), m, tabs)
        nz = S[0] | S[1]
        if not any(not (mk & nz) for mk in masks):
            none += 1
    return {"m": m, "samples": count, "no_singular_subspace_of_codim_le_4": none,
            "match": none > 0}


# ---------- the case count of Corollary 13 ----------

def case_bounds(a, b):
    """Largest bound on n = dim L/A over every case (s, dim S, r), versus 2a + 3b (e = 3).

    dim S = 0 gives exponent 4 (settled). Otherwise n <= a + s + 2b + r with r <= b(a - s)
    (Theorem 17); n <= a + 2b + 3 when dim S = 1 (Proposition 17); n <= 2a + 2b + 1 when b >= 1 and
    r >= b(a - 2) + 1 (Theorem 21 with Lemma 19); n <= 2a + 2b + 2 when b >= 2 and either dim S <= 2
    or r >= b(a - 3) + 1 (Theorem 22 with Lemma 19)."""
    need = 2 * a + 3 * b
    worst, open_cases = 0, []
    for dS in range(1, a + 1):
        for s in range(0, dS + 1):
            for r in range(0, b * (a - s) + 1):
                bound = a + s + 2 * b + r
                if dS == 1:
                    bound = min(bound, a + 2 * b + 3)
                if b >= 1 and r >= b * (a - 2) + 1:
                    bound = min(bound, 2 * a + 2 * b + 1)
                if b >= 2 and (dS <= 2 or r >= b * (a - 3) + 1):
                    bound = min(bound, 2 * a + 2 * b + 2)
                worst = max(worst, bound)
                if bound > need:
                    open_cases.append([s, dS, r, bound])
    return {"need": need, "max_bound": worst, "settled": worst <= need, "open": open_cases}


def settled_predicted(a, b):
    return b == 0 or (a - 4) * (b - 1) <= 1


BOUND_CASES = [(5, 2), (4, 3), (4, 8), (6, 2), (5, 3), (7, 2), (8, 1)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {}
    tab = m2_table()
    out["m2_table"] = tab
    ok = tab == M2_TABLE_PREDICTED
    print(f"m2 table (dim U -> largest dim C): {tab}, match {ok}", flush=True)
    st = lemma20_run(verbose=True)
    out["lemma20"] = st
    ok = ok and st["match"]
    print(f"lemma20: {json.dumps(st, sort_keys=True)}", flush=True)
    ctl = control_run()
    out["control"] = ctl
    ok = ok and ctl["match"]
    print(f"control: {json.dumps(ctl, sort_keys=True)}", flush=True)
    table_ok = True
    out["settled_table"] = {}
    for a in range(1, 9):
        row = ""
        for b in range(0, 9):
            got = case_bounds(a, b)["settled"]
            table_ok = table_ok and got == settled_predicted(a, b)
            row += " Y" if got else " ."
            out["settled_table"][f"{a},{b}"] = got
        print(f"settled a={a}: b=0..8{row}", flush=True)
    print(f"settled table matches b = 0 or (a - 4)(b - 1) <= 1: {table_ok}", flush=True)
    ok = ok and table_ok
    out["bounds"] = {}
    for a, b in BOUND_CASES:
        r = case_bounds(a, b)
        out["bounds"][f"{a},{b}"] = r
        print(f"bounds a={a} b={b}: need {r['need']}, max {r['max_bound']}, settled {r['settled']}, "
              f"open (s, dim S, r, bound) {r['open']}", flush=True)
    ok = ok and out["bounds"]["5,2"]["settled"] and out["bounds"]["4,3"]["settled"]
    ok = ok and out["bounds"]["6,2"]["open"] == [[3, d, 6, 19] for d in range(3, 7)]
    ok = ok and out["bounds"]["5,3"]["open"] == [[3, d, 6, 20] for d in range(3, 6)]
    out["all_match"] = ok
    print(f"SUMMARY all_match {ok}", flush=True)
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "thm22.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
