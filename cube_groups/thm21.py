# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Exact checks for Lemma 19, Theorem 21 and Corollary 12 of finite-groups.md (version 1.7.3),
section 14: 2-groups whose involutions are all central, with a self-centralising normal
A ~ Z_4^a x Z_2^b.

Lemma 19 (slices). For W <= Hom(F_2^a, F_2^b) and y != 0 in F_2^b put
V_y = {x in F_2^a : y^T M x = 0 for every M in W} and d_y = dim V_y. Then x -> y x^T maps V_y onto
W^perp n (F_2^a (x) y), and for every basis y_1, ..., y_b of F_2^b these slices are independent, so
d_(y_1) + ... + d_(y_b) <= codim W. Hence codim W < 2b forces min_y d_y <= 1.
Control (sharpness): at codim W = 2b exactly C(a, 2)_2 subspaces have every d_y >= 2, namely the
K_X = {M : M X = 0} with dim X = 2, and on them every d_y = 2.

Theorem 21 / Corollary 12 (case count). With Theorem 17 (n_0 <= a + s + 2b, r <= b(a - s)),
Proposition 17 (dim S = 1 gives n <= a + 2b + 3) and Theorem 21 (r >= b(a - 2) + 1 gives
n <= 2a + 2b + 1), every case (s, dim S, r) has n <= 2a + 3b exactly when b = 0 or
(a - 3)(b - 1) <= 1; for (5, 2) and (4, 3) the only cases left have s = 2 and r = b(a - 2).

Group check (needs cube_groups/z4z2.py next to this file): on the explicit groups of z4z2.py,
sigma(h) lies in V_y whenever y^T Q_h = 0 (the step of Theorem 21 that uses Lemma 17), the largest
subspace T of H with sigma(T) = 0 has dim T <= a + 2b (Lemma 18), and squaring on the preimage of
such a T vanishes only on Omega; the control group with a non-central involution breaks the last.

Matrices M in M_(b x a)(F_2) are bitmasks: entry (p, q) (row p, column q) is bit p * a + q, as in
case33.py. Pure Python, no dependencies.

Usage: python thm21.py [--out-dir DIR]
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
    if k < 0 or k > n:
        return 0
    num, den = 1, 1
    for i in range(k):
        num *= (1 << (n - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def apply(M, x, a, b):
    """M applied to x (bitmask of length a); result is a bitmask of length b."""
    mask = (1 << a) - 1
    out = 0
    for p in range(b):
        if parity((M >> (p * a)) & mask & x):
            out |= 1 << p
    return out


def outer(y, x, a, b):
    """The b x a matrix y x^T as a bitmask; <M, y x^T> = parity(M & y x^T) = y^T M x."""
    out = 0
    for p in range(b):
        if (y >> p) & 1:
            out |= x << (p * a)
    return out


def slice_dims(cons, a, b):
    """d_y = dim V_y for every y != 0, where W = span(cons)^perp, so W^perp = span(cons).

    V_y = {x : y x^T in W^perp}, and x -> y x^T is one-to-one, so
    d_y = dim(W^perp n {y x^T}) = rank(cons) + a - rank(cons + {y e_q^T})."""
    c = rank_f2(cons)
    return {y: c + a - rank_f2(list(cons) + [outer(y, 1 << q, a, b) for q in range(a)])
            for y in range(1, 1 << b)}


def slice_dims_direct(cons, a, b):
    """The same numbers straight from the definition of V_y (used by the tests)."""
    W = nullspace(cons, a * b)
    out = {}
    for y in range(1, 1 << b):
        V = [x for x in range(1 << a) if all(not parity(y & apply(M, x, a, b)) for M in W)]
        out[y] = len(V).bit_length() - 1
    return out


def bases_of(b):
    """Every basis of F_2^b, as a sorted tuple of b non-zero vectors, once each."""
    return [ys for ys in itertools.combinations(range(1, 1 << b), b) if rank_f2(list(ys)) == b]


def lemma19_report(a, b, max_codim, check_bases=True):
    """Lemma 19 over every W of codimension c <= max_codim in Hom(F_2^a, F_2^b)."""
    bases = bases_of(b) if check_bases else []
    out = {}
    for c in range(0, min(max_codim, a * b) + 1):
        r = {"spaces": 0, "min_d_hist": {}, "min_d_le_1_violations": 0,
             "basis_sum_violations": 0, "all_d_ge_2": 0, "all_d_ge_2_not_all_2": 0}
        for cons in subspaces(a * b, c):
            d = slice_dims(cons, a, b)
            m = min(d.values())
            r["spaces"] += 1
            r["min_d_hist"][str(m)] = r["min_d_hist"].get(str(m), 0) + 1
            if c < 2 * b and m > 1:
                r["min_d_le_1_violations"] += 1
            for ys in bases:
                if sum(d[y] for y in ys) > c:
                    r["basis_sum_violations"] += 1
            if m >= 2:
                r["all_d_ge_2"] += 1
                r["all_d_ge_2_not_all_2"] += any(v != 2 for v in d.values())
        out[c] = r
    return out


def lemma19_match(a, b, rep):
    ok = True
    for c, r in rep.items():
        ok = ok and r["spaces"] == gaussian_binomial(a * b, c)
        ok = ok and r["min_d_le_1_violations"] == 0 and r["basis_sum_violations"] == 0
        if c < 2 * b:
            ok = ok and r["all_d_ge_2"] == 0
        if c == 2 * b:
            ok = ok and r["all_d_ge_2"] == gaussian_binomial(a, 2) and r["all_d_ge_2_not_all_2"] == 0
    return ok


def case_bounds(a, b):
    """Largest bound on n = dim L/A over every case (s, dim S, r), versus 2a + 3b (e = 3).

    dim S = 0 gives exponent 4 (settled). Otherwise n <= a + s + 2b + r with r <= b(a - s)
    (Theorem 17); n <= a + 2b + 3 when dim S = 1 (Proposition 17); n <= 2a + 2b + 1 when b >= 1 and
    r >= b(a - 2) + 1 (Theorem 21 with Lemma 19)."""
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
                worst = max(worst, bound)
                if bound > need:
                    open_cases.append([s, dS, r, bound])
    return {"need": need, "max_bound": worst, "settled": worst <= need, "open": open_cases}


def settled_predicted(a, b):
    return b == 0 or (a - 3) * (b - 1) <= 1


# ---------- the group check (uses z4z2.py) ----------

def max_subspace_in(Z, n):
    """A largest subspace of F_2^n (vectors = int bitmasks) contained in the set Z (0 in Z)."""
    best = [{0}]

    def grow(span, start):
        if len(span) > len(best[0]):
            best[0] = span
        for v in range(start, 1 << n):
            if v in span:
                continue
            new = span | {s ^ v for s in span}
            if new <= Z:
                grow(new, v + 1)
    grow({0}, 1)
    return best[0]


def group_report(elems, mul, A4, A2):
    import z4z2
    e = z4z2.identity_of(elems, mul)
    elems = [e] + [x for x in elems if x != e]
    inv = {}
    for x in elems:
        if x not in inv:
            y = next(y for y in elems if mul(x, y) == e)
            inv[x], inv[y] = y, x
    a, b = len(A4), len(A2)
    k = a + b

    def power(g, m):
        out = e
        for _ in range(m):
            out = mul(out, g)
        return out
    gens = A4 + A2
    coord = {}
    for xs in itertools.product(*([range(4)] * a + [range(2)] * b)):
        g = e
        for gen, m in zip(gens, xs):
            g = mul(g, power(gen, m))
        coord[g] = xs
    coset_of, reps = {}, []
    for g in elems:
        if g not in coset_of:
            c = len(reps)
            reps.append(g)
            for x in coord:
                coset_of[mul(g, x)] = c
    nH = len(reps)
    act_ok = True
    D = []
    for g in reps:
        cols = []
        for x in A4:
            cc = coord[mul(mul(mul(g, x), inv[g]), inv[x])]
            act_ok &= all(v % 2 == 0 for v in cc[:a])
            cols.append(tuple(v // 2 for v in cc[:a]) + tuple(cc[a:]))
        D.append(tuple(tuple(cols[i][r] for i in range(a)) for r in range(k)))
    Q = [D[c][a:] for c in range(nH)]
    sigma = [tuple(v % 2 for v in coord[mul(g, g)][:a]) for g in reps]

    basis = z4z2.greedy_basis_cosets(reps, coset_of, mul, range(nH))
    n = len(basis)
    cid = []
    for x in range(1 << n):
        g = e
        for i in range(n):
            if (x >> i) & 1:
                g = mul(g, reps[basis[i]])
        cid.append(coset_of[g])
    coords_ok = sorted(cid) == list(range(nH))

    S = z4z2.span([sigma[c] for c in range(nH)], a)
    vecs = list(itertools.product(range(2), repeat=a))
    ys = [y for y in itertools.product(range(2), repeat=b) if any(y)]

    def yQ(y, c):
        return tuple(sum(y[p] * Q[c][p][i] for p in range(b)) % 2 for i in range(a))
    lemma17_violations, thm21_ok, slices = 0, True, {}
    for y in ys:
        rows = [yQ(y, c) for c in range(nH)]
        V = {x for x in vecs if all(sum(r[i] * x[i] for i in range(a)) % 2 == 0 for r in rows)}
        Ty = [c for c in range(nH) if not any(rows[c])]
        lemma17_violations += sum(1 for c in Ty if sigma[c] not in V)
        d = len(V).bit_length() - 1
        dS = len(V & S).bit_length() - 1
        if dS == 0:
            thm21_ok &= n <= 2 * a + 2 * b - d
        elif dS == 1:
            thm21_ok &= n <= 2 * a + 2 * b + 2 - d
        slices["".join(map(str, y))] = [d, dS, len(Ty).bit_length() - 1]
    zero = (0,) * a
    Z = {x for x in range(1 << n) if sigma[cid[x]] == zero}
    T = max_subspace_in(Z, n)
    t = len(T).bit_length() - 1
    Tc = {cid[x] for x in T}
    Y = [g for g in elems if coset_of[g] in Tc]
    zeros = sum(1 for g in Y if mul(g, g) == e)
    return {"a": a, "b": b, "n": n, "coords_ok": coords_ok, "action_ok": act_ok,
            "rank_Q": rank_f2([sum(Q[c][p][i] << (p * a + i) for p in range(b) for i in range(a))
                               for c in range(nH)]),
            "dim_S": len(S).bit_length() - 1, "slices (d_y, dim V_y n S, dim T_y)": slices,
            "lemma17_step_violations": lemma17_violations, "max_singular_dim": t,
            "lemma18_ok": t <= a + 2 * b, "squares_trivial_on_Y": zeros, "omega_order": 1 << k,
            "theorem21_ok": thm21_ok}


def group_checks():
    try:
        import z4z2
    except ImportError:
        return None
    out = {}
    for name, (E, mul, A4, A2), control in z4z2.groups():
        r = group_report(E, mul, A4, A2)
        r["control"] = control
        if control:
            r["match"] = r["squares_trivial_on_Y"] > r["omega_order"]
        else:
            r["match"] = (r["coords_ok"] and r["action_ok"] and r["lemma17_step_violations"] == 0
                          and r["lemma18_ok"] and r["theorem21_ok"]
                          and r["squares_trivial_on_Y"] == r["omega_order"])
        out[name] = r
        print(f"group {name}: {json.dumps(r, sort_keys=True)}", flush=True)
    return out


LEMMA19_CASES = [(1, 2, 4, True), (1, 3, 6, True), (2, 1, 2, True), (3, 1, 2, True),
                 (2, 2, 4, True), (3, 2, 4, True), (2, 3, 6, True), (4, 2, 4, True),
                 (2, 4, 8, False)]
BOUND_CASES = [(5, 2), (4, 3), (3, 4), (3, 5), (3, 8), (4, 2), (6, 2), (5, 3), (8, 1)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"lemma19": {}, "bounds": {}, "settled_table": {}, "groups": None}
    ok = True
    for a, b, cmax, cb in LEMMA19_CASES:
        rep = lemma19_report(a, b, cmax, check_bases=cb)
        match = lemma19_match(a, b, rep)
        out["lemma19"][f"{a},{b}"] = rep
        ok = ok and match
        for c, r in rep.items():
            print(f"lemma19 a={a} b={b} codim={c}: {json.dumps(r, sort_keys=True)}", flush=True)
        print(f"lemma19 a={a} b={b}: match {match}", flush=True)
    table_ok = True
    for a in range(1, 9):
        row = ""
        for b in range(0, 9):
            got = case_bounds(a, b)["settled"]
            table_ok = table_ok and got == settled_predicted(a, b)
            row += " Y" if got else " ."
            out["settled_table"][f"{a},{b}"] = got
        print(f"settled a={a}: b=0..8{row}", flush=True)
    print(f"settled table matches b = 0 or (a - 3)(b - 1) <= 1: {table_ok}", flush=True)
    ok = ok and table_ok
    for a, b in BOUND_CASES:
        r = case_bounds(a, b)
        out["bounds"][f"{a},{b}"] = r
        print(f"bounds a={a} b={b}: need {r['need']}, max {r['max_bound']}, settled {r['settled']}, "
              f"open (s, dim S, r, bound) {r['open']}", flush=True)
    ok = ok and out["bounds"]["3,4"]["settled"]
    ok = ok and out["bounds"]["5,2"]["open"] == [[2, d, 6, 17] for d in range(2, 6)]
    ok = ok and out["bounds"]["4,3"]["open"] == [[2, d, 6, 18] for d in range(2, 5)]
    groups = group_checks()
    out["groups"] = groups
    if groups is None:
        print("groups: z4z2.py not found, group check skipped", flush=True)
    else:
        ok = ok and all(r["match"] for r in groups.values())
    out["all_match"] = ok
    print(f"SUMMARY all_match {ok}, groups checked {groups is not None}")
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "thm21.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
