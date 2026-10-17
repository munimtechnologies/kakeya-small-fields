# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma 30, Theorem 26, Proposition 24 and Corollary 17 of notes/rank-restriction.md (version
1.7.10 of section 14 of finite-groups.md): a sharper restriction at a vector, A(4) = 4, and the
settled cases.

Setting as in m4_irred.py. X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Lemma 30: let u be in V, x0 = sigma(u), phi = beta(u, .) and U+ = {h : phi(h) in span(x0)}.
(a) For every system and every h in U+, A_h x0 = phi(h) and A_u sigma(h) = 0.
(b) If the system is anisotropic and u != 0, then codim U+ <= t - 1, sigma(h) is not in span(x0)
for h in U+ outside span(u), and dim U+ <= 1 + A(t - rank A_u - 1). So dim V <= t + A(t - rho - 1)
for every rank rho of an element, and an element of rank t - 1 gives dim V <= t.

Parts. lemma30: random systems with t = 3, 4, 5 (random spaces, spaces of matrices of rank t - 1,
and the diagonal system of Lemma 23(d)); (a) is checked at sampled vectors of every solution, and (b)
at every vector of random maximal anisotropic subspaces. cases: the bounds of Proposition 24 and the
table of settled (a, b) (Corollary 17). control: random pairs (alpha, sigma) that are not systems
break (a), and random anisotropic maps that are not systems break the rank t - 1 claim of (b).

Vectors of F_2^m are int bitmasks; a t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c (0-based). Pure Python, no dependencies; the helpers are copied from m4_irred.py so that this
file runs on its own.

Usage: python m6_sharp.py [--out-dir DIR] [--part lemma30|cases|control] [--budget-minutes 20]
"""
import argparse
import itertools
import json
import os
import random
import time


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


def independent(gens):
    """A maximal independent subset of gens, in order."""
    out = []
    for g in gens:
        if rank_f2(out + [g]) > len(out):
            out.append(g)
    return out


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


# ---------- t x t matrices over F_2 ----------

def mat_apply(A, x, t):
    row_mask = (1 << t) - 1
    out = 0
    for r in range(t):
        if parity((A >> (t * r)) & row_mask & x):
            out |= 1 << r
    return out


def entries(t, cells):
    """The matrix with a 1 in each (r, c) of cells (0-based)."""
    return sum(1 << (t * r + c) for r, c in cells)


def rows_of(A, t):
    row_mask = (1 << t) - 1
    return [(A >> (t * r)) & row_mask for r in range(t)]


def mat_rank(A, t):
    return rank_f2(rows_of(A, t))


# ---------- quadratic maps V -> F_2^t ----------

def monomials(m):
    return [(i, i) for i in range(m)] + list(itertools.combinations(range(m), 2))


def mon_tables(m):
    return [sum(1 << h for h in range(1 << m) if (h >> i) & 1 and (h >> j) & 1)
            for i, j in monomials(m)]


def sigma_from_coeffs(c, tabs, t):
    """sigma for the coefficient vector c, as t masks over h (bit h of mask i = coordinate i)."""
    N = len(tabs)
    return tuple(combine(tabs, (c >> (i * N)) & ((1 << N) - 1)) for i in range(t))


def sig(S, h):
    out = 0
    for i, q in enumerate(S):
        out |= ((q >> h) & 1) << i
    return out


def table(S, m):
    """Value table [sigma(h) for h in V] of the masks S."""
    return [sig(S, h) for h in range(1 << m)]


def system(Cbasis, y):
    """(m, alpha table) for V = F_2^(c + y), alpha = basis combination of the first c coordinates."""
    c = len(Cbasis)
    m = c + y
    cmask = (1 << c) - 1
    return m, [combine(Cbasis, h & cmask) for h in range(1 << m)]


def solve_sigma(at, m, t):
    """Basis (coefficient vectors) of every sigma satisfying (*) for the alpha table at."""
    mons = monomials(m)
    N = len(mons)
    w2 = [0] + [1 << i for i in range(m)] + [(1 << i) | (1 << j)
                                            for i, j in itertools.combinations(range(m), 2)]
    pairs = [(h, 1 << i) for h in w2 for i in range(m)]
    rows = [0] * (t * len(pairs))
    for u in range(t * N):
        comp, k = divmod(u, N)
        i, j = mons[k]
        bit = 1 << u
        for p, (h, hp) in enumerate(pairs):
            s = (((h >> i) & 1) & ((h >> j) & 1)) << comp
            pol = 0 if i == j else ((((h >> i) & 1) & ((hp >> j) & 1))
                                    ^ (((h >> j) & 1) & ((hp >> i) & 1)))
            if not s and not pol:
                continue
            bb = pol << comp
            e = mat_apply(at[hp], s, t) ^ bb ^ mat_apply(at[h], bb, t)
            r = 0
            while e:
                if e & 1:
                    rows[t * p + r] |= bit
                e >>= 1
                r += 1
    return nullspace(rows, t * N)


def is_system(at, sv, m, t):
    """Does (*) hold for the alpha table at and the value table sv on F_2^m?"""
    for h in range(1 << m):
        s = sv[h]
        for hp in range(1 << m):
            b = sv[h ^ hp] ^ s ^ sv[hp]
            if mat_apply(at[hp], s, t) != b ^ mat_apply(at[h], b, t):
                return False
    return True


# ---------- Lemma 30 ----------

def restrict(at, sv, basis):
    """(k, alpha table, value table) of the system restricted to span(basis), in its coordinates."""
    vals = [combine(basis, c) for c in range(1 << len(basis))]
    return len(basis), [at[v] for v in vals], [sv[v] for v in vals]


def anisotropic(sv):
    return all(sv[h] for h in range(1, len(sv)))


def greedy_anisotropic(sv, m, rng):
    """Basis of a maximal subspace of F_2^m on which sigma has no non-zero zero (random order)."""
    order = list(range(1, 1 << m))
    rng.shuffle(order)
    basis, span, seen = [], [0], {0}
    for v in order:
        if v in seen or not sv[v]:
            continue
        new = [v ^ w for w in span]
        if all(sv[x] for x in new):
            basis.append(v)
            span += new
            seen.update(new)
    return basis


def lemma30_check(at, sv, m, t, u):
    """The quantities of Lemma 30 at u."""
    x0, A = sv[u], at[u]
    phi = [sv[u ^ h] ^ x0 ^ sv[h] for h in range(1 << m)]
    plus = [h for h in range(1 << m) if phi[h] == 0 or phi[h] == x0]
    dim_plus = len(plus).bit_length() - 1
    return {"a": all(mat_apply(at[h], x0, t) == phi[h] and mat_apply(A, sv[h], t) == 0
                     for h in plus),
            "rho": mat_rank(A, t), "dim_plus": dim_plus, "codim_plus": m - dim_plus,
            "image": rank_f2([phi[1 << i] for i in range(m)]),
            "x0_in_image": x0 != 0 and x0 in phi,
            "outside": all(sv[h] != 0 and sv[h] != x0 for h in plus if h not in (0, u))}


KNOWN_A = [0, 1, 2, 3, 4]   # A(s) = s for s <= 4 (A(4) = 4 is Theorem 26)


def grade_aniso(r, m, t):
    """Lemma 30(b) at a non-zero u of an anisotropic system with dim V = m."""
    s = t - r["rho"] - 1
    return {"a": r["a"], "codim": r["codim_plus"] <= t - 1, "outside": r["outside"],
            "dim": 0 <= s and r["dim_plus"] <= 1 + KNOWN_A[s],
            "top_rank": r["rho"] != t - 1 or not r["x0_in_image"],
            "bound": 0 <= s and m <= t + KNOWN_A[s]}


def diagonal(t):
    """Lemma 23(d): V = F_2^(2t) with u in bits 0..t-1 and v in bits t..2t-1, A_h = diag(u),
    sigma_i = (1 + u_i) v_i."""
    at, sv = [], []
    for h in range(1 << (2 * t)):
        u, v = h & ((1 << t) - 1), h >> t
        at.append(sum(1 << (t * i + i) for i in range(t) if (u >> i) & 1))
        sv.append(~u & v & ((1 << t) - 1))
    return 2 * t, at, sv


def random_matrix(rng, t, kind):
    while True:
        A = rng.getrandbits(t * t)
        if kind != "singular" or mat_rank(A, t) == t - 1:
            return A


def lemma30_survey(budget_seconds, rng, plan=((3, 150), (4, 150), (5, 90)), samples=48):
    start = time.time()
    st = {"finished": False, "by_t": {}}
    for t, count in plan:
        s = {"systems": 0, "solutions": 0, "a_checks": 0, "a_fail": 0, "subspaces": 0,
             "restrict_fail": 0, "u_checks": 0, "fail": {}, "max_dim": {}, "by_rho": {},
             "x0_in_image_by_rho": {}, "equality": 0, "examples": []}
        st["by_t"][str(t)] = s
        for i in range(count):
            if time.time() - start > budget_seconds:
                return st
            kind = ("random", "singular", "diagonal")[i % 3]
            if kind == "diagonal":
                m, at, sv = diagonal(t)
                sols = [sv]
            else:
                B = independent([random_matrix(rng, t, kind) for _ in range(rng.randint(1, 4))])
                m, at = system(B, rng.randint(0, min(2, 6 - len(B))))
                tabs = mon_tables(m)
                sol = solve_sigma(at, m, t)
                sols = [table(sigma_from_coeffs(combine(sol, rng.getrandbits(len(sol))), tabs, t),
                              m) for _ in range(3 if sol else 0)]
            s["systems"] += 1
            for sv in sols:
                s["solutions"] += 1
                for u in rng.sample(range(1 << m), min(samples, 1 << m)):
                    s["a_checks"] += 1
                    if not lemma30_check(at, sv, m, t, u)["a"]:
                        s["a_fail"] += 1
                for _ in range(3):
                    basis = greedy_anisotropic(sv, m, rng)
                    if not basis:
                        continue
                    k, at_w, sv_w = restrict(at, sv, basis)
                    s["subspaces"] += 1
                    s["max_dim"][str(k)] = s["max_dim"].get(str(k), 0) + 1
                    if not (is_system(at_w, sv_w, k, t) and anisotropic(sv_w)):
                        s["restrict_fail"] += 1
                        continue
                    for u in range(1, 1 << k):
                        r = lemma30_check(at_w, sv_w, k, t, u)
                        s["u_checks"] += 1
                        rho = str(r["rho"])
                        s["by_rho"][rho] = s["by_rho"].get(rho, 0) + 1
                        if r["x0_in_image"]:
                            s["x0_in_image_by_rho"][rho] = s["x0_in_image_by_rho"].get(rho, 0) + 1
                        if r["codim_plus"] == t - 1 and r["dim_plus"] == 1 + KNOWN_A[
                                max(0, t - r["rho"] - 1)]:
                            s["equality"] += 1
                        for key, ok in grade_aniso(r, k, t).items():
                            if not ok:
                                s["fail"][key] = s["fail"].get(key, 0) + 1
                                if len(s["examples"]) < 5:
                                    s["examples"].append({"at": at_w, "sv": sv_w, "u": u})
    st["finished"] = True
    return st


# ---------- Proposition 24 and Corollary 17 ----------

def bounds(tmax):
    """Upper bounds A[t] >= A(t) and E[t] >= M(t) - t for t = 0..tmax (Proposition 24):
    A(1), A(2), A(3) = 1, 2, 3, and for t >= 4
    A(t) <= min(2t, max(t, t + A(t - 4), max over 0 < d < t of M(t - d) + A(d))),
    with M(s) <= s + E(s) and E(s) = max over r <= s of (A(r) - r) (Theorem 24)."""
    A, E = [0, 1, 2, 3], [0, 0, 0, 0]
    for t in range(4, tmax + 1):
        red = max(t - d + E[t - d] + A[d] for d in range(1, t))
        A.append(min(2 * t, max(t, t + A[t - 4], red)))
        E.append(max(E[t - 1], A[t] - t))
    return A[:tmax + 1], E[:tmax + 1]


def settled(a, b):
    """Corollary 17 (the count of Corollary 14 with the bounds of Proposition 24): tau = the largest
    t <= a with E[s] <= b for every s <= t."""
    if b <= 1:
        return True
    E = bounds(a)[1]
    tau = 0
    while tau < a and E[tau + 1] <= b:
        tau += 1
    return (a - tau - 2) * (b - 1) <= 1


EXTRA17 = {(10, 4), (10, 5), (10, 6), (11, 6), (10, 7), (11, 7), (11, 8), (12, 8), (12, 9),
           (13, 10)}
EXTRA16 = {(9, 5), (9, 6), (10, 7)}


def cases():
    A, E = bounds(14)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "graded": {"a_bounds": A[:13] == [0, 1, 2, 3, 4, 6, 8, 10, 12, 15, 18, 21, 24],
                       "e_bounds": E[:13] == [0, 0, 0, 0, 0, 1, 2, 3, 4, 6, 8, 10, 12],
                       "corollary17": all(v == (b <= 1 or a <= max(9, b + 2) or (a, b) in EXTRA17)
                                          for (a, b), v in grid.items()),
                       "contains_corollary16": all(v for (a, b), v in grid.items()
                                                   if b <= 1 or a <= max(8, b + 2)
                                                   or (a, b) in EXTRA16)}}


# ---------- control ----------

def control(rng, count=300):
    """(i) random (alpha, sigma) on F_2^4 with t = 3 that are not systems: (a) fails at some u.
    (ii) random anisotropic quadratic maps F_2^3 -> F_2^3 with random alpha (not systems): some u
    with rank A_u = 2 has sigma(u) in beta(u, V), which Lemma 30(b) rules out for systems."""
    t, m = 3, 4
    tabs = mon_tables(m)
    st = {"pairs": 0, "systems": 0, "a_broken": 0, "aniso_maps": 0, "top_rank_u": 0,
          "top_rank_broken": 0}
    for _ in range(count):
        m_, at = system([rng.getrandbits(t * t) for _ in range(m)], 0)
        sv = table(sigma_from_coeffs(rng.getrandbits(t * len(tabs)), tabs, t), m)
        st["pairs"] += 1
        if is_system(at, sv, m, t):
            st["systems"] += 1
        if any(not lemma30_check(at, sv, m, t, u)["a"] for u in range(1, 1 << m)):
            st["a_broken"] += 1
    m3, tabs3 = 3, mon_tables(3)
    while st["aniso_maps"] < count:
        sv = table(sigma_from_coeffs(rng.getrandbits(t * len(tabs3)), tabs3, t), m3)
        if not anisotropic(sv):
            continue
        st["aniso_maps"] += 1
        m_, at = system([random_matrix(rng, t, "singular") for _ in range(m3)], 0)
        for u in range(1, 1 << m3):
            r = lemma30_check(at, sv, m3, t, u)
            if r["rho"] == t - 1:
                st["top_rank_u"] += 1
                if r["x0_in_image"]:
                    st["top_rank_broken"] += 1
    st["graded"] = {"no_systems": st["systems"] == 0, "a_broken_most": st["a_broken"] >= 250,
                    "top_rank_broken_some": st["top_rank_broken"] > 0}
    return st


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["lemma30", "cases", "control"], default="cases")
    ap.add_argument("--budget-minutes", type=float, default=20.0)
    args = ap.parse_args()
    rng = random.Random(30)
    budget = args.budget_minutes * 60
    if args.part == "cases":
        out = cases()
        print(f"cases: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY cases all_match {all(out['graded'].values())}", flush=True)
        write_out(out, args.out_dir, "cases.json")
    elif args.part == "lemma30":
        st = lemma30_survey(budget, rng)
        by = st["by_t"]
        graded = {f"t{t}_{k}": by.get(t, {}).get(k, 1) == 0
                  for t in ("3", "4", "5") for k in ("a_fail", "restrict_fail")}
        graded.update({f"t{t}_fail_none": t in by and not by[t]["fail"] for t in ("3", "4", "5")})
        graded["finished"] = st["finished"]
        explore = {t: {k: s[k] for k in ("systems", "solutions", "a_checks", "subspaces",
                                         "u_checks", "max_dim", "by_rho", "x0_in_image_by_rho",
                                         "equality")} for t, s in by.items()}
        print(f"lemma30: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY lemma30 all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded, "exploratory": explore}, args.out_dir,
                  "lemma30.json")
    else:
        out = control(rng)
        print(f"control: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY control all_match {all(out['graded'].values())}", flush=True)
        write_out(out, args.out_dir, "control.json")


if __name__ == "__main__":
    main()
