# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma 26, Theorem 24, Proposition 22 and Corollary 14 of finite-groups.md (section 14, version
1.7.7): the restriction at a vector u, M(3) = 3, anisotropic systems, and the settled cases.

Setting as in m3_core.py. X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Lemma 26: for u in V let U = {h : beta(h, u) = 0} and X1 = ker A_u. Then sigma(U) lies in X1, and
sigma on U, with h -> A_h restricted to X1 and projected onto X1, is again a system, with
dim X1 = t - rank A_u. If sigma(u) = 0, then codim U <= dim Fix(A_u) <= rank A_u. Theorem 24:
max(t, A(t)) <= M(t) <= t + max_(s <= t) (A(s) - s), where A(t) is the largest dim V of an
anisotropic system (sigma(h) != 0 for h != 0); so M(3) = 3 by the computed A(2) = 2 and A(3) = 3.
Proposition 22: if every A_h has rank <= 1, the A_h share an image line x0 (then beta takes values
in span(x0)) or a kernel hyperplane ker f0 (then f0(sigma) vanishes on a subspace of codimension
<= 2); this gives A(4) <= 6 and A(5) <= 8. Corollary 14: the case count of the group question.

Parts. cases: the bounds for A(t) and M(t) - t and the table of settled (a, b). lemma26: Lemma 26
and Theorem 24 on random systems with t = 2, 3, 4. rank1: Proposition 22(b) on every subspace C of
a common-image or common-kernel space of rank-1 matrices, t = 2, 3, 4. aniso4: a random search for
anisotropic systems with t = 4 and dim V = 5, 6, 7 over subspaces of singular matrices.

Vectors of F_2^m are int bitmasks; a t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c (0-based); a set of vectors is an int with bit x set for each x in it. Pure Python, no
dependencies; the helpers are copied from m3_core.py so that this file runs on its own.

Usage: python m3_exact.py [--out-dir DIR] [--part cases|lemma26|rank1|aniso4]
                          [--budget-minutes 20]
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


def random_subspace(rng, nbits, c):
    """Basis of a random c-dimensional subspace of F_2^nbits (c <= nbits)."""
    while True:
        B = independent([rng.randrange(1, 1 << nbits) for _ in range(c)])
        if len(B) == c:
            return B


# ---------- t x t matrices over F_2 ----------

def mat_apply(A, x, t):
    row_mask = (1 << t) - 1
    out = 0
    for r in range(t):
        if parity((A >> (t * r)) & row_mask & x):
            out |= 1 << r
    return out


def identity(t):
    return sum(1 << (t * i + i) for i in range(t))


def entries(t, cells):
    """The matrix with a 1 in each (r, c) of cells (0-based)."""
    return sum(1 << (t * r + c) for r, c in cells)


def rows_of(A, t):
    row_mask = (1 << t) - 1
    return [(A >> (t * r)) & row_mask for r in range(t)]


def is_singular(A, t):
    return rank_f2(rows_of(A, t)) < t


def mat_rank(A, t):
    return rank_f2(rows_of(A, t))


def kernel_basis(A, t):
    """Basis of ker A."""
    return nullspace(rows_of(A, t), t)


def fix_dim(A, t):
    """dim Fix(A) = dim ker(I + A)."""
    return len(kernel_basis(A ^ identity(t), t))


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


# ---------- vanishing subspaces ----------

def xor_masks(m):
    """xm[i] = the set of h in F_2^m with bit i equal to 0."""
    return [sum(1 << h for h in range(1 << m) if not (h >> i) & 1) for i in range(m)]


def xor_perm(x, v, xm):
    """The set {w ^ v : w in x}."""
    i = 0
    while v:
        if v & 1:
            s = 1 << i
            M = xm[i]
            x = ((x >> s) & M) | ((x & M) << s)
        v >>= 1
        i += 1
    return x


class _Limit(Exception):
    pass


def has_vanishing(zmask, need, xm, node_limit=200000):
    """(found, exact): is there a subspace of dimension >= need whose non-zero vectors all lie in
    zmask (a set of non-zero vectors)?"""
    if need <= 0:
        return True, True
    nodes = [0]

    def dfs(S, size, d, cand):
        # S = the current subspace (a set), size = 2^d; cand = the w with w + S inside zmask.
        if d >= need:
            return True
        nodes[0] += 1
        if nodes[0] > node_limit:
            raise _Limit
        lack = size * ((1 << (need - d)) - 1)
        while cand:
            if cand.bit_count() < lack:
                return False
            v = (cand & -cand).bit_length() - 1
            coset = xor_perm(S, v, xm)
            if dfs(S | coset, size * 2, d + 1, cand & xor_perm(cand, v, xm)):
                return True
            cand &= ~coset
        return False

    try:
        return dfs(1, 1, 0, zmask), True
    except _Limit:
        return False, False


def least_codim(zmask, m, xm, node_limit=200000):
    """(least codimension of a subspace of F_2^m inside zmask + {0}, exact flag). If the search is
    cut off, the first value is only an upper bound."""
    d = 0
    while d < m:
        found, exact = has_vanishing(zmask, d + 1, xm, node_limit)
        if not exact:
            return m - d, False
        if not found:
            break
        d += 1
    return m - d, True


def zero_set(sv):
    """The non-zero h with sv[h] = 0, as a set."""
    return sum(1 << h for h in range(1, len(sv)) if sv[h] == 0)


# ---------- Lemma 26 ----------

def restrict(at, sv, m, t, u):
    """The restriction of Lemma 26 at u. U = {h : beta(h, u) = 0}, X1 = ker A_u. Returns
    (Ub, X1b, at1, sv1, inside): bases of U and X1, the alpha and sigma tables of the projected
    system on U (coordinates of Ub in V, of X1b in X1), and whether sigma(U) lies in X1."""
    Ub = independent([h for h in range(1, 1 << m) if sv[h ^ u] ^ sv[h] ^ sv[u] == 0])
    X1b = kernel_basis(at[u], t)
    d = len(X1b)
    full = list(X1b)
    for i in range(t):
        if rank_f2(full + [1 << i]) > len(full):
            full.append(1 << i)
    coord = {combine(full, c): c for c in range(1 << t)}
    low = (1 << d) - 1
    at1, sv1 = [], []
    inside = True
    for x in range(1 << len(Ub)):
        h = combine(Ub, x)
        cs = coord[sv[h]]
        if cs >> d:
            inside = False
        sv1.append(cs & low)
        M = 0
        for col in range(d):
            img = coord[mat_apply(at[h], X1b[col], t)] & low
            for r in range(d):
                if (img >> r) & 1:
                    M |= 1 << (d * r + col)
        at1.append(M)
    return Ub, X1b, at1, sv1, inside


def lemma26_at(at, sv, m, t, u):
    """Lemma 26 at u: inside (sigma(U) <= ker A_u), system (the projected restriction satisfies
    (*)), rank A_u, dim Fix(A_u), codim U, k = dim U, d = dim X1 and the restricted table sv1."""
    Ub, X1b, at1, sv1, inside = restrict(at, sv, m, t, u)
    k, d = len(Ub), len(X1b)
    return {"inside": inside, "system": inside and is_system(at1, sv1, k, d),
            "rank": t - d, "fix": fix_dim(at[u], t), "codim": m - k, "k": k, "d": d,
            "sv1": sv1}


def lemma26_survey(budget_seconds, rng, count=360):
    start = time.time()
    st = {"systems": 0, "sigmas": 0, "checks": 0, "zero_checks": 0, "not_inside": 0,
          "not_system": 0, "codim_gt_fix": 0, "fix_gt_rank": 0, "restriction_violations": 0,
          "lc_over_bound": {}, "max_lc": {}, "inexact": 0, "aniso_max": {}, "finished": False}
    mmax = {2: 6, 3: 7, 4: 6}
    bound = {2: 2, 3: 3, 4: 6}          # Theorem 24: M(2) = 2, M(3) = 3, M(4) <= 6
    xms = {m: xor_masks(m) for m in range(0, 8)}
    tabs = {}
    plan = [2] * (count // 6) + [3] * (count // 2) + [4] * (count // 3)
    rng.shuffle(plan)
    for t in plan:
        if time.time() - start > budget_seconds:
            st["stopped_at"] = st["systems"]
            return st
        c = rng.randint(1, min(t * t - 1, mmax[t]))
        B = random_subspace(rng, t * t, c)
        y = rng.randint(0, min(t, mmax[t] - c))
        m, at = system(B, y)
        if m not in tabs:
            tabs[m] = mon_tables(m)
        sol = solve_sigma(at, m, t)
        st["systems"] += 1
        key = str(t)
        for _ in range(3 if sol else 0):
            sv = table(sigma_from_coeffs(combine(sol, rng.getrandbits(len(sol))), tabs[m], t), m)
            st["sigmas"] += 1
            lc, exact = least_codim(zero_set(sv), m, xms[m])
            if not exact:
                st["inexact"] += 1
            else:
                st["max_lc"][key] = max(st["max_lc"].get(key, 0), lc)
                if lc > bound[t]:
                    st["lc_over_bound"][key] = st["lc_over_bound"].get(key, 0) + 1
            zeros = [h for h in range(1, 1 << m) if sv[h] == 0]
            if not zeros:
                st["aniso_max"][key] = max(st["aniso_max"].get(key, 0), m)
            us = rng.sample(range(1, 1 << m), min(3, (1 << m) - 1)) + \
                rng.sample(zeros, min(3, len(zeros)))
            for u in us:
                r = lemma26_at(at, sv, m, t, u)
                st["checks"] += 1
                if not r["inside"]:
                    st["not_inside"] += 1
                elif not r["system"]:
                    st["not_system"] += 1
                if sv[u]:
                    continue
                st["zero_checks"] += 1
                if r["codim"] > r["fix"]:
                    st["codim_gt_fix"] += 1
                if r["fix"] > r["rank"]:
                    st["fix_gt_rank"] += 1
                if exact and r["inside"]:
                    lu, ex2 = least_codim(zero_set(r["sv1"]), r["k"], xms[r["k"]])
                    if ex2 and lc > r["codim"] + lu:
                        st["restriction_violations"] += 1
    st["finished"] = True
    return st


# ---------- Proposition 22(b): spaces of rank-1 matrices ----------

def rank1_survey(budget_seconds, rng, per=8):
    start = time.time()
    st = {"systems": 0, "sigmas": 0, "image_beta_outside_line": 0, "kernel_q_codim_gt_2": 0,
          "kernel_inexact": 0, "aniso_max": {}, "aniso_over_bound": 0, "finished": False}
    xms = {m: xor_masks(m) for m in range(0, 9)}
    tabs = {}
    for t in (2, 3, 4):
        kinds = (("image", [entries(t, [(0, c)]) for c in range(t)]),
                 ("kernel", [entries(t, [(r, 0)]) for r in range(t)]))
        for kind, gens in kinds:
            for c in range(1, t + 1):
                for rows in subspaces(t, c):
                    B = [combine(gens, r) for r in rows]
                    for y in range(0, min(t, 8 - c) + 1):
                        if time.time() - start > budget_seconds:
                            st["stopped_at"] = f"t={t} {kind} c={c} y={y}"
                            return st
                        m, at = system(B, y)
                        if m not in tabs:
                            tabs[m] = mon_tables(m)
                        sol = solve_sigma(at, m, t)
                        st["systems"] += 1
                        D = len(sol)
                        picks = range(1, 1 << D) if D <= 3 else \
                            [rng.randrange(1, 1 << D) for _ in range(per)]
                        for p in picks:
                            sv = table(sigma_from_coeffs(combine(sol, p), tabs[m], t), m)
                            st["sigmas"] += 1
                            if kind == "image":
                                if any((sv[h ^ hp] ^ sv[h] ^ sv[hp]) >> 1
                                       for h in range(1 << m) for hp in range(h)):
                                    st["image_beta_outside_line"] += 1
                            else:
                                zq = sum(1 << h for h in range(1, 1 << m) if not sv[h] & 1)
                                found, exact = has_vanishing(zq, m - 2, xms[m])
                                if not exact:
                                    st["kernel_inexact"] += 1
                                elif not found:
                                    st["kernel_q_codim_gt_2"] += 1
                            if not zero_set(sv):
                                key = f"{t} {kind}"
                                st["aniso_max"][key] = max(st["aniso_max"].get(key, 0), m)
                                if m > (t if kind == "image" else t + 1):
                                    st["aniso_over_bound"] += 1
    st["finished"] = True
    return st


# ---------- anisotropic systems with t = 4 ----------

def singular_subspace(rng, t, c, kind):
    """A random c-dimensional subspace of M_t(F_2) whose non-zero elements are all singular:
    kills_e0 (every matrix kills e_0), into_H (every image lies in x_0 = 0) or filtered random."""
    n2 = t * t
    col0 = sum(1 << (t * r) for r in range(t))
    row0 = (1 << t) - 1
    for _ in range(200000):
        gens = [rng.randrange(1, 1 << n2) for _ in range(c)]
        if kind == "kills_e0":
            gens = [g & ~col0 for g in gens]
        elif kind == "into_H":
            gens = [g & ~row0 for g in gens]
        B = independent([g for g in gens if g])
        if len(B) == c and all(is_singular(combine(B, i), t) for i in range(1, 1 << c)):
            return B
    return None


def aniso_count(sol, tabs, m, t, rng, cap=16, samples=20000):
    """(solutions examined, anisotropic ones, exhaustive?)."""
    D = len(sol)
    if D == 0:
        return 0, 0, True
    full = (1 << (1 << m)) - 1
    sm = [sigma_from_coeffs(v, tabs, t) for v in sol]
    found = 0
    if D <= cap:
        cur = [0] * t
        for i in range(1, 1 << D):
            j = (i & -i).bit_length() - 1
            cur = [a ^ b for a, b in zip(cur, sm[j])]
            nz = 0
            for q in cur:
                nz |= q
            if nz | 1 == full:
                found += 1
        return (1 << D) - 1, found, True
    for _ in range(samples):
        S = sigma_from_coeffs(combine(sol, rng.randrange(1, 1 << D)), tabs, t)
        nz = 0
        for q in S:
            nz |= q
        if nz | 1 == full:
            found += 1
    return samples, found, False


def aniso4_survey(budget_seconds, rng):
    start = time.time()
    t = 4
    st = {"systems": 0, "solutions": 0, "sampled_systems": 0, "by_m": {}, "found": [],
          "finished": False}
    tabs = {}
    plan = []
    for m, reps in ((5, 60), (6, 20), (7, 4)):
        for c in range(1, min(m, 6) + 1):
            if m - c > t:
                continue
            for kind in ("kills_e0", "into_H", "random"):
                if kind == "random" and c > 4:
                    continue
                plan += [(m, c, kind)] * reps
    rng.shuffle(plan)
    for m, c, kind in plan:
        if time.time() - start > budget_seconds:
            st["stopped_at"] = st["systems"]
            return st
        B = singular_subspace(rng, t, c, kind)
        if B is None:
            continue
        mm, at = system(B, m - c)
        if mm not in tabs:
            tabs[mm] = mon_tables(mm)
        sol = solve_sigma(at, mm, t)
        n, found, exhaustive = aniso_count(sol, tabs[mm], mm, t, rng)
        st["systems"] += 1
        st["solutions"] += n
        if not exhaustive:
            st["sampled_systems"] += 1
        key = str(mm)
        rec = st["by_m"].setdefault(key, {"systems": 0, "aniso_systems": 0, "aniso_solutions": 0})
        rec["systems"] += 1
        if found:
            rec["aniso_systems"] += 1
            rec["aniso_solutions"] += found
            if len(st["found"]) < 10:
                st["found"].append({"m": mm, "kind": kind, "C": B, "count": found})
    st["finished"] = True
    return st


# ---------- Corollary 14: the case count ----------

def a_bounds(tmax):
    """Upper bounds for A(t), t = 0..tmax: A(1), A(2), A(3) = 1, 2, 3 (Lemma 22, Proposition 21),
    then A(t) <= min(2t, max(t, 2 + A(t - 1), t + A(t - 2))) (Proposition 22)."""
    A = [0, 1, 2, 3]
    for t in range(4, tmax + 1):
        A.append(min(2 * t, max(t, 2 + A[t - 1], t + A[t - 2])))
    return A[:tmax + 1]


def e_bounds(tmax):
    """E[t] >= M(t) - t, by Theorem 24: E[t] = max over s <= t of (A(s) - s)."""
    A = a_bounds(tmax)
    out, best = [], 0
    for t in range(tmax + 1):
        best = max(best, A[t] - t)
        out.append(best)
    return out


def settled(a, b):
    """Corollary 14: does Z_4^a x Z_2^b follow from Theorems 16, 17, Lemma 19, Proposition 20 and
    the bounds M(t) <= t + E[t]? tau = the largest t <= a with E[s] <= b for every s <= t."""
    if b <= 1:
        return True
    E = e_bounds(a)
    tau = 0
    while tau < a and E[tau + 1] <= b:
        tau += 1
    return (a - tau - 2) * (b - 1) <= 1


def cases():
    A, E = a_bounds(12), e_bounds(12)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "graded": {"a_bounds": A[:7] == [0, 1, 2, 3, 6, 8, 12],
                       "e_bounds": E[:7] == [0, 0, 0, 0, 2, 3, 6],
                       "corollary14": all(v == (b <= 1 or a <= max(7, b + 2))
                                          for (a, b), v in grid.items()),
                       "contains_corollary13": all(v for (a, b), v in grid.items()
                                                   if b == 0 or (a - 4) * (b - 1) <= 1)}}


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["cases", "lemma26", "rank1", "aniso4"], default="cases")
    ap.add_argument("--budget-minutes", type=float, default=20.0)
    args = ap.parse_args()
    rng = random.Random(26)
    budget = args.budget_minutes * 60
    if args.part == "cases":
        out = cases()
        graded = out["graded"]
        print(f"cases: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY cases all_match {all(graded.values())}", flush=True)
        write_out(out, args.out_dir, "cases.json")
    elif args.part == "lemma26":
        st = lemma26_survey(budget, rng)
        graded = {"inside": st["not_inside"] == 0, "system": st["not_system"] == 0,
                  "codim_le_fix": st["codim_gt_fix"] == 0, "fix_le_rank": st["fix_gt_rank"] == 0,
                  "restriction": st["restriction_violations"] == 0,
                  "theorem24": not st["lc_over_bound"],
                  "aniso_le_t": all(v <= int(k) for k, v in st["aniso_max"].items()
                                    if int(k) <= 3),
                  "finished": st["finished"]}
        explore = {"max_lc": st["max_lc"], "aniso_max": st["aniso_max"],
                   "inexact": st["inexact"]}
        print(f"lemma26: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY lemma26 all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded, "exploratory": explore}, args.out_dir,
                  "lemma26.json")
    elif args.part == "rank1":
        st = rank1_survey(budget, rng)
        graded = {"image_beta_in_line": st["image_beta_outside_line"] == 0,
                  "kernel_q_codim_le_2": st["kernel_q_codim_gt_2"] == 0,
                  "aniso_bounds": st["aniso_over_bound"] == 0, "finished": st["finished"]}
        print(f"rank1: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"SUMMARY rank1 all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded}, args.out_dir, "rank1.json")
    else:
        st = aniso4_survey(budget, rng)
        m7 = st["by_m"].get("7", {"aniso_systems": 0})
        graded = {"none_with_dim_7": m7["aniso_systems"] == 0}
        explore = {k: v for k, v in st["by_m"].items()}
        print(f"aniso4: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY aniso4 finished {st['finished']} dim5 "
              f"{st['by_m'].get('5', {}).get('aniso_systems', 0)} dim6 "
              f"{st['by_m'].get('6', {}).get('aniso_systems', 0)} dim7 "
              f"{m7['aniso_systems']}", flush=True)
        write_out({"stats": st, "graded": graded, "exploratory": explore}, args.out_dir,
                  "aniso4.json")


if __name__ == "__main__":
    main()
