# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma 27, Lemma 28 and Corollary 15 of finite-groups.md (section 14, version 1.7.8): invariant
subspaces, a hyperplane mapped into a line, and where an anisotropic system with dim V > t must live.

Setting as in m3_exact.py. X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Lemma 27: if Y = span(e_0, ..., e_(d-1)) is invariant under every A_h, then sigma modulo Y (with the
lower right blocks of the A_h) is a system with t - d, and on every subspace U where sigma modulo Y
vanishes, sigma (with the upper left blocks) is a system with d. So LC(V) <= M(t - d) + M(d), and an
anisotropic system has dim V <= M(t - d) + A(d); with M(s) = A(s) = s for s <= 3 both are <= t when
t <= 4. Lemma 28: if every A_h maps P = span(e_1, ..., e_(t-1)) into span(e_0), let tau = sigma_0
and pi(h) = the P-part of A_h e_0. Then tau(h) pi(h) = 0; if pi != 0, tau vanishes on a subspace W
of codimension <= 1 and beta = 0 on W; LC(V) <= t; an anisotropic system has dim V <= t.

Parts. lemma27: random systems with t = 3, 4 whose alpha(V) keeps Y invariant. lemma28: random
systems with t = 3, 4 whose alpha(V) maps P into span(e_0). irred4: a random search for anisotropic
systems with t = 4 and dim V = 5, 6 over irreducible spaces of singular matrices (subspaces of the
compression spaces of types (1, 1), (1, 2), (2, 1), and random ones), with reducible spaces as a
graded control. control: random quadratic maps F_2^5 -> F_2^4; many are anisotropic, so it is the
identity (*) that rules such maps out.

Vectors of F_2^m are int bitmasks; a t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c (0-based); a set of vectors is an int with bit x set for each x in it. Pure Python, no
dependencies; the helpers are copied from m3_exact.py so that this file runs on its own.

Usage: python m4_irred.py [--out-dir DIR] [--part lemma27|lemma28|irred4|control]
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


def find_vanishing(zmask, need, xm, node_limit=200000):
    """(S, exact): S is the set of a subspace of dimension >= need whose non-zero vectors all lie
    in zmask (a set of non-zero vectors), or None if there is none."""
    if need <= 0:
        return 1, True
    nodes = [0]

    def dfs(S, size, d, cand):
        # S = the current subspace (a set), size = 2^d; cand = the w with w + S inside zmask.
        if d >= need:
            return S
        nodes[0] += 1
        if nodes[0] > node_limit:
            raise _Limit
        lack = size * ((1 << (need - d)) - 1)
        while cand:
            if cand.bit_count() < lack:
                return None
            v = (cand & -cand).bit_length() - 1
            coset = xor_perm(S, v, xm)
            got = dfs(S | coset, size * 2, d + 1, cand & xor_perm(cand, v, xm))
            if got is not None:
                return got
            cand &= ~coset
        return None

    try:
        return dfs(1, 1, 0, zmask), True
    except _Limit:
        return None, False


def least_codim(zmask, m, xm, node_limit=200000):
    """(least codimension of a subspace of F_2^m inside zmask + {0}, exact flag). If the search is
    cut off, the first value is only an upper bound."""
    d = 0
    while d < m:
        S, exact = find_vanishing(zmask, d + 1, xm, node_limit)
        if not exact:
            return m - d, False
        if S is None:
            break
        d += 1
    return m - d, True


def vanishing_basis(zmask, m, xm, node_limit=200000):
    """(basis, exact): a basis of a largest subspace of F_2^m inside zmask + {0}."""
    best = 1
    d = 0
    while d < m:
        S, exact = find_vanishing(zmask, d + 1, xm, node_limit)
        if not exact:
            return None, False
        if S is None:
            break
        best = S
        d += 1
    return independent([h for h in range(1, 1 << m) if (best >> h) & 1]), True


def zero_set(sv):
    """The non-zero h with sv[h] = 0, as a set."""
    return sum(1 << h for h in range(1, len(sv)) if sv[h] == 0)


# ---------- blocks, compression spaces, invariant subspaces ----------

def block_mask(t, d):
    """The matrices that map Y = span(e_0, ..., e_(d-1)) into itself."""
    return sum(1 << (t * r + c) for r in range(t) for c in range(t) if not c < d <= r)


def compression_mask(t, i, j):
    """The matrices that map P = span(e_i, ..., e_(t-1)) into Q = span(e_0, ..., e_(j-1))."""
    return sum(1 << (t * r + c) for r in range(t) for c in range(t) if c < i or r < j)


def block(A, t, lo, hi):
    """The square block of A on the coordinates lo, ..., hi - 1, as a (hi - lo)^2-bit matrix."""
    k = hi - lo
    out = 0
    for r in range(k):
        for c in range(k):
            if (A >> (t * (r + lo) + c + lo)) & 1:
                out |= 1 << (k * r + c)
    return out


def proper_subspaces(t):
    """Every subspace of F_2^t other than 0 and F_2^t, as a reduced echelon basis."""
    return [rows for d in range(1, t) for rows in subspaces(t, d)]


def is_irreducible(B, t, subs):
    """Is no subspace in subs invariant under every matrix of the basis B?"""
    for Y in subs:
        if all(rank_f2(Y + [mat_apply(A, y, t)]) == len(Y) for A in B for y in Y):
            return False
    return True


def restrict(at, sv, Ub, t, lo, hi):
    """The tables over span(Ub) (coordinates of Ub) of sigma on the coordinates lo, ..., hi - 1,
    shifted down by lo, and of the blocks of A_h on them; and whether sigma has no other
    non-zero coordinate there."""
    k = hi - lo
    keep = ((1 << k) - 1) << lo
    at1, sv1, inside = [], [], True
    for x in range(1 << len(Ub)):
        h = combine(Ub, x)
        if sv[h] & ~keep:
            inside = False
        sv1.append((sv[h] & keep) >> lo)
        at1.append(block(at[h], t, lo, hi))
    return at1, sv1, inside


# ---------- Lemma 27 ----------

def lemma27_check(at, sv, m, t, d, xms):
    """Lemma 27 for the invariant Y = span(e_0, ..., e_(d-1)) on one solution: the quotient system,
    a largest U where it vanishes, the system on U, and the codimensions."""
    full = [1 << i for i in range(m)]
    atq, svq, _ = restrict(at, sv, full, t, d, t)
    Ub, ex1 = vanishing_basis(zero_set(svq), m, xms[m])
    lc, ex2 = least_codim(zero_set(sv), m, xms[m])
    out = {"quotient": is_system(atq, svq, m, t - d), "exact": ex1 and ex2, "lc": lc,
           "aniso": not zero_set(sv)}
    if ex1:
        k = len(Ub)
        at1, sv1, inside = restrict(at, sv, Ub, t, 0, d)
        lc1, ex3 = least_codim(zero_set(sv1), k, xms[k])
        out.update(inside=inside, restricted=inside and is_system(at1, sv1, k, d),
                   codim_q=m - k, lc_u=lc1, exact=out["exact"] and ex3)
    return out


def lemma27_survey(budget_seconds, rng, count=240):
    start = time.time()
    st = {"systems": 0, "sigmas": 0, "not_quotient": 0, "not_inside": 0, "not_restricted": 0,
          "split_violations": 0, "codim_q_over": 0, "lc_u_over": 0, "lc_over_t": 0,
          "aniso_over_t": 0, "inexact": 0, "max_lc": {}, "aniso_max": {}, "finished": False}
    xms = {m: xor_masks(m) for m in range(0, 8)}
    tabs = {}
    mmax = {3: 7, 4: 6}
    for n in range(count):
        if time.time() - start > budget_seconds:
            st["stopped_at"] = n
            return st
        t = 3 if n % 2 else 4
        d = rng.randint(1, t - 1)
        mask = block_mask(t, d)
        c = rng.randint(1, mmax[t])
        y = rng.randint(0, min(t, mmax[t] - c))
        B = independent([rng.randrange(1, 1 << (t * t)) & mask for _ in range(c)])
        m, at = system(B, y)
        if m == 0:
            continue
        if m not in tabs:
            tabs[m] = mon_tables(m)
        sol = solve_sigma(at, m, t)
        st["systems"] += 1
        key = str(t)
        for _ in range(3 if sol else 0):
            sv = table(sigma_from_coeffs(combine(sol, rng.getrandbits(len(sol))), tabs[m], t), m)
            st["sigmas"] += 1
            r = lemma27_check(at, sv, m, t, d, xms)
            if not r["quotient"]:
                st["not_quotient"] += 1
            if "inside" in r and not r["inside"]:
                st["not_inside"] += 1
            elif "restricted" in r and not r["restricted"]:
                st["not_restricted"] += 1
            if not r["exact"]:
                st["inexact"] += 1
                continue
            st["max_lc"][key] = max(st["max_lc"].get(key, 0), r["lc"])
            if r["lc"] > r["codim_q"] + r["lc_u"]:
                st["split_violations"] += 1
            if r["codim_q"] > t - d:            # M(t - d) = t - d for t - d <= 3
                st["codim_q_over"] += 1
            if r["lc_u"] > d:                   # M(d) = d for d <= 3
                st["lc_u_over"] += 1
            if r["lc"] > t:
                st["lc_over_t"] += 1
            if r["aniso"]:
                st["aniso_max"][key] = max(st["aniso_max"].get(key, 0), m)
                if m > t:
                    st["aniso_over_t"] += 1
    st["finished"] = True
    return st


# ---------- Lemma 28 ----------

def lemma28_check(at, sv, m, t, xms):
    """Lemma 28 for P = span(e_1, ..., e_(t-1)) mapped into span(e_0) on one solution."""
    pis = [mat_apply(at[h], 1, t) >> 1 for h in range(1 << m)]
    tau = [sv[h] & 1 for h in range(1 << m)]
    lc, exact = least_codim(zero_set(sv), m, xms[m])
    out = {"tau_pi": all(not (tau[h] and pis[h]) for h in range(1 << m)),
           "pi_zero": not any(pis), "lc": lc, "exact": exact, "aniso": not zero_set(sv)}
    if not out["pi_zero"]:
        ztau = sum(1 << h for h in range(1, 1 << m) if not tau[h])
        S, ex = find_vanishing(ztau, m - 1, xms[m])
        out["hyperplane"] = (S is not None) if ex else None
        if S is not None:
            W = [h for h in range(1 << m) if (S >> h) & 1]
            out["beta_zero"] = all(sv[a ^ b] == sv[a] ^ sv[b] for a in W for b in W)
    return out


def lemma28_survey(budget_seconds, rng, count=240):
    start = time.time()
    st = {"systems": 0, "sigmas": 0, "pi_nonzero": 0, "tau_pi_violations": 0, "no_hyperplane": 0,
          "beta_not_zero": 0, "lc_over_t": 0, "aniso_over_t": 0, "inexact": 0, "max_lc": {},
          "aniso_max": {}, "finished": False}
    xms = {m: xor_masks(m) for m in range(0, 8)}
    tabs = {}
    mmax = {3: 7, 4: 6}
    for n in range(count):
        if time.time() - start > budget_seconds:
            st["stopped_at"] = n
            return st
        t = 3 if n % 2 else 4
        mask = compression_mask(t, 1, 1)
        c = rng.randint(1, min(2 * t - 1, mmax[t]))
        y = rng.randint(0, min(t, mmax[t] - c))
        B = independent([rng.randrange(1, 1 << (t * t)) & mask for _ in range(c)])
        m, at = system(B, y)
        if m == 0:
            continue
        if m not in tabs:
            tabs[m] = mon_tables(m)
        sol = solve_sigma(at, m, t)
        st["systems"] += 1
        key = str(t)
        for _ in range(3 if sol else 0):
            sv = table(sigma_from_coeffs(combine(sol, rng.getrandbits(len(sol))), tabs[m], t), m)
            st["sigmas"] += 1
            r = lemma28_check(at, sv, m, t, xms)
            if not r["tau_pi"]:
                st["tau_pi_violations"] += 1
            if not r["pi_zero"]:
                st["pi_nonzero"] += 1
                if r["hyperplane"] is None:
                    st["inexact"] += 1
                elif not r["hyperplane"]:
                    st["no_hyperplane"] += 1
                elif not r["beta_zero"]:
                    st["beta_not_zero"] += 1
            if not r["exact"]:
                st["inexact"] += 1
                continue
            st["max_lc"][key] = max(st["max_lc"].get(key, 0), r["lc"])
            if r["lc"] > t:
                st["lc_over_t"] += 1
            if r["aniso"]:
                st["aniso_max"][key] = max(st["aniso_max"].get(key, 0), m)
                if m > t:
                    st["aniso_over_t"] += 1
    st["finished"] = True
    return st


# ---------- anisotropic systems with t = 4 over irreducible spaces ----------

KINDS = ("comp11", "comp12", "comp21", "random", "reducible")


def random_space(rng, t, c, kind, subs, tries=4000):
    """A random c-dimensional space of singular t x t matrices of the given kind, irreducible
    unless kind == "reducible" (then it keeps span(e_0, ..., e_(d-1)) invariant), or None."""
    n2 = t * t
    masks = {"comp11": compression_mask(t, 1, 1), "comp12": compression_mask(t, 1, 2),
             "comp21": compression_mask(t, 2, 1), "random": (1 << n2) - 1}
    for _ in range(tries):
        mask = block_mask(t, rng.randint(1, t - 1)) if kind == "reducible" else masks[kind]
        B = independent([rng.randrange(1, 1 << n2) & mask for _ in range(c)])
        if len(B) != c:
            continue
        if not all(is_singular(combine(B, i), t) for i in range(1, 1 << c)):
            continue
        if kind == "reducible" or is_irreducible(B, t, subs):
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


def irred4_survey(budget_seconds, rng):
    start = time.time()
    t = 4
    subs = proper_subspaces(t)
    st = {"systems": 0, "no_space": 0, "solutions": 0, "sampled_systems": 0, "by": {},
          "found": [], "finished": False}
    tabs = {}
    plan = []
    for m, reps in ((5, 10), (6, 4)):
        for c in range(2, min(m, 6) + 1):
            if m - c > t:
                continue
            for kind in KINDS:
                if kind == "random" and c > 3:
                    continue
                plan += [(m, c, kind)] * reps
    rng.shuffle(plan)
    for m, c, kind in plan:
        if time.time() - start > budget_seconds:
            st["stopped_at"] = st["systems"]
            return st
        rec = st["by"].setdefault(f"{kind} {m}", {"systems": 0, "aniso_systems": 0,
                                                  "aniso_solutions": 0, "max_rank": {}})
        B = random_space(rng, t, c, kind, subs)
        if B is None:
            st["no_space"] += 1
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
        rk = str(max(mat_rank(combine(B, i), t) for i in range(1, 1 << c)))
        rec["systems"] += 1
        rec["max_rank"][rk] = rec["max_rank"].get(rk, 0) + 1
        if found:
            rec["aniso_systems"] += 1
            rec["aniso_solutions"] += found
            if len(st["found"]) < 10:
                st["found"].append({"m": mm, "kind": kind, "C": B, "count": found})
    st["finished"] = True
    return st


# ---------- control ----------

def control(rng, count=300, m=5, t=4):
    """Random quadratic maps F_2^m -> F_2^t (no identity imposed): how many are anisotropic?"""
    tabs = mon_tables(m)
    N = len(tabs)
    found = 0
    for _ in range(count):
        sv = table(sigma_from_coeffs(rng.getrandbits(t * N), tabs, t), m)
        if not zero_set(sv):
            found += 1
    return {"maps": count, "anisotropic": found}


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def report(part, st, graded, explore, out_dir):
    print(f"{part}: {json.dumps(st, sort_keys=True)}", flush=True)
    print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
    print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
    print(f"SUMMARY {part} all_match {all(graded.values())}", flush=True)
    write_out({"stats": st, "graded": graded, "exploratory": explore}, out_dir, f"{part}.json")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["lemma27", "lemma28", "irred4", "control"],
                    default="control")
    ap.add_argument("--budget-minutes", type=float, default=20.0)
    args = ap.parse_args()
    rng = random.Random(27)
    budget = args.budget_minutes * 60
    if args.part == "lemma27":
        st = lemma27_survey(budget, rng)
        graded = {"quotient": st["not_quotient"] == 0, "inside": st["not_inside"] == 0,
                  "restricted": st["not_restricted"] == 0,
                  "split": st["split_violations"] == 0, "codim_q": st["codim_q_over"] == 0,
                  "lc_u": st["lc_u_over"] == 0, "lc_le_t": st["lc_over_t"] == 0,
                  "aniso_le_t": st["aniso_over_t"] == 0, "finished": st["finished"]}
        explore = {"max_lc": st["max_lc"], "aniso_max": st["aniso_max"], "inexact": st["inexact"]}
        report("lemma27", st, graded, explore, args.out_dir)
    elif args.part == "lemma28":
        st = lemma28_survey(budget, rng)
        graded = {"tau_pi": st["tau_pi_violations"] == 0, "hyperplane": st["no_hyperplane"] == 0,
                  "beta_zero": st["beta_not_zero"] == 0, "lc_le_t": st["lc_over_t"] == 0,
                  "aniso_le_t": st["aniso_over_t"] == 0, "finished": st["finished"]}
        explore = {"max_lc": st["max_lc"], "aniso_max": st["aniso_max"],
                   "pi_nonzero": st["pi_nonzero"], "inexact": st["inexact"]}
        report("lemma28", st, graded, explore, args.out_dir)
    elif args.part == "irred4":
        st = irred4_survey(budget, rng)
        by = st["by"]
        graded = {"reducible_none": all(by.get(f"reducible {m}", {"aniso_systems": 0})
                                        ["aniso_systems"] == 0 for m in (5, 6)),
                  "comp11_none": all(by.get(f"comp11 {m}", {"aniso_systems": 0})
                                     ["aniso_systems"] == 0 for m in (5, 6)),
                  "finished": st["finished"]}
        explore = {k: v["aniso_systems"] for k, v in sorted(by.items())}
        report("irred4", st, graded, explore, args.out_dir)
    else:
        st = control(rng)
        graded = {"some_anisotropic": st["anisotropic"] > 0}
        report("control", st, graded, {"anisotropic": st["anisotropic"]}, args.out_dir)


if __name__ == "__main__":
    main()
