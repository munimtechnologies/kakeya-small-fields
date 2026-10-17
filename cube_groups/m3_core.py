# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma 25, Proposition 21 and Theorem 23 of finite-groups.md (section 14, version 1.7.6): zeros of
sigma, elements of order 7, and the systems with t = 3 that still decide whether M(3) <= 5.

Setting as in normal_form.py. X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Fix(A) = ker(I + A). Call A *good* if A and I + A are both invertible; for t = 3 these are the 48
elements of order 7 of GL_3(F_2). Lemma 25: (a) if sigma(u) = 0, then beta(u, h) lies in Fix(A_u)
for every h; (b) every h with A_h good lies in the zero set of sigma and in the radical of beta;
(c) if E is a complement in alpha(V) of the span S of its good elements, the least codimension of
a vanishing subspace for V is at most that for the restriction to alpha^(-1)(E). Theorem 23 (t = 3)
then leaves only images C without an element of order 7 (dim C <= 7) and dim C + y >= 8.

Parts. facts: the good elements of M_2(F_2) and M_3(F_2) and their span; every subspace of M_3(F_2)
of dimension 6, 7 or 8 without a good element (listed as annihilators under the trace form
(A, B) -> tr(AB)) and its conjugacy classes under GL_3(F_2); the 14 stabilisers of a line or a
plane; the good elements in each hyperplane; the 4 good-free hyperplanes of M_2(F_2). lemma25:
Lemma 25 and Theorem 23(a), (b) on random systems with t = 3 (m <= 7), and Lemma 25(a), (b) with
t = 4. core5, core6, core7: for every conjugacy class of good-free C of that dimension and every
y <= 3 with dim C + y >= 8, every solution sigma (or a random sample when dim Sol is above --cap)
is checked for a vanishing subspace of codimension <= 5, and the exact least codimension of a few
solutions is recorded.

Vectors of F_2^m are int bitmasks; a t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c (0-based); a set of vectors (or of matrices) is an int with bit x set for each x in it.
Pure Python, no dependencies; the helpers are copied from nf_pencil.py so that this file runs on
its own.

Usage: python m3_core.py [--out-dir DIR] [--part facts|lemma25|core5|core6|core7]
                         [--budget-minutes 30] [--cap 16]
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


def span_set(vectors):
    """Every element of the span of vectors, as a set."""
    S = {0}
    for v in vectors:
        if v not in S:
            S |= {s ^ v for s in S}
    return S


def bits(x):
    """The set bits of x, in increasing order."""
    out = []
    while x:
        low = x & -x
        out.append(low.bit_length() - 1)
        x ^= low
    return out


# ---------- t x t matrices over F_2 ----------

def mat_apply(A, x, t):
    row_mask = (1 << t) - 1
    out = 0
    for r in range(t):
        if parity((A >> (t * r)) & row_mask & x):
            out |= 1 << r
    return out


def mat_mul(A, B, t):
    out = 0
    for c in range(t):
        y = mat_apply(A, mat_apply(B, 1 << c, t), t)
        for r in range(t):
            if (y >> r) & 1:
                out |= 1 << (t * r + c)
    return out


def identity(t):
    return sum(1 << (t * i + i) for i in range(t))


def entries(t, cells):
    """The matrix with a 1 in each (r, c) of cells (0-based)."""
    return sum(1 << (t * r + c) for r, c in cells)


def is_singular(A, t):
    row_mask = (1 << t) - 1
    return rank_f2([(A >> (t * r)) & row_mask for r in range(t)]) < t


def transpose(A, t):
    out = 0
    for r in range(t):
        for c in range(t):
            if (A >> (t * r + c)) & 1:
                out |= 1 << (t * c + r)
    return out


def is_good(A, t):
    """A and I + A both invertible (for t = 3: A has order 7)."""
    return not is_singular(A, t) and not is_singular(A ^ identity(t), t)


def good_mask(t):
    return sum(1 << A for A in range(1 << (t * t)) if is_good(A, t))


def set_mask(S):
    return sum(1 << x for x in S)


def trace_masks(t):
    """zm[B] = the set of A with tr(AB) = 0. tr(AB) = sum of A_ij B_ji = parity(A & B^T)."""
    n = 1 << (t * t)
    tr = [transpose(B, t) for B in range(n)]
    return [sum(1 << A for A in range(n) if not parity(A & tr[B])) for B in range(n)]


def gl(t):
    return [A for A in range(1 << (t * t)) if not is_singular(A, t)]


def conj_perms(t):
    """For each g in GL_t(F_2), the permutation A -> g A g^(-1) of M_t(F_2), as a list."""
    G = gl(t)
    one = identity(t)
    perms = []
    for g in G:
        gi = next(B for B in G if mat_mul(g, B, t) == one)
        perms.append([mat_mul(mat_mul(g, A, t), gi, t) for A in range(1 << (t * t))])
    return perms


def free_subspaces(t, k, zm, gm, deadline=None):
    """Element sets of every k-dim subspace of M_t(F_2) with no good element, found as the
    annihilators of the (t^2 - k)-dim subspaces under the trace form. (sets, finished)."""
    n2 = t * t
    full = (1 << (1 << n2)) - 1
    out = []
    count = 0
    for D in subspaces(n2, n2 - k):
        count += 1
        if deadline is not None and count % 4096 == 0 and time.time() > deadline:
            return out, False
        mk = full
        for B in D:
            mk &= zm[B]
        if not mk & gm:
            out.append(mk)
    return out, True


def orbits(masks, perms):
    """[(representative, orbit size)] of the conjugation action on the given subspace sets."""
    seen = set()
    reps = []
    for mk in masks:
        if mk in seen:
            continue
        els = bits(mk)
        imgs = set()
        for p in perms:
            im = 0
            for x in els:
                im |= 1 << p[x]
            imgs.add(im)
        seen |= imgs
        reps.append((mk, len(imgs)))
    return reps


def stabilisers(t):
    """Element sets of the stabilisers {A : A P <= P} of every proper non-zero subspace P."""
    n = 1 << (t * t)
    out = []
    for d in range(1, t):
        for B in subspaces(t, d):
            P = span_set(B)
            out.append(sum(1 << A for A in range(n) if all(mat_apply(A, x, t) in P for x in B)))
    return out


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


def zero_mask_of(S, m):
    nz = 0
    for q in S:
        nz |= q
    return ((1 << (1 << m)) - 2) & ~nz


def restricted_zero_mask(sv, Wb):
    """Zero set of sigma restricted to span(Wb), in the coordinates of Wb."""
    return sum(1 << x for x in range(1, 1 << len(Wb)) if sv[combine(Wb, x)] == 0)


# ---------- Lemma 25 ----------

def lemma25_violations(at, sv, m, t):
    """(violations of Lemma 25(a), violations of Lemma 25(b)) for the value table sv."""
    one = identity(t)
    va = vb = 0
    for u in range(1 << m):
        good = is_good(at[u], t)
        if good and sv[u]:
            vb += 1
        if sv[u] and not good:
            continue
        for h in range(1 << m):
            b = sv[u ^ h] ^ sv[u] ^ sv[h]
            if not sv[u] and mat_apply(at[u] ^ one, b, t):
                va += 1
            if good and b:
                vb += 1
    return va, vb


def good_complement(Cbasis, t):
    """(dim S, indices i such that Cbasis[i] span a complement E of the span S of the good
    elements of span(Cbasis), whether E has a good element)."""
    goods = [A for A in span_set(Cbasis) if is_good(A, t)]
    S = independent(goods)
    chosen = []
    for i, b in enumerate(Cbasis):
        if rank_f2(S + [Cbasis[j] for j in chosen] + [b]) > len(S) + len(chosen):
            chosen.append(i)
    E = [Cbasis[i] for i in chosen]
    return len(S), chosen, any(is_good(A, t) for A in span_set(E) if A)


def lemma25_survey(budget_seconds, rng, count=400):
    start = time.time()
    st = {"t3_systems": 0, "t3_sigmas": 0, "t3_nonzero_sigmas": 0, "va": 0, "vb": 0,
          "complement_has_good": 0, "restriction_violations": 0, "theorem23a_violations": 0,
          "theorem23b_violations": 0, "with_good": 0, "max_codim": 0, "t4_systems": 0,
          "t4_sigmas": 0, "t4_va": 0, "t4_vb": 0, "finished": False}
    tabs = {}
    xms = {m: xor_masks(m) for m in range(1, 8)}
    for _ in range(count):
        if time.time() - start > budget_seconds:
            st["stopped_at"] = st["t3_systems"]
            return st
        c = rng.randint(1, 6)
        while True:
            B = independent([rng.randrange(1, 512) for _ in range(c)])
            if len(B) == c:
                break
        y = rng.randint(0, min(3, 7 - c))
        m, at = system(B, y)
        if m not in tabs:
            tabs[m] = mon_tables(m)
        sol = solve_sigma(at, m, 3)
        st["t3_systems"] += 1
        s, chosen, bad = good_complement(B, 3)
        if s:
            st["with_good"] += 1
        if bad:
            st["complement_has_good"] += 1
        Wb = [1 << i for i in chosen] + [1 << (c + j) for j in range(y)]
        picks = [combine(sol, rng.getrandbits(len(sol))) for _ in range(4)] if sol else [0]
        for v in picks:
            S = sigma_from_coeffs(v, tabs[m], 3)
            sv = table(S, m)
            st["t3_sigmas"] += 1
            if v:
                st["t3_nonzero_sigmas"] += 1
            va, vb = lemma25_violations(at, sv, m, 3)
            st["va"] += va
            st["vb"] += vb
            lc, _ = least_codim(zero_mask_of(S, m), m, xms[m])
            st["max_codim"] = max(st["max_codim"], lc)
            lw, _ = least_codim(restricted_zero_mask(sv, Wb), len(Wb), xms[len(Wb)]) \
                if Wb else (0, True)
            if lc > lw:
                st["restriction_violations"] += 1
            if m >= 4 and lc > m - 1:
                st["theorem23a_violations"] += 1
            if lc > 5:
                st["theorem23b_violations"] += 1
    for _ in range(40):
        c = rng.randint(1, 4)
        B = independent([rng.randrange(1, 1 << 16) for _ in range(c)])
        y = rng.randint(0, 5 - len(B))
        m, at = system(B, y)
        if m not in tabs:
            tabs[m] = mon_tables(m)
        sol = solve_sigma(at, m, 4)
        st["t4_systems"] += 1
        for v in ([combine(sol, rng.getrandbits(len(sol))) for _ in range(3)] if sol else []):
            sv = table(sigma_from_coeffs(v, tabs[m], 4), m)
            st["t4_sigmas"] += 1
            va, vb = lemma25_violations(at, sv, m, 4)
            st["t4_va"] += va
            st["t4_vb"] += vb
    st["finished"] = True
    return st


# ---------- the systems left by Theorem 23 ----------

def core_survey(e, budget_seconds, cap, samples, exact_per, rng):
    start = time.time()
    deadline = start + budget_seconds
    zm = trace_masks(3)
    gm = good_mask(3)
    perms = conj_perms(3)
    masks, fin = free_subspaces(3, e, zm, gm, deadline)
    st = {"e": e, "free_subspaces": len(masks), "enumeration_finished": fin, "classes": 0,
          "orbit_sum": 0, "systems": 0, "exhaustive_systems": 0, "sampled_systems": 0,
          "zero_sol_systems": 0, "sigmas_checked": 0, "over5": 0, "undecided": 0,
          "max_sol_dim": 0, "sol_dims": {}, "exact_codims": {}, "inexact_codims": 0,
          "examples_over5": [], "finished": False}
    if not fin:
        st["stopped_at"] = "enumeration"
        return st
    reps = orbits(masks, perms)
    st["classes"] = len(reps)
    st["orbit_sum"] = sum(o for _, o in reps)
    print(f"core{e}: {len(masks)} good-free subspaces in {len(reps)} classes", flush=True)
    tabs = {}
    xms = {}
    done = 0
    for mk, osz in reps:
        B = independent(bits(mk))
        for y in range(max(0, 8 - e), 4):
            if time.time() > deadline:
                st["stopped_at"] = f"class {done} y={y}"
                return st
            m, at = system(B, y)
            if m not in tabs:
                tabs[m] = mon_tables(m)
                xms[m] = xor_masks(m)
            xm = xms[m]
            sol = solve_sigma(at, m, 3)
            D = len(sol)
            st["systems"] += 1
            st["max_sol_dim"] = max(st["max_sol_dim"], D)
            st["sol_dims"][str(D)] = st["sol_dims"].get(str(D), 0) + 1
            if D == 0:
                st["zero_sol_systems"] += 1
                continue
            sm = [sigma_from_coeffs(v, tabs[m], 3) for v in sol]
            full = (1 << (1 << m)) - 2
            need = m - 5

            def check(cur, idx):
                z = full & ~(cur[0] | cur[1] | cur[2])
                found, exact = has_vanishing(z, need, xm)
                st["sigmas_checked"] += 1
                if not exact:
                    st["undecided"] += 1
                elif not found:
                    st["over5"] += 1
                    if len(st["examples_over5"]) < 10:
                        st["examples_over5"].append({"C": B, "y": y, "coeffs": combine(sol, idx)})

            if D <= cap:
                st["exhaustive_systems"] += 1
                cur = [0, 0, 0]
                for i in range(1, 1 << D):
                    j = (i & -i).bit_length() - 1
                    cur = [a ^ b for a, b in zip(cur, sm[j])]
                    check(cur, i ^ (i >> 1))
            else:
                st["sampled_systems"] += 1
                for _ in range(samples):
                    p = rng.randrange(1, 1 << D)
                    check(sigma_from_coeffs(combine(sol, p), tabs[m], 3), p)
            for _ in range(exact_per):
                p = rng.randrange(1, 1 << D)
                lc, exact = least_codim(zero_mask_of(sigma_from_coeffs(combine(sol, p), tabs[m], 3),
                                                     m), m, xm)
                if exact:
                    st["exact_codims"][str(lc)] = st["exact_codims"].get(str(lc), 0) + 1
                else:
                    st["inexact_codims"] += 1
        done += 1
        if done % 50 == 0:
            print(f"core{e}: {done} of {len(reps)} classes, {st['sigmas_checked']} sigmas, "
                  f"over5 {st['over5']}, undecided {st['undecided']}", flush=True)
    st["finished"] = True
    return st


# ---------- parts ----------

def facts(budget_seconds):
    deadline = time.time() + budget_seconds
    out = {}
    gm2, gm3 = good_mask(2), good_mask(3)
    out["good_t2"] = bin(gm2).count("1")
    out["good_t3"] = bin(gm3).count("1")
    out["good_span_t3"] = rank_f2(bits(gm3))
    zm2 = trace_masks(2)
    h2, _ = free_subspaces(2, 3, zm2, gm2)
    out["t2_free_hyperplanes"] = len(h2)
    zm = trace_masks(3)
    perms = conj_perms(3)
    out["gl3"] = len(perms)
    hyper = []
    for B in subspaces(9, 1):
        mk = ((1 << 512) - 1) & zm[B[0]]
        hyper.append(bin(mk & gm3).count("1"))
    out["hyperplanes"] = len(hyper)
    out["min_good_in_hyperplane"] = min(hyper)
    stabs = stabilisers(3)
    out["stabilisers"] = len(stabs)
    out["stabilisers_distinct"] = len(set(stabs))
    out["stabiliser_sizes"] = sorted({bin(s).count("1") for s in stabs})
    out["stabilisers_good_free"] = all(not s & gm3 for s in stabs)
    free = {}
    for k in (8, 7, 6):
        masks, fin = free_subspaces(3, k, zm, gm3, deadline)
        reps = orbits(masks, perms) if fin else []
        free[str(k)] = {"subspaces": len(masks), "finished": fin, "classes": len(reps),
                        "orbit_sum": sum(o for _, o in reps),
                        "class_sizes": sorted(o for _, o in reps)}
        if k == 7:
            out["free7_are_stabilisers"] = fin and set(masks) == set(stabs)
        print(f"free subspaces of dim {k}: {json.dumps(free[str(k)])}", flush=True)
    out["free"] = free
    return out


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["facts", "lemma25", "core5", "core6", "core7"],
                    default="facts")
    ap.add_argument("--budget-minutes", type=float, default=30.0)
    ap.add_argument("--cap", type=int, default=16)
    args = ap.parse_args()
    rng = random.Random(11)
    budget = args.budget_minutes * 60
    if args.part == "facts":
        out = facts(budget)
        f = out["free"]
        graded = {
            "good_t2_2": out["good_t2"] == 2,
            "good_t3_48": out["good_t3"] == 48,
            "good_span_9": out["good_span_t3"] == 9,
            "t2_free_hyperplanes_4": out["t2_free_hyperplanes"] == 4,
            "gl3_168": out["gl3"] == 168,
            "every_hyperplane_has_16_good": out["min_good_in_hyperplane"] >= 16,
            "no_free_8": f["8"]["finished"] and f["8"]["subspaces"] == 0,
            "stabilisers_14_free_dim7": (out["stabilisers_distinct"] == 14
                                         and out["stabiliser_sizes"] == [128]
                                         and out["stabilisers_good_free"]),
            "orbit_sums": all(v["orbit_sum"] == v["subspaces"] for v in f.values() if v["finished"]),
        }
        explore = {"min_good_in_hyperplane": out["min_good_in_hyperplane"],
                   "free7": f["7"]["subspaces"], "free7_classes": f["7"]["classes"],
                   "free7_are_stabilisers": out.get("free7_are_stabilisers"),
                   "free6": f["6"]["subspaces"], "free6_classes": f["6"]["classes"]}
        out["graded"] = graded
        out["exploratory"] = explore
        print(f"facts: {json.dumps({k: v for k, v in out.items() if k != 'free'}, sort_keys=True)}",
              flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY facts all_match {all(graded.values())}", flush=True)
        write_out(out, args.out_dir, "facts.json")
    elif args.part == "lemma25":
        st = lemma25_survey(budget, rng)
        graded = {"lemma25a": st["va"] == 0 and st["t4_va"] == 0,
                  "lemma25b": st["vb"] == 0 and st["t4_vb"] == 0,
                  "complement_good_free": st["complement_has_good"] == 0,
                  "lemma25c": st["restriction_violations"] == 0,
                  "theorem23a": st["theorem23a_violations"] == 0,
                  "theorem23b": st["theorem23b_violations"] == 0,
                  "finished": st["finished"]}
        print(f"lemma25: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"SUMMARY lemma25 all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded}, args.out_dir, "lemma25.json")
    else:
        e = int(args.part[-1])
        st = core_survey(e, budget, args.cap, samples=4096, exact_per=4, rng=rng)
        graded = {"orbit_sum": (not st["classes"]) or st["orbit_sum"] == st["free_subspaces"]}
        explore = {"over5": st["over5"], "undecided": st["undecided"],
                   "all_exhaustive": st["sampled_systems"] == 0, "finished": st["finished"],
                   "exact_codims": st["exact_codims"]}
        print(f"core{e}: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY core{e} finished {st['finished']} over5 {st['over5']} undecided "
              f"{st['undecided']} sampled {st['sampled_systems']}", flush=True)
        write_out({"stats": st, "graded": graded, "exploratory": explore}, args.out_dir,
                  f"core{e}.json")


if __name__ == "__main__":
    main()
