# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""A counterexample to the normal-form conjecture after Lemma 23 of finite-groups.md (version 1.7.5),
the pencil criterion behind it, and a search for anisotropic systems.

Setting as in normal_form.py. X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Normal form: sigma(h) = (I + A_h) lam(h) for a linear map lam : V -> X. Fix(A) = ker(I + A).

1. Criterion (draft Lemma 24). Let alpha be one-to-one with A_i = A_(e_i), q_i = sigma(e_i) and
   b_ij = beta(e_i, e_j). Then (*) holds on the basis and pairs iff A_j q_i = (I + A_i) b_ij for all
   i, j (b_ii = 0) and A_k b_ij + A_i b_jk + A_j b_ik = 0 for distinct i, j, k; sigma has the normal
   form iff there are f_i in Fix(A_i) with f_i + f_j + b_ij in Fix(A_i + A_j) for all i < j. For a
   pencil (m = 2) this reads: b_12 lies in Fix(A_1) + Fix(A_2) + Fix(A_1 + A_2). It holds whenever
   one of A_1, A_2, A_1 + A_2 is invertible, and for every pencil when t = 2.
2. The example. t = 3, m = 2, A_1 = E_11, A_2 = E_12 + E_13 + E_21 + E_22 (1-based entries),
   sigma(e_1) = e_2 + e_3, sigma(e_2) = e_1 + e_2 + e_3, beta(e_1, e_2) = e_2. It satisfies (*),
   sigma vanishes only at 0, Fix(A_1) + Fix(A_2) + Fix(A_1 + A_2) = span(e_1) does not contain e_2,
   and so no linear lam gives the normal form. Its solution space is 1-dimensional for y = 0..3.
3. Anisotropic systems: sigma(h) != 0 for every h != 0. Then every A_h is singular for h outside
   ker alpha (A_h sigma(h) = 0), restrictions to subspaces stay anisotropic, and the least
   codimension of a vanishing subspace is m, so an anisotropic system with m = t + 1 would give
   M(t) > t. The search lists every subspace C of M_t(F_2) whose non-zero elements are all singular,
   and every y = m - c <= t, and looks at every solution of (*).

Vectors of F_2^t are int bitmasks; a t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c (0-based). A quadratic map is stored by its coefficient vector as in normal_form.py, or as a
value table sv with sv[h] = sigma(h). Pure Python, no dependencies; the helpers are copied from
normal_form.py so that this file runs on its own.

Usage: python nf_pencil.py [--out-dir DIR] [--part pencils|aniso-small|aniso-t3d4|rank3]
                           [--budget-minutes 30]
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


def kernel(A, t):
    return [x for x in range(1 << t) if mat_apply(A, x, t) == 0]


def fix_space(A, t):
    """Fix(A) = ker(I + A), as a list of its vectors."""
    return kernel(A ^ identity(t), t)


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


def identity_holds_table(at, sv, m, t):
    """(*) on every pair (h, h'), for the value table sv."""
    one = identity(t)
    for h in range(1 << m):
        for hp in range(1 << m):
            b = sv[h ^ hp] ^ sv[h] ^ sv[hp]
            if mat_apply(at[hp], sv[h], t) != mat_apply(at[h] ^ one, b, t):
                return False
    return True


def nf_bruteforce(at, sv, m, t):
    """A linear lam (the list lam(e_j)) with sv[h] = (I + A_h) lam(h) for every h, or None."""
    one = identity(t)
    choices = [[v for v in range(1 << t) if mat_apply(at[1 << j] ^ one, v, t) == sv[1 << j]]
               for j in range(m)]
    for lam in itertools.product(*choices):
        ok = True
        for h in range(1, 1 << m):
            lh = combine(list(lam), h)
            if mat_apply(at[h] ^ one, lh, t) != sv[h]:
                ok = False
                break
        if ok:
            return list(lam)
    return None


def f_criterion(Cbasis, sv, t):
    """Draft Lemma 24 for alpha one-to-one (y = 0): f_i in Fix(A_i) with f_i + f_j + b_ij in
    Fix(A_i + A_j) for all i < j?"""
    c = len(Cbasis)
    fixes = [fix_space(A, t) for A in Cbasis]
    prs = list(itertools.combinations(range(c), 2))
    pfix = {(i, j): set(fix_space(Cbasis[i] ^ Cbasis[j], t)) for i, j in prs}
    bij = {(i, j): sv[(1 << i) | (1 << j)] ^ sv[1 << i] ^ sv[1 << j] for i, j in prs}
    for f in itertools.product(*fixes):
        if all((f[i] ^ f[j] ^ bij[i, j]) in pfix[i, j] for i, j in prs):
            return True
    return False


def min_codim_table(sv, m):
    """Least codimension of a subspace of V on which sigma vanishes (by listing subspaces)."""
    for d in range(m, -1, -1):
        for B in subspaces(m, d):
            if all(sv[x] == 0 for x in span_set(B)):
                return m - d
    return m


# ---------- pencils (rank alpha = 2, y = 0) ----------

def pencil_alpha(A1, A2):
    return [0, A1, A2, A1 ^ A2]


def pencil_sigma(q1, q2, b):
    """Value table on V = F_2^2 (h = x_1 + 2 x_2) of sigma(e_1) = q1, sigma(e_2) = q2,
    beta(e_1, e_2) = b."""
    return [0, q1, q2, q1 ^ q2 ^ b]


def pencil_systems(A1, A2, t):
    """Every (q1, q2, b) with A1 q1 = 0, A2 q2 = 0, A2 q1 = (I + A1) b and A1 q2 = (I + A2) b."""
    one = identity(t)
    k1 = kernel(A1, t)
    k2 = kernel(A2, t)
    out = []
    for b in range(1 << t):
        r1 = mat_apply(A1 ^ one, b, t)
        Q1 = [q for q in k1 if mat_apply(A2, q, t) == r1]
        if not Q1:
            continue
        r2 = mat_apply(A2 ^ one, b, t)
        Q2 = [q for q in k2 if mat_apply(A1, q, t) == r2]
        for q1 in Q1:
            for q2 in Q2:
                out.append((q1, q2, b))
    return out


def pencil_fix_sum(A1, A2, t):
    return span_set(fix_space(A1, t) + fix_space(A2, t) + fix_space(A1 ^ A2, t))


def pencil_criterion(A1, A2, b, t):
    """b in Fix(A1) + Fix(A2) + Fix(A1 + A2)?"""
    return b in pencil_fix_sum(A1, A2, t)


def has_invertible(A1, A2, t):
    return any(not is_singular(A, t) for A in (A1, A2, A1 ^ A2))


# ---------- the example ----------

def counterexample():
    """(t, A1, A2, q1, q2, b) of the example in the docstring (0-based bits)."""
    t = 3
    A1 = entries(t, [(0, 0)])
    A2 = entries(t, [(0, 1), (0, 2), (1, 0), (1, 1)])
    return t, A1, A2, 0b110, 0b111, 0b010


def check_counterexample():
    t, A1, A2, q1, q2, b = counterexample()
    at = pencil_alpha(A1, A2)
    sv = pencil_sigma(q1, q2, b)
    tabs = mon_tables(2)
    coef = 0
    N = len(tabs)
    # coefficient vector: monomials (0,0), (1,1), (0,1) -> q1, q2, b in each coordinate
    for comp in range(t):
        for k, v in enumerate((q1, q2, b)):
            if (v >> comp) & 1:
                coef |= 1 << (comp * N + k)
    sol_dims = []
    in_sol_nf = []
    for y in range(4):
        m, aty = system([A1, A2], y)
        sol = solve_sigma(aty, m, t)
        sol_dims.append(len(sol))
        nf = nf_gens(aty, m, t)
        in_sol_nf.append(rank_f2(nf + sol) == rank_f2(nf))
    sol0 = solve_sigma(at, 2, t)
    return {
        "identity": identity_holds_table(at, sv, 2, t),
        "pencil_conditions": (q1, q2, b) in pencil_systems(A1, A2, t),
        "in_sol": rank_f2(sol0 + [coef]) == rank_f2(sol0),
        "anisotropic": all(sv[h] for h in range(1, 4)),
        "least_codim": min_codim_table(sv, 2),
        "nf_bruteforce": nf_bruteforce(at, sv, 2, t),
        "criterion": pencil_criterion(A1, A2, b, t),
        "fix_sum": sorted(pencil_fix_sum(A1, A2, t)),
        "singular": [is_singular(A, t) for A in (A1, A2, A1 ^ A2)],
        "sol_dims_y0_to_3": sol_dims,
        "sol_inside_nf_y0_to_3": in_sol_nf,
    }


def coeffs_of(f, m, t):
    """Coefficient vector of the quadratic map h -> f(h) (f(0) = 0, degree <= 2)."""
    mons = monomials(m)
    N = len(mons)
    out = 0
    for k, (i, j) in enumerate(mons):
        if i == j:
            v = f(1 << i)
        else:
            v = f((1 << i) | (1 << j)) ^ f(1 << i) ^ f(1 << j)
        for comp in range(t):
            if (v >> comp) & 1:
                out |= 1 << (comp * N + k)
    return out


def nf_gens(at, m, t):
    """Coefficient vectors of Q_lam(h) = (I + A_h) lam(h) for lam = E_(r, j), lam(h) = h_j e_r."""
    out = []
    for j in range(m):
        for r in range(t):
            e = 1 << r

            def f(h, j=j, e=e):
                return (e ^ mat_apply(at[h], e, t)) if (h >> j) & 1 else 0

            out.append(coeffs_of(f, m, t))
    return out


# ---------- the pencil survey ----------

def pencil_survey(t, pencils, brute_limit, rng, deadline=None):
    """Criterion over the given pencils; brute force on every failing system and on up to
    brute_limit passing ones."""
    st = {"t": t, "pencils": 0, "systems": 0, "failing_pencils": 0, "failing_systems": 0,
          "failing_with_invertible": 0, "criterion_mismatches": 0, "brute_checked": 0,
          "anisotropic_systems": 0, "failing_anisotropic": 0, "examples": [], "finished": False}
    passing_seen = 0
    for A1, A2 in pencils:
        if deadline is not None and time.time() > deadline:
            st["stopped_at"] = st["pencils"]
            return st
        st["pencils"] += 1
        fs = pencil_fix_sum(A1, A2, t)
        at = pencil_alpha(A1, A2)
        fail_here = False
        for q1, q2, b in pencil_systems(A1, A2, t):
            st["systems"] += 1
            ok = b in fs
            sv = pencil_sigma(q1, q2, b)
            aniso = q1 and q2 and (q1 ^ q2 ^ b)
            if aniso:
                st["anisotropic_systems"] += 1
            brute = not ok
            if ok:
                passing_seen += 1
                if passing_seen <= brute_limit or rng.random() < 0.01:
                    brute = True
            if brute:
                st["brute_checked"] += 1
                if (nf_bruteforce(at, sv, 2, t) is not None) != ok:
                    st["criterion_mismatches"] += 1
            if not ok:
                st["failing_systems"] += 1
                fail_here = True
                if aniso:
                    st["failing_anisotropic"] += 1
                if len(st["examples"]) < 8:
                    st["examples"].append({"A1": A1, "A2": A2, "q1": q1, "q2": q2, "b": b})
        if fail_here:
            st["failing_pencils"] += 1
            if has_invertible(A1, A2, t):
                st["failing_with_invertible"] += 1
    st["finished"] = True
    return st


def all_pencils(t):
    for B in subspaces(t * t, 2):
        yield B[0], B[1]


def random_pencils(t, count, rng):
    n = 1 << (t * t)
    for _ in range(count):
        while True:
            A1, A2 = rng.randrange(1, n), rng.randrange(1, n)
            if A1 != A2:
                break
        yield A1, A2


# ---------- rank 3 (draft Lemma 24 against brute force) ----------

def rank3_survey(t, subs, rng, max_sols=64, deadline=None):
    """For 3-dim C (y = 0): every (or up to max_sols random) solution, criterion vs brute force."""
    st = {"t": t, "subspaces": 0, "solutions": 0, "not_in_nf": 0, "mismatches": 0,
          "subspaces_with_failure": 0, "finished": False}
    tabs = mon_tables(3)
    for B in subs:
        if deadline is not None and time.time() > deadline:
            st["stopped_at"] = st["subspaces"]
            return st
        st["subspaces"] += 1
        m, at = system(B, 0)
        sol = solve_sigma(at, m, t)
        D = len(sol)
        if D == 0:
            continue
        if (1 << D) - 1 <= max_sols:
            picks = range(1, 1 << D)
        else:
            picks = [rng.randrange(1, 1 << D) for _ in range(max_sols)]
        failed = False
        for p in picks:
            sv = table(sigma_from_coeffs(combine(sol, p), tabs, t), m)
            st["solutions"] += 1
            crit = f_criterion(B, sv, t)
            if (nf_bruteforce(at, sv, m, t) is not None) != crit:
                st["mismatches"] += 1
            if not crit:
                st["not_in_nf"] += 1
                failed = True
        if failed:
            st["subspaces_with_failure"] += 1
    st["finished"] = True
    return st


# ---------- singular subspaces and anisotropic systems ----------

def singular_subspaces(t, cmax, deadline=None):
    """levels[c] = every c-dim subspace of M_t(F_2) whose non-zero elements are all singular, each
    as the tuple of its elements. (levels, finished)."""
    n = 1 << (t * t)
    sing = [is_singular(A, t) for A in range(n)]
    smask = sum(1 << A for A in range(n) if sing[A])
    SX = [0] * n
    for s in range(n):
        if sing[s]:
            SX[s] = sum(1 << A for A in range(n) if sing[A ^ s])
    levels = {0: [(0,)]}
    for c in range(1, cmax + 1):
        seen = set()
        out = []
        for S in levels[c - 1]:
            if deadline is not None and time.time() > deadline:
                levels[c] = out
                return levels, False
            allowed = smask
            for s in S:
                allowed &= SX[s]
            for s in S:
                allowed &= ~(1 << s)
            while allowed:
                low = allowed & -allowed
                M = low.bit_length() - 1
                coset = [s ^ M for s in S]
                for x in coset:
                    allowed &= ~(1 << x)
                new = S + tuple(coset)
                key = 0
                for x in new:
                    key |= 1 << x
                if key in seen:
                    continue
                seen.add(key)
                out.append(tuple(sorted(new)))
        levels[c] = out
    return levels, True


def anisotropic_in(Cbasis, y, t, tabs, cap=20, samples=1 << 15, rng=None):
    """(number of anisotropic sigma found, dim Sol, exhaustive flag, one example coefficient vector)."""
    m, at = system(Cbasis, y)
    if m not in tabs:
        tabs[m] = mon_tables(m)
    sol = solve_sigma(at, m, t)
    D = len(sol)
    full = (1 << (1 << m)) - 2
    masks = [sigma_from_coeffs(v, tabs[m], t) for v in sol]
    count = 0
    example = None
    if D <= cap:
        cur = [0] * t
        for i in range(1, 1 << D):
            j = (i & -i).bit_length() - 1
            cur = [a ^ b for a, b in zip(cur, masks[j])]
            u = 0
            for a in cur:
                u |= a
            if u == full:
                count += 1
                if example is None:
                    example = i
        if example is not None:
            g = example ^ (example >> 1)
            example = combine(sol, g)
        return count, D, True, example
    rng = rng or random.Random(0)
    for _ in range(samples):
        p = rng.randrange(1, 1 << D)
        u = 0
        for a in sigma_from_coeffs(combine(sol, p), tabs[m], t):
            u |= a
        if u == full:
            count += 1
            if example is None:
                example = combine(sol, p)
    return count, D, False, example


def aniso_search(t, d, levels, tabs, deadline=None):
    """Every reduced system with dim V = d whose C is singular: anisotropic solutions."""
    st = {"t": t, "d": d, "systems": 0, "systems_with_anisotropic": 0, "anisotropic_sigmas": 0,
          "sampled_systems": 0, "max_sol_dim": 0, "by_c": {}, "examples": [], "finished": False}
    for c in range(max(0, d - t), d + 1):
        if c not in levels:
            st["missing_level"] = c
            return st
        y = d - c
        hits = 0
        for S in levels[c]:
            if deadline is not None and time.time() > deadline:
                st["stopped_at"] = f"c={c}"
                return st
            B = independent([x for x in S if x])
            cnt, D, exh, ex = anisotropic_in(B, y, t, tabs)
            st["systems"] += 1
            st["max_sol_dim"] = max(st["max_sol_dim"], D)
            if not exh:
                st["sampled_systems"] += 1
            if cnt:
                hits += 1
                st["systems_with_anisotropic"] += 1
                st["anisotropic_sigmas"] += cnt
                if len(st["examples"]) < 6:
                    st["examples"].append({"C": B, "y": y, "coeffs": ex, "sol_dim": D})
        st["by_c"][str(c)] = {"subspaces": len(levels[c]), "y": y, "with_anisotropic": hits}
        print(f"t={t} d={d} c={c} y={y}: {len(levels[c])} subspaces, {hits} with anisotropic",
              flush=True)
    st["finished"] = True
    return st


# ---------- parts ----------

def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["pencils", "aniso-small", "aniso-t3d4", "rank3"],
                    default="pencils")
    ap.add_argument("--budget-minutes", type=float, default=30.0)
    args = ap.parse_args()
    rng = random.Random(7)
    deadline = time.time() + args.budget_minutes * 60
    if args.part == "pencils":
        ce = check_counterexample()
        print(f"counterexample: {json.dumps(ce, sort_keys=True)}", flush=True)
        p2 = pencil_survey(2, list(all_pencils(2)), 10 ** 6, rng)
        print(f"t2: {json.dumps({k: v for k, v in p2.items() if k != 'examples'})}", flush=True)
        p3 = pencil_survey(3, all_pencils(3), 3000, rng, deadline)
        print(f"t3: {json.dumps({k: v for k, v in p3.items() if k != 'examples'})}", flush=True)
        print(f"t3 examples: {json.dumps(p3['examples'])}", flush=True)
        p4 = pencil_survey(4, random_pencils(4, 3000, rng), 300, rng, deadline)
        print(f"t4 sample: {json.dumps({k: v for k, v in p4.items() if k != 'examples'})}",
              flush=True)
        graded = {
            "counterexample": (ce["identity"] and ce["pencil_conditions"] and ce["in_sol"]
                               and ce["anisotropic"] and ce["least_codim"] == 2
                               and ce["nf_bruteforce"] is None and not ce["criterion"]
                               and ce["sol_dims_y0_to_3"] == [1, 1, 1, 1]
                               and ce["sol_inside_nf_y0_to_3"] == [False] * 4),
            "t2_pencils_35": p2["pencils"] == 35,
            "t2_no_failing": p2["failing_systems"] == 0,
            "t3_pencils_43435": p3["finished"] and p3["pencils"] == 43435,
            "t3_failing_positive": p3["failing_pencils"] > 0,
            "failing_have_no_invertible": (p3["failing_with_invertible"] == 0
                                           and p4["failing_with_invertible"] == 0),
            "criterion_matches_bruteforce": (p2["criterion_mismatches"] == 0
                                             and p3["criterion_mismatches"] == 0
                                             and p4["criterion_mismatches"] == 0),
        }
        explore = {"t3_failing_pencils": p3["failing_pencils"],
                   "t3_failing_systems": p3["failing_systems"],
                   "t3_failing_anisotropic": p3["failing_anisotropic"],
                   "t4_failing_pencils_of_3000": p4["failing_pencils"]}
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY pencils all_match {all(graded.values())}", flush=True)
        write_out({"counterexample": ce, "t2": p2, "t3": p3, "t4": p4, "graded": graded,
                   "exploratory": explore}, args.out_dir, "pencils.json")
    elif args.part == "rank3":
        r2 = rank3_survey(2, subspaces(4, 3), rng, deadline=deadline)
        print(f"rank3 t2: {json.dumps(r2)}", flush=True)
        subs3 = []
        for _ in range(400):
            B = independent([rng.randrange(1, 512) for _ in range(3)])
            if len(B) == 3:
                subs3.append(B)
        r3 = rank3_survey(3, subs3, rng, max_sols=16, deadline=deadline)
        print(f"rank3 t3 sample: {json.dumps(r3)}", flush=True)
        graded = {"t2_mismatches_zero": r2["mismatches"] == 0, "t2_finished": r2["finished"],
                  "t3_mismatches_zero": r3["mismatches"] == 0}
        explore = {"t2_not_in_nf": r2["not_in_nf"], "t3_not_in_nf": r3["not_in_nf"],
                   "t3_subspaces_with_failure": r3["subspaces_with_failure"]}
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY rank3 all_match {all(graded.values())}", flush=True)
        write_out({"t2": r2, "t3": r3, "graded": graded, "exploratory": explore},
                  args.out_dir, "rank3.json")
    elif args.part == "aniso-small":
        tabs = {}
        res = {}
        for t, dmax in ((1, 2), (2, 3), (3, 3)):
            levels, fin = singular_subspaces(t, dmax, deadline)
            res[f"t{t}_levels"] = {str(c): len(v) for c, v in levels.items()}
            for d in range(1, dmax + 1):
                st = aniso_search(t, d, levels, tabs, deadline)
                res[f"t{t}_d{d}"] = st
                print(f"t={t} d={d}: {json.dumps({k: v for k, v in st.items() if k != 'examples'})}",
                      flush=True)
        graded = {
            "t1_d1_positive": res["t1_d1"]["systems_with_anisotropic"] > 0,
            "t1_d2_zero": res["t1_d2"]["finished"] and res["t1_d2"]["anisotropic_sigmas"] == 0,
            "t2_d2_positive": res["t2_d2"]["systems_with_anisotropic"] > 0,
            "t2_d3_zero": res["t2_d3"]["finished"] and res["t2_d3"]["anisotropic_sigmas"] == 0,
            "t3_d2_positive": res["t3_d2"]["systems_with_anisotropic"] > 0,
            "t3_d3_positive": res["t3_d3"]["systems_with_anisotropic"] > 0,
        }
        print(f"levels: t1 {res['t1_levels']}, t2 {res['t2_levels']}, t3 {res['t3_levels']}",
              flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"SUMMARY aniso-small all_match {all(graded.values())}", flush=True)
        write_out({"results": res, "graded": graded}, args.out_dir, "aniso-small.json")
    else:
        tabs = {}
        levels, fin = singular_subspaces(3, 4, deadline)
        print(f"t3 singular levels {({c: len(v) for c, v in levels.items()})}, finished {fin}",
              flush=True)
        st = aniso_search(3, 4, levels, tabs, deadline) if fin else {"finished": False}
        print(f"t3 d4: {json.dumps({k: v for k, v in st.items() if k != 'examples'})}", flush=True)
        print(f"t3 d4 examples: {json.dumps(st.get('examples', []))}", flush=True)
        explore = {"finished": st.get("finished", False),
                   "anisotropic_d4": st.get("systems_with_anisotropic")}
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY aniso-t3d4 finished {explore['finished']}", flush=True)
        write_out({"levels": {str(c): len(v) for c, v in levels.items()}, "d4": st},
                  args.out_dir, "aniso-t3d4.json")


if __name__ == "__main__":
    main()
