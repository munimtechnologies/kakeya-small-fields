# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""How much codimension does Lemma 20 of finite-groups.md really need? An exact search for every
dimension t = dim X <= 2 and a sampled search for t = 3 (section 14, the case left open for
(a, b) = (6, 2) and (5, 3)).

Setting. X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta, alpha : V -> End(X)
linear, and

    alpha(h') sigma(h) = (I + alpha(h)) beta(h, h')     for all h, h' in V.          (*)

Let M(t) be the largest, over all such systems, of the least codimension of a subspace of V on
which sigma vanishes. Lemma 20 gives M(2) <= 4. Draft Lemma 22 (Lemma 15 read again) gives
M(1) <= 1, and the system sigma = x1 x2, alpha = x1 + x2 on F_2^2 shows M(1) = 1. The open case of
section 14 needs M(3) <= b + 3: M(3) <= 5 would settle (6, 2), M(3) <= 6 would settle (5, 3).

Reduction (draft Lemma 21). Let K = ker alpha and K_0 = K n ker sigma. For k in K_0, (*) with
h = k gives beta(k, h') = 0, so K_0 lies in the radical of beta and sigma, alpha factor through
V / K_0, of dimension rank alpha + dim sigma(K). Two linear maps onto the same C <= End(X) with
kernels of the same dimension y differ by an automorphism of V. So M(t) is the largest least
codimension over the systems V = F_2^(c + y), alpha(h) = the combination of a basis of C given by
the first c coordinates of h, with C running over the subspaces of End(X) (c = dim C) and
y = 0..t, and sigma running over all solutions of (*). The solutions form a vector space, found by
linear algebra (both sides of (*) have degree <= 2 in h and are linear in h', so h of weight <= 2
and h' in a basis suffice).

Also checked: K_0 lies in rad beta for every solution (Lemma 21(a)); if alpha(V) = End(X) and
t >= 2, then sigma = 0 (Lemma 21(c)), so the solution space is 0.

Parts. t1: all of C <= F_2 and y <= 1 (exact). t2: all 67 subspaces C of M_2(F_2) and y <= 2, every
solution sigma when the solution space has dimension <= FULL_BITS (exact when no system is
sampled). t3: structured subspaces of M_3(F_2) and random subspaces of them and of M_3(F_2), with
y <= 3 and m <= 10, sampled solutions, under a time budget (exploratory: a lower bound on M(3)).
The least codimension is computed exactly by a branch-and-bound search for the largest subspace
inside the zero set of sigma.

Vectors of F_2^m are int bitmasks. A t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c. sigma is a tuple of t masks of 2^m bits (bit h of the i-th is the i-th coordinate of
sigma(h)). Pure Python, no dependencies.

Usage: python plane_search.py [--out-dir DIR] [--part t1t2|t3|all] [--budget-minutes 40]
"""
import argparse
import itertools
import json
import os
import random
import time

FULL_BITS = 14


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
    """The matrix with a 1 in each (r, c) of cells."""
    return sum(1 << (t * r + c) for r, c in cells)


# ---------- quadratic maps V -> F_2^t ----------

def monomials(m):
    return [(i, i) for i in range(m)] + list(itertools.combinations(range(m), 2))


def mon_tables(m):
    return [sum(1 << h for h in range(1 << m) if (h >> i) & 1 and (h >> j) & 1)
            for i, j in monomials(m)]


def sigma_from_coeffs(c, tabs, t):
    """sigma for the coefficient vector c (bits i N .. i N + N - 1 for coordinate i)."""
    N = len(tabs)
    return tuple(combine(tabs, (c >> (i * N)) & ((1 << N) - 1)) for i in range(t))


def sig(S, h):
    out = 0
    for i, q in enumerate(S):
        out |= ((q >> h) & 1) << i
    return out


def beta(S, h, hp):
    return sig(S, h ^ hp) ^ sig(S, h) ^ sig(S, hp)


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


def identity_holds(at, S, m, t, rng=None, samples=None):
    """(*) on every pair (h, h'), or on `samples` random pairs."""
    if samples is None:
        pairs = itertools.product(range(1 << m), repeat=2)
    else:
        pairs = ((rng.randrange(1 << m), rng.randrange(1 << m)) for _ in range(samples))
    one = identity(t)
    for h, hp in pairs:
        b = beta(S, h, hp)
        if mat_apply(at[hp], sig(S, h), t) != mat_apply(at[h] ^ one, b, t):
            return False
    return True


# ---------- the largest subspace on which sigma vanishes ----------

def zero_set(S, m):
    nz = 0
    for q in S:
        nz |= q
    return [h for h in range(1, 1 << m) if not (nz >> h) & 1]


def max_singular_dim(zeros, node_limit=300000):
    """(largest dim of a subspace T with T minus 0 inside zeros, exact flag).

    Branch and bound. At a node with span S (dim d), cand is the set of c outside S with c + S inside
    the zero set; it is a union of cosets of S, so at most log2(|cand| / 2^d + 1) more dimensions are
    possible. After a branch on v, the coset v + S is dropped: every subspace through it is done."""
    state = {"best": 0, "nodes": 0, "exact": True}

    def dfs(S, d, cand):
        state["nodes"] += 1
        if d > state["best"]:
            state["best"] = d
        if state["nodes"] > node_limit:
            state["exact"] = False
            return
        cand = set(cand)
        while cand:
            if d + (((len(cand) >> d) + 1).bit_length() - 1) <= state["best"]:
                return
            v = min(cand)
            coset = [x ^ v for x in S]
            dfs(S + coset, d + 1, [c for c in cand if (c ^ v) in cand])
            if not state["exact"]:
                return
            cand.difference_update(coset)

    dfs([0], 0, zeros)
    return state["best"], state["exact"]


def min_codim(S, m, node_limit=300000):
    best, exact = max_singular_dim(zero_set(S, m), node_limit)
    return m - best, exact


# ---------- one system ----------

def k0_in_radical(S, m, c):
    """Lemma 21(a): every k in K_0 = ker alpha n ker sigma has beta(k, e_i) = 0 for each basis e_i.

    Here ker alpha is spanned by the last m - c coordinates (alpha's basis is independent)."""
    K = [h << c for h in range(1 << (m - c))]
    for k in K:
        if sig(S, k):
            continue
        for i in range(m):
            if beta(S, k, 1 << i):
                return False
    return True


def run_system(Cbasis, y, t, tabs_by_m, rng, full_bits=FULL_BITS, samples=256, node_limit=300000,
               full_identity_m=6, deadline=None):
    """Solve one system and return its record: solution dim, largest least codimension found, etc.

    Past the deadline (a time.time() value) no further solutions are examined, and the record
    is marked as not full."""
    m, at = system(Cbasis, y)
    if m not in tabs_by_m:
        tabs_by_m[m] = mon_tables(m)
    tabs = tabs_by_m[m]
    sol = solve_sigma(at, m, t)
    D = len(sol)
    rec = {"c": len(Cbasis), "y": y, "m": m, "sol_dim": D, "max_codim": 0, "full": True,
           "exact": True, "k0_violations": 0, "identity_violations": 0, "sigmas": 0, "best": None}
    if D == 0:
        return rec
    tables = [sigma_from_coeffs(v, tabs, t) for v in sol]
    if D <= full_bits:
        def gen():
            cur = tuple(0 for _ in range(t))
            coef = 0
            for i in range(1, 1 << D):
                b = (i & -i).bit_length() - 1
                cur = tuple(x ^ z for x, z in zip(cur, tables[b]))
                coef ^= sol[b]
                yield cur, coef
    else:
        rec["full"] = False

        def gen():
            for i in range(D):
                yield tables[i], sol[i]
            for _ in range(samples):
                c = rng.getrandbits(D)
                S = tuple(0 for _ in range(t))
                coef = 0
                for i in range(D):
                    if (c >> i) & 1:
                        S = tuple(x ^ z for x, z in zip(S, tables[i]))
                        coef ^= sol[i]
                yield S, coef
    checked = 0
    for S, coef in gen():
        if deadline is not None and time.time() > deadline:
            rec["full"] = False
            rec["cut"] = True
            break
        rec["sigmas"] += 1
        cd, ex = min_codim(S, m, node_limit)
        if not ex:
            rec["exact"] = False
        if checked < 3:
            if not k0_in_radical(S, m, len(Cbasis)):
                rec["k0_violations"] += 1
            if m <= full_identity_m:
                ok = identity_holds(at, S, m, t)
            else:
                ok = identity_holds(at, S, m, t, rng=rng, samples=4000)
            if not ok:
                rec["identity_violations"] += 1
            checked += 1
        if cd > rec["max_codim"]:
            rec["max_codim"] = cd
            rec["best"] = {"C": list(Cbasis), "y": y, "coeffs": coef}
            if not k0_in_radical(S, m, len(Cbasis)):
                rec["k0_violations"] += 1
    return rec


# ---------- part t1 and t2: every subspace C (exact) ----------

def exact_part(t, seed=1, verbose=False):
    rng = random.Random(seed)
    tabs = {}
    st = {"t": t, "systems": 0, "max_codim": 0, "exact": True, "by_c_y": {}, "hist": {},
          "k0_violations": 0, "identity_violations": 0, "full_action_sol_dims": [], "best": None,
          "argmax_count": 0}
    for c in range(t * t + 1):
        for B in subspaces(t * t, c):
            for y in range(t + 1):
                rec = run_system(B, y, t, tabs, rng)
                st["systems"] += 1
                st["k0_violations"] += rec["k0_violations"]
                st["identity_violations"] += rec["identity_violations"]
                if not (rec["full"] and rec["exact"]):
                    st["exact"] = False
                key = f"{c},{y}"
                st["by_c_y"][key] = max(st["by_c_y"].get(key, 0), rec["max_codim"])
                hk = str(rec["max_codim"])
                st["hist"][hk] = st["hist"].get(hk, 0) + 1
                if c == t * t:
                    st["full_action_sol_dims"].append(rec["sol_dim"])
                if rec["max_codim"] > st["max_codim"]:
                    st["max_codim"] = rec["max_codim"]
                    st["best"] = rec["best"]
                    st["argmax_count"] = 0
                if rec["max_codim"] == st["max_codim"] and rec["max_codim"] > 0:
                    st["argmax_count"] += 1
        if verbose:
            row = {k: v for k, v in st["by_c_y"].items() if k.split(",")[0] == str(c)}
            print(f"t={t} dim C={c}: done, max so far {st['max_codim']}, by (c, y) {row}",
                  flush=True)
    return st


# ---------- part t3: structured and random subspaces of M_3(F_2) ----------

def structured_3():
    t = 3
    cells = [(r, c) for r in range(3) for c in range(3)]
    e = lambda *cs: entries(t, cs)
    w = e((1, 0), (2, 1), (0, 2), (1, 2))      # companion matrix of x^3 + x + 1
    N = e((0, 1), (1, 2))                       # nilpotent Jordan block
    one = identity(t)
    fam = {
        "End": [e(p) for p in cells],
        "trace0": [e(p) for p in cells if p[0] != p[1]] + [e((0, 0), (1, 1)), e((1, 1), (2, 2))],
        "fix_line": [e(p) for p in cells if p not in ((1, 0), (2, 0))],
        "stab_plane": [e(p) for p in cells if p not in ((2, 0), (2, 1))],
        "upper": [e((r, c)) for r, c in cells if r <= c],
        "kill_e1": [e(p) for p in cells if p[1] != 0],
        "image_in_plane": [e(p) for p in cells if p[0] != 2],
        "symmetric": [e((i, i)) for i in range(3)] + [e((i, j), (j, i))
                                                     for i, j in itertools.combinations(range(3), 2)],
        "block_2_1": [e((0, 0)), e((0, 1)), e((1, 0)), e((1, 1)), e((2, 2))],
        "five": [e((0, 0)), e((1, 1)), e((0, 2)), e((1, 2)), e((2, 2))],
        "diag": [e((i, i)) for i in range(3)],
        "strict_upper": [e((r, c)) for r, c in cells if r < c],
        "kill_plane": [e((r, 2)) for r in range(3)],
        "alternating": [e((i, j), (j, i)) for i, j in itertools.combinations(range(3), 2)],
        "F8": [one, w, mat_mul(w, w, t)],
        "jordan": [one, N, mat_mul(N, N, t)],
        "rank1_row": [e((0, c)) for c in range(3)],
        "rank1_col": [e((r, 0)) for r in range(3)],
    }
    return {k: independent(v) for k, v in fam.items()}


def random_subspace(B, d, rng):
    while True:
        rows = [combine(B, rng.getrandbits(len(B))) for _ in range(d)]
        if rank_f2(rows) == d:
            return rows


def t3_part(budget_seconds, seed=3, m_max=10, random_per_dim=3, verbose=True):
    t = 3
    rng = random.Random(seed)
    tabs = {}
    start = time.time()
    st = {"t": 3, "systems": 0, "max_codim": 0, "by_source": {}, "hist": {}, "k0_violations": 0,
          "identity_violations": 0, "inexact": 0, "sampled_systems": 0, "End_sol_dims": [],
          "systems_with_codim_ge_5": 0, "systems_with_codim_ge_6": 0, "systems_with_codim_ge_7": 0,
          "best": None, "finished": False}
    fam = structured_3()
    jobs = []
    for name, B in fam.items():
        jobs.append((name, B))
    for name, B in fam.items():
        for d in range(2, len(B)):
            for i in range(random_per_dim):
                jobs.append((f"{name}/sub{d}", random_subspace(B, d, rng)))
    for d in range(2, 9):
        for i in range(2 * random_per_dim):
            jobs.append((f"M3/rand{d}", random_subspace(fam["End"], d, rng)))
    for name, B in jobs:
        for y in range(4):
            if len(B) + y > m_max:
                continue
            if time.time() - start > budget_seconds:
                st["stopped_at"] = f"{name} y={y}"
                return st
            rec = run_system(B, y, t, tabs, rng, full_bits=8, samples=64, node_limit=20000,
                             full_identity_m=5, deadline=start + budget_seconds)
            st["systems"] += 1
            st["k0_violations"] += rec["k0_violations"]
            st["identity_violations"] += rec["identity_violations"]
            if not rec["exact"]:
                st["inexact"] += 1
            if not rec["full"]:
                st["sampled_systems"] += 1
            if name == "End":
                st["End_sol_dims"].append(rec["sol_dim"])
            src = name.split("/")[0]
            st["by_source"][src] = max(st["by_source"].get(src, 0), rec["max_codim"])
            hk = str(rec["max_codim"])
            st["hist"][hk] = st["hist"].get(hk, 0) + 1
            for k in (5, 6, 7):
                if rec["max_codim"] >= k:
                    st[f"systems_with_codim_ge_{k}"] += 1
            if rec["max_codim"] > st["max_codim"]:
                st["max_codim"] = rec["max_codim"]
                st["best"] = dict(rec["best"], source=name, m=rec["m"], sol_dim=rec["sol_dim"])
            if verbose:
                print(f"t=3 {name} c={len(B)} y={y}: sol dim {rec['sol_dim']}, max codim "
                      f"{rec['max_codim']}{'' if rec['full'] else ' (sampled)'}"
                      f"{'' if rec['exact'] else ' (node limit)'}", flush=True)
    st["finished"] = True
    return st


# ---------- predictions ----------

def grade_exact(st1, st2):
    """The pre-registered predictions for the exact parts."""
    return {
        "t1_max_is_1": st1["max_codim"] == 1 and st1["exact"],
        "t2_max_le_4": st2["max_codim"] <= 4,
        "t2_full_action_sol_dims_zero": st2["full_action_sol_dims"] == [0, 0, 0],
        "no_k0_violations": st1["k0_violations"] + st2["k0_violations"] == 0,
        "no_identity_violations": st1["identity_violations"] + st2["identity_violations"] == 0,
    }


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["t1t2", "t3", "all"], default="all")
    ap.add_argument("--budget-minutes", type=float, default=40.0)
    args = ap.parse_args()
    if args.part in ("t1t2", "all"):
        st1 = exact_part(1, verbose=True)
        print(f"t1: {json.dumps(st1, sort_keys=True)}", flush=True)
        st2 = exact_part(2, verbose=True)
        print(f"t2: {json.dumps(st2, sort_keys=True)}", flush=True)
        grade = grade_exact(st1, st2)
        ok = all(grade.values())
        print(f"predictions: {json.dumps(grade, sort_keys=True)}", flush=True)
        print(f"M(1) = {st1['max_codim']}; M(2) = {st2['max_codim']} "
              f"({'exact' if st2['exact'] else 'lower bound: some systems were sampled'})", flush=True)
        print(f"SUMMARY t1t2 all_match {ok}", flush=True)
        write_out({"t1": st1, "t2": st2, "predictions": grade, "all_match": ok}, args.out_dir,
                  "plane-t1t2.json")
    if args.part in ("t3", "all"):
        st3 = t3_part(args.budget_minutes * 60)
        print(f"t3: {json.dumps(st3, sort_keys=True)}", flush=True)
        ok3 = st3["k0_violations"] == 0 and st3["identity_violations"] == 0 and \
            all(d == 0 for d in st3["End_sol_dims"])
        print(f"largest least codimension found for t = 3: {st3['max_codim']} "
              f"(a lower bound on M(3); finished {st3['finished']})", flush=True)
        print(f"SUMMARY t3 consistency {ok3}", flush=True)
        write_out({"t3": st3, "consistency": ok3}, args.out_dir, "plane-t3.json")


if __name__ == "__main__":
    main()
