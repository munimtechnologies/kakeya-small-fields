# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Does every solution of the identity of Lemma 20 have the normal form of Lemma 23 of
finite-groups.md (section 14, version 1.7.5)?

Setting as in plane_search.py. X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Normal form: sigma(h) = (I + A_h) lam(h) for a linear map lam : V -> X. Then sigma vanishes on
ker lam, of codimension <= t (Lemma 23(b)). Lemma 23 proves the normal form when rank alpha <= 1
and shows M(t) >= t with a diagonal example; if every system had the normal form, M(t) = t and
Proposition 20 would settle every Z_4^a x Z_2^b.

For each system (C, y) of Lemma 21's reduction (V = F_2^(c + y), alpha = the combination of a basis
of C given by the first c coordinates), the solutions of (*) form a space Sol, and the maps
Q_lam(h) = (I + A_h) lam(h) form a space NF, spanned by lam = E_(r, j) (lam(h) = h_j e_r). The script
checks Sol <= NF by ranks, records dim (Sol n NF), checks pointwise that sigma(h) lies in
Im(I + A_h) (Lemma 23(a)) for up to four basis solutions, and, for a system where Sol is not inside
NF, computes the least codimension of a subspace on which a solution outside NF vanishes.

Parts. small: every system with t = 1 (4) and t = 2 (all 67 subspaces C of M_2(F_2), y <= 2: 201),
and the diagonal example of Lemma 23(d) for t = 1, 2, 3 (identity on every pair, exact least
codimension, membership in Sol and NF). t3: 18 structured subspaces of M_3(F_2), random subspaces
of them and of M_3(F_2), y <= 3, m <= 10. t4: structured and random subspaces of M_4(F_2), m <= 8.
t3c2: every subspace of M_3(F_2) of dimension 1 (511) and 2 (43,435), y <= 3, under a time budget.

Vectors of F_2^m are int bitmasks. A t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c. A quadratic map is stored by its coefficient vector: bit i N + k is the coefficient of the
k-th monomial of monomials(m) in coordinate i (N = number of monomials). Pure Python, no
dependencies; the helpers are copied from plane_search.py so that this file runs on its own.

Usage: python normal_form.py [--out-dir DIR] [--part small|t3|t4|t3c2] [--budget-minutes 30]
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


def in_image(A, x, t):
    """Is x in Im(I + A)?"""
    one = identity(t)
    cols = [mat_apply(A ^ one, 1 << c, t) for c in range(t)]
    return rank_f2(cols + [x]) == rank_f2(cols)


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


def coeffs_of(f, m, t):
    """Coefficient vector of the quadratic map h -> f(h) (f(0) = 0, degree <= 2): the coefficient of
    x_i is f(e_i), and that of x_i x_j is f(e_i + e_j) + f(e_i) + f(e_j)."""
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
    """(largest dim of a subspace T with T minus 0 inside zeros, exact flag); as in plane_search.py."""
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


# ---------- the normal form ----------

def nf_basis(at, m, t):
    """Coefficient vectors of Q_lam(h) = (I + A_h) lam(h) for lam = E_(r, j), lam(h) = h_j e_r."""
    out = []
    for j in range(m):
        for r in range(t):
            e = 1 << r

            def f(h, j=j, e=e):
                return (e ^ mat_apply(at[h], e, t)) if (h >> j) & 1 else 0

            out.append(coeffs_of(f, m, t))
    return out


def nf_check(Cbasis, y, t, tabs, rng, pointwise=4, codim_samples=32):
    """Record for one system: dim Sol, dim NF, dim (Sol n NF), Sol <= NF?, Lemma 23(a) pointwise."""
    m, at = system(Cbasis, y)
    if m not in tabs:
        tabs[m] = mon_tables(m)
    sol = solve_sigma(at, m, t)
    D = len(sol)
    rec = {"c": len(Cbasis), "y": y, "m": m, "sol_dim": D, "nf_dim": None, "inter_dim": D,
           "in_nf": True, "image_violations": 0, "outside_max_codim": None}
    if D == 0:
        return rec
    nf = nf_basis(at, m, t)
    rn = rank_f2(nf)
    rboth = rank_f2(nf + sol)
    rec["nf_dim"] = rn
    rec["inter_dim"] = rn + D - rboth
    rec["in_nf"] = rboth == rn
    for v in sol[:pointwise]:
        S = sigma_from_coeffs(v, tabs[m], t)
        for h in range(1 << m):
            if not in_image(at[h], sig(S, h), t):
                rec["image_violations"] += 1
                break
    if not rec["in_nf"]:
        outside = [v for v in sol if rank_f2(nf + [v]) > rn]
        cands = list(outside)
        for _ in range(codim_samples):
            v = combine(sol, rng.getrandbits(D))
            if v and rank_f2(nf + [v]) > rn:
                cands.append(v)
        best = 0
        for v in cands:
            cd, _ = min_codim(sigma_from_coeffs(v, tabs[m], t), m, 20000)
            best = max(best, cd)
        rec["outside_max_codim"] = best
        rec["example"] = {"C": list(Cbasis), "y": y, "coeffs": outside[0]}
    return rec


def new_stats(part, t):
    return {"part": part, "t": t, "systems": 0, "nonzero": 0, "not_in_nf": 0,
            "rank_le1_not_in_nf": 0, "image_violations": 0, "max_sol_dim": 0,
            "outside_max_codim": 0, "outside_codim_gt_t": 0, "examples": [], "finished": False}


def add(st, rec, label):
    st["systems"] += 1
    if rec["sol_dim"]:
        st["nonzero"] += 1
    st["max_sol_dim"] = max(st["max_sol_dim"], rec["sol_dim"])
    st["image_violations"] += rec["image_violations"]
    if not rec["in_nf"]:
        st["not_in_nf"] += 1
        if rec["c"] <= 1:
            st["rank_le1_not_in_nf"] += 1
        oc = rec["outside_max_codim"] or 0
        st["outside_max_codim"] = max(st["outside_max_codim"], oc)
        if oc > st["t"]:
            st["outside_codim_gt_t"] += 1
        if len(st["examples"]) < 10:
            st["examples"].append(dict(rec["example"], source=label, sol_dim=rec["sol_dim"],
                                       inter_dim=rec["inter_dim"], outside_max_codim=oc))


# ---------- the diagonal example of Lemma 23(d) ----------

def diag_example(t):
    """alpha(h) = diag(u_1..u_t), sigma_i(h) = (1 + u_i) v_i, u_i = bit i, v_i = bit t + i."""
    Cbasis = [entries(t, [(i, i)]) for i in range(t)]
    m, at = system(Cbasis, t)
    S = tuple(sum(1 << h for h in range(1 << m) if (h >> (t + i)) & 1 and not (h >> i) & 1)
              for i in range(t))
    return Cbasis, m, at, S


def check_diag(t):
    Cbasis, m, at, S = diag_example(t)
    coef = coeffs_of(lambda h: sig(S, h), m, t)
    sol = solve_sigma(at, m, t)
    nf = nf_basis(at, m, t)
    cd, exact = min_codim(S, m)
    return {"t": t, "m": m, "identity": identity_holds(at, S, m, t),
            "in_sol": rank_f2(sol + [coef]) == rank_f2(sol),
            "in_nf": rank_f2(nf + [coef]) == rank_f2(nf),
            "least_codim": cd, "exact": exact}


# ---------- parts ----------

def part_exact(t, rng, tabs):
    st = new_stats(f"t{t}", t)
    st["full_action_sol_dims"] = []
    for c in range(t * t + 1):
        for B in subspaces(t * t, c):
            for y in range(t + 1):
                rec = nf_check(B, y, t, tabs, rng)
                add(st, rec, f"c{c}")
                if c == t * t:
                    st["full_action_sol_dims"].append(rec["sol_dim"])
        print(f"t={t} dim C={c}: systems {st['systems']}, not in NF {st['not_in_nf']}", flush=True)
    st["finished"] = True
    return st


def structured(t):
    cells = [(r, c) for r in range(t) for c in range(t)]
    e = lambda *cs: entries(t, cs)
    one = identity(t)
    fam = {
        "End": [e(p) for p in cells],
        "fix_line": [e(p) for p in cells if not (p[1] == 0 and p[0] != 0)],
        "stab_plane": [e(p) for p in cells if not (p[0] == t - 1 and p[1] < t - 1)],
        "upper": [e((r, c)) for r, c in cells if r <= c],
        "kill_e1": [e(p) for p in cells if p[1] != 0],
        "image_in_hyperplane": [e(p) for p in cells if p[0] != t - 1],
        "symmetric": [e((i, i)) for i in range(t)] + [e((i, j), (j, i))
                                                     for i, j in itertools.combinations(range(t), 2)],
        "diag": [e((i, i)) for i in range(t)],
        "diag_plus_I": [one] + [e((i, i)) for i in range(t - 1)],
        "strict_upper": [e((r, c)) for r, c in cells if r < c],
        "kill_hyperplane": [e((r, t - 1)) for r in range(t)],
        "alternating": [e((i, j), (j, i)) for i, j in itertools.combinations(range(t), 2)],
        "rank1_row": [e((0, c)) for c in range(t)],
        "rank1_col": [e((r, 0)) for r in range(t)],
        "jordan": [one] + [e(*[(i, i + k) for i in range(t - k)]) for k in range(1, t)],
        "diag_and_corner": [e((i, i)) for i in range(t)] + [e((0, t - 1))],
    }
    if t == 3:
        w = e((1, 0), (2, 1), (0, 2), (1, 2))      # companion matrix of x^3 + x + 1
        fam["F8"] = [one, w, mat_mul(w, w, t)]
        fam["block_2_1"] = [e((0, 0)), e((0, 1)), e((1, 0)), e((1, 1)), e((2, 2))]
        fam["five"] = [e((0, 0)), e((1, 1)), e((0, 2)), e((1, 2)), e((2, 2))]
    if t == 4:
        fam["blocks_2_2"] = [e((r, c)) for r, c in cells if (r < 2) == (c < 2)]
        fam["block_diag_idem"] = [e((0, 0), (1, 1)), e((2, 2), (3, 3)), e((0, 1)), e((2, 3))]
    return {k: independent(v) for k, v in fam.items()}


def random_subspace(B, d, rng):
    while True:
        rows = [combine(B, rng.getrandbits(len(B))) for _ in range(d)]
        if rank_f2(rows) == d:
            return rows


def part_sampled(t, budget_seconds, rng, tabs, m_max, y_max, per_dim, rand_dims, rand_count):
    start = time.time()
    st = new_stats(f"t{t}", t)
    st["End_sol_dims"] = []
    fam = structured(t)
    End = fam["End"]
    jobs = [(name, B) for name, B in fam.items()]
    for name, B in fam.items():
        for d in range(2, len(B)):
            for _ in range(per_dim):
                jobs.append((f"{name}/sub{d}", random_subspace(B, d, rng)))
    for d in rand_dims:
        for _ in range(rand_count):
            jobs.append((f"M{t}/rand{d}", random_subspace(End, d, rng)))
    for name, B in jobs:
        for y in range(y_max + 1):
            if len(B) + y > m_max:
                continue
            if time.time() - start > budget_seconds:
                st["stopped_at"] = f"{name} y={y}"
                return st
            rec = nf_check(B, y, t, tabs, rng)
            add(st, rec, name)
            if name == "End":
                st["End_sol_dims"].append(rec["sol_dim"])
            print(f"t={t} {name} c={len(B)} y={y}: sol {rec['sol_dim']}, NF n Sol "
                  f"{rec['inter_dim']}, in NF {rec['in_nf']}"
                  f"{'' if rec['in_nf'] else ', outside codim ' + str(rec['outside_max_codim'])}",
                  flush=True)
    st["finished"] = True
    return st


def part_t3c2(budget_seconds, rng, tabs):
    start = time.time()
    st = new_stats("t3c2", 3)
    st["by_c"] = {}
    for c in (1, 2):
        done = 0
        for B in subspaces(9, c):
            for y in range(4):
                if time.time() - start > budget_seconds:
                    st["stopped_at"] = f"c={c} after {done} subspaces"
                    return st
                add(st, nf_check(B, y, 3, tabs, rng, pointwise=2), f"c{c}")
            done += 1
            if done % 5000 == 0:
                print(f"t3c2 c={c}: {done} subspaces, not in NF {st['not_in_nf']}", flush=True)
        st["by_c"][str(c)] = {"subspaces": done, "not_in_nf_so_far": st["not_in_nf"]}
        print(f"t3c2 c={c} done: {done} subspaces, not in NF {st['not_in_nf']}", flush=True)
    st["finished"] = True
    return st


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["small", "t3", "t4", "t3c2"], default="small")
    ap.add_argument("--budget-minutes", type=float, default=30.0)
    args = ap.parse_args()
    rng = random.Random(5)
    tabs = {}
    budget = args.budget_minutes * 60
    if args.part == "small":
        st1 = part_exact(1, rng, tabs)
        st2 = part_exact(2, rng, tabs)
        diag = [check_diag(t) for t in (1, 2, 3)]
        graded = {
            "t1_all_in_nf": st1["not_in_nf"] == 0,
            "t2_rank_le1_in_nf": st2["rank_le1_not_in_nf"] == 0,
            "no_image_violations": st1["image_violations"] + st2["image_violations"] == 0,
            "t2_full_action_zero": st2["full_action_sol_dims"] == [0, 0, 0],
            "diag_ok": all(d["identity"] and d["in_sol"] and d["in_nf"] and d["exact"]
                           and d["least_codim"] == d["t"] for d in diag),
        }
        explore = {"t2_all_in_nf": st2["not_in_nf"] == 0, "t2_not_in_nf": st2["not_in_nf"],
                   "t2_outside_max_codim": st2["outside_max_codim"]}
        out = {"t1": st1, "t2": st2, "diag": diag, "graded": graded, "exploratory": explore}
        print(f"diag: {json.dumps(diag)}", flush=True)
        print(f"t2 summary: systems {st2['systems']}, nonzero {st2['nonzero']}, not in NF "
              f"{st2['not_in_nf']}, examples {json.dumps(st2['examples'])}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY small all_match {all(graded.values())}", flush=True)
        write_out(out, args.out_dir, "nf-small.json")
    elif args.part in ("t3", "t4"):
        t = 3 if args.part == "t3" else 4
        if t == 3:
            st = part_sampled(3, budget, rng, tabs, m_max=10, y_max=3, per_dim=2,
                              rand_dims=range(2, 9), rand_count=8)
        else:
            st = part_sampled(4, budget, rng, tabs, m_max=8, y_max=2, per_dim=1,
                              rand_dims=range(2, 7), rand_count=4)
        graded = {"no_image_violations": st["image_violations"] == 0,
                  "rank_le1_in_nf": st["rank_le1_not_in_nf"] == 0,
                  "End_zero": all(d == 0 for d in st["End_sol_dims"])}
        print(f"{args.part}: {json.dumps({k: v for k, v in st.items() if k != 'examples'}, sort_keys=True)}",
              flush=True)
        print(f"examples: {json.dumps(st['examples'])}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: all in NF {st['not_in_nf'] == 0}, largest codimension outside NF "
              f"{st['outside_max_codim']}, above t: {st['outside_codim_gt_t']}", flush=True)
        print(f"SUMMARY {args.part} all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded}, args.out_dir, f"nf-{args.part}.json")
    else:
        st = part_t3c2(budget, rng, tabs)
        graded = {"no_image_violations": st["image_violations"] == 0,
                  "rank_le1_in_nf": st["rank_le1_not_in_nf"] == 0}
        print(f"t3c2: {json.dumps({k: v for k, v in st.items() if k != 'examples'}, sort_keys=True)}",
              flush=True)
        print(f"examples: {json.dumps(st['examples'])}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: all in NF {st['not_in_nf'] == 0}", flush=True)
        print(f"SUMMARY t3c2 all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded}, args.out_dir, "nf-t3c2.json")


if __name__ == "__main__":
    main()
