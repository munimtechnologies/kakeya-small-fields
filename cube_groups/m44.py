# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m44: shape (c) of Case B at rank 4 for t = 7 and dim V = 9 (notes/a29.md, Lemma 85), split
by the image R of A_u and then by the matrix A_u itself, with the matrices M_n of Lemma 38
(notes/shape-c.md) as conditions.

Setting and encoding as in case_b.py and case_b_shapes.py. The form c of Lemma 37
(notes/case-b-shapes.md) at (t, k) = (7, 3) fixes

    x0 = sigma(u) = e_0,  P = phi(V) = span(e_1, ..., e_6),  A_u kills W = span(e_0, e_1, e_2),
    sigma(v_1) = e_1,  sigma(v_2) = e_2,  beta(v_1, v_2) = 0,  A_(v_1), A_(v_2) kill W,
    phi(v_(2+j)) = e_j.

Job m40b left the class cY of Lemma 81 UNKNOWN after 150 minutes, with only A_u e_3 and A_u e_4
fixed. Every base change in

    K = {g in GL(X) : g e_0 = e_0, g W = W, g P = P}

keeps the form: g acts on Y = W n P by some b in GL_2, and (v_1, v_2) is replaced by the basis of
span(v_1, v_2) on which the new sigma takes the values e_1, e_2 (sigma is linear there, as beta = 0
on N); the v_(2+j) are chosen again over g e_j. So R = Im A_u can be taken to be a representative of
its K-orbit, and then A_u a representative of its class under the stabiliser of R in K. By
Corollary 51 (notes/a24.md), dim(R n W) >= 2. Lemma 85 counts the K-orbits of such R by hand: 5.

How the split is computed. As in m43.py: the orbits of R are closures under generators of K (exact);
the classes of A_u (the 20160 matrices with kernel W and image R) are closures under conjugation by
NGENS random units of the algebra {g : g e_0 in span(e_0), g W <= W, g Y <= Y, g P <= P, g R <= R},
whose units are exactly the stabiliser of R in K. Every unit is checked to lie in it, so every
computed class lies inside one true class, and the split is complete whether or not the units
generate the stabiliser. At t = 5 and 6 the whole of K is enumerated and the computed classes must
equal the exact ones.

Each instance is the CNF of case_b_shapes.encode_shape(7, 3, 'c') with the columns of A_u on
e_3, ..., e_6 fixed by 28 unit clauses, and with new variables M_1, M_2 (the matrices of M_(v_1),
M_(v_2) on X / W in the basis [e_3], ..., [e_6]) tied to the system by Lemma 38:

    (S)  A_(v_i) e_(3+j) = A_u (sum over l of M_i[l][j] e_(3+l))         (Lemma 38, definition)
    (a)  rows 3 to 6 of beta(v_i, v_(2+j)) are 0 for j = 1, 2 and column j - 3 of M_i for j >= 3
    (b)  M_1 M_2 = M_2 M_1
    (51) M_n != 0 for every n != 0 in N, with M_u = I (Corollary 51: n -> A_n is one-to-one on N)

(S), (a) and (b) are 2 n t + 2 n (t - 1) + n^2 linear conditions (n = t - 3); (51) is 6 clauses.

Controls: case_b's (t, k) = (2, 1) example must be SAT; every class at t = 5, 6 (dim V = t + 2) must
be UNSAT, since A(t) = t there. Corollary 51 is proved only at t = 7, but extra conditions cannot turn
UNSAT into SAT. There is no positive control in form c: a satisfiable instance at t <= 6 would
contradict A(t) = t. The unit tests check the conditions on hand-made data instead.

Matrices are kept as tuples of columns (column c = image of e_c, a bit mask). sat_aniso.py uses
t^2-bit masks with entry (r, c) at bit t r + c.

Parts: selfcheck (pure Python), controls, solve [--part-index k --parts n], grade.

Usage: python m44.py --part selfcheck|controls|solve|grade [--part-index 0] [--parts 4]
                     [--group-minutes 140] [--cap-minutes 25] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

import case_b as cb
import case_b_shapes as csh
import sat_aniso as sa

T = 7
K = 3
NGENS = 24
MIN_BUDGET = 20.0
SMALL = (5, 6)
# Hand counts (notes/a29.md, Lemma 85), for A_u of rank t - 3.
HAND_K = {5: 576, 6: 64512, 7: 30965760}        # 6 x 4^(t-3) x |GL_(t-3)(F_2)|
HAND_R = {5: 7, 6: 99, 7: 995}
HAND_R_ORBITS = {5: {"YP": 1, "X": 3, "G": 3},
                 6: {"W": 1, "YP": 7, "Yn": 7, "X": 42, "G": 42},
                 7: {"W": 15, "YP": 35, "Yn": 105, "X": 420, "G": 420}}
HAND_W_CLASSES = {6: 1, 7: 5}                   # classes of A_u when R contains W
HAND_LIN = {5: 40, 6: 75, 7: 120}               # n (4 t - 2 + n), n = t - 3
AU_UNITS = {5: 10, 6: 18, 7: 28}                # t (t - 3)
NONZERO = 6


# ---------- vectors, subspaces, matrices (as in m43.py) ----------

def rref(vecs):
    """The reduced row echelon basis of span(vecs), pivots = leading bits, in decreasing order."""
    rows = []
    for v in vecs:
        for r in rows:
            if (v >> (r.bit_length() - 1)) & 1:
                v ^= r
        if v:
            q = v.bit_length() - 1
            rows = [r ^ v if (r >> q) & 1 else r for r in rows]
            rows.append(v)
            rows.sort(reverse=True)
    return tuple(rows)


def in_span(rows, v):
    return len(rref(list(rows) + [v])) == len(rows)


def dim_meet(a, b):
    return len(a) + len(b) - len(rref(list(a) + list(b)))


def gl_order(n):
    out = 1
    for i in range(n):
        out *= (1 << n) - (1 << i)
    return out


def subspaces(t, k):
    """Every k-dimensional subspace of F_2^t (as rref tuples), enumerated as reduced echelon forms."""
    out = []
    for piv in itertools.combinations(range(t), k):
        piv = sorted(piv, reverse=True)
        frees = [[b for b in range(q) if b not in piv] for q in piv]
        for bits in itertools.product(*[range(1 << len(f)) for f in frees]):
            rows = []
            for q, f, x in zip(piv, frees, bits):
                r = 1 << q
                for i, b in enumerate(f):
                    if (x >> i) & 1:
                        r |= 1 << b
                rows.append(r)
            out.append(tuple(rows))
    return sorted(out)


def identity(t):
    return sum(1 << (t * r + r) for r in range(t))


def cols_of(g, t):
    return [sa.mat_apply(g, 1 << c, t) for c in range(t)]


def apply_cols(cols, x):
    out = 0
    c = 0
    while x:
        if x & 1:
            out ^= cols[c]
        x >>= 1
        c += 1
    return out


def image_cols(cols, rows):
    return rref([apply_cols(cols, v) for v in rows])


def ann(rows, t):
    """Basis of {f : f . s = 0 for every s in rows}."""
    return sa.nullspace(list(rows), t)


def p_basis(p):
    return rref([1 << j for j in range(1, p + 1)])


def w_basis():
    return rref([1, 2, 4])


def y_basis():
    return rref([2, 4])


def orbits_under(items, gens, apply):
    """The closures of items under the maps apply(g, .), g in gens, as sorted lists; items must be
    sorted, and each orbit starts with its least element."""
    index = {x: i for i, x in enumerate(items)}
    perms = [[index[apply(g, x)] for x in items] for g in gens]
    seen = [False] * len(items)
    out = []
    for i0 in range(len(items)):
        if seen[i0]:
            continue
        seen[i0] = True
        orb, stack = [i0], [i0]
        while stack:
            i = stack.pop()
            for pm in perms:
                k = pm[i]
                if not seen[k]:
                    seen[k] = True
                    orb.append(k)
                    stack.append(k)
        out.append([items[i] for i in sorted(orb)])
    return out


def group_orbits(items, group, apply):
    """The orbits of a whole group (a list containing every element) on items: orbit of x = {g x}."""
    seen, out = set(), []
    for x in items:
        if x in seen:
            continue
        orb = sorted({apply(g, x) for g in group})
        seen.update(orb)
        out.append(orb)
    return out


# ---------- the group K and stabilisers ----------

def group_order(t):
    """|K| = |GL_2| x 2^(2 (t - 3)) x |GL_(t-3)|: K acts faithfully on P as the parabolic subgroup
    that keeps Y, and g e_0 = e_0."""
    return gl_order(2) * (1 << (2 * (t - K))) * gl_order(t - K)


def generators(t):
    """The elementary transvections g e_j = e_j + e_i (other e_c fixed) with 3 <= j < t and
    1 <= i < t, i != j, and e_1 -> e_1 + e_2, e_2 -> e_2 + e_1: they lie in K and generate it."""
    gens = []
    for j in range(K, t):
        for i in range(1, t):
            if i != j:
                gens.append(identity(t) ^ (1 << (t * i + j)))
    gens.append(identity(t) ^ (1 << (t * 2 + 1)))
    gens.append(identity(t) ^ (1 << (t * 1 + 2)))
    return gens


def keeps(g, t, rows):
    return image_cols(cols_of(g, t), rows) == tuple(rows)


def in_group(g, t, extra=()):
    return (sa.rank_f2(sa.rows_of(g, t)) == t and sa.mat_apply(g, 1, t) == 1
            and keeps(g, t, w_basis()) and keeps(g, t, p_basis(t - 1))
            and all(keeps(g, t, s) for s in extra))


def group_elements(t):
    """Every element of K, by closure (only for small t)."""
    gens = generators(t)
    one = identity(t)
    seen, frontier = {one}, [one]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = sa.mat_mul(s, g, t)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return sorted(seen)


def stab_algebra(t, subs):
    """Basis (t^2-bit masks) of {g : g S <= S for every S in subs}."""
    cons = []
    for S in subs:
        for f in ann(S, t):
            for s in S:
                cons.append(sum(1 << (t * r + c) for r in range(t) if (f >> r) & 1
                                for c in range(t) if (s >> c) & 1))
    return sa.nullspace(cons, t * t)


def stab_subs(t, r):
    return [(1,), w_basis(), y_basis(), p_basis(t - 1), r]


def random_units(t, subs, count, seed):
    """count uniform random units of the stabiliser algebra of subs (seeded); with span(e_0) among
    subs, each fixes e_0."""
    basis = stab_algebra(t, subs)
    rng = random.Random(seed)
    out, tries = [], 0
    while len(out) < count and tries < 200000:
        tries += 1
        g = sa.combine(basis, rng.getrandbits(len(basis)))
        if sa.rank_f2(sa.rows_of(g, t)) == t:
            out.append(g)
    return out, {"algebra_dim": len(basis), "tries": tries}


def unit_pair(g, t):
    return tuple(cols_of(g, t)), tuple(cols_of(sa.mat_inv(g, t), t))


def conj(gi, A):
    """g A g^-1 on column tuples: column c is g (A (g^-1 e_c))."""
    gc, gic = gi
    return tuple(apply_cols(gc, apply_cols(A, x)) for x in gic)


# ---------- the orbits of R and the classes of A_u ----------

def r_type(t, r):
    """The invariant of Lemma 85: W (R contains W); YP, Yn (R n W = Y, R in P or not); X (R n W a
    plane through e_0); G (another plane); None if dim(R n W) < 2."""
    meet = [x for x in range(1, 8) if in_span(r, x)]
    if len(meet) == 7:
        return "W"
    if len(meet) != 3:
        return None
    if sorted(meet) == [2, 4, 6]:
        return "YP" if dim_meet(r, p_basis(t - 1)) == len(r) else "Yn"
    return "X" if 1 in meet else "G"


def candidates(t):
    """The subspaces R of dimension t - 3 with dim(R n W) >= 2 (Corollary 51)."""
    return [r for r in subspaces(t, t - K) if dim_meet(r, w_basis()) >= 2]


def r_orbits(t):
    """[(rep, size)] for the K-orbits of candidates(t), exact (closure under generators of K),
    ordered by least element."""
    orbs = orbits_under(candidates(t), [cols_of(g, t) for g in generators(t)], image_cols)
    return [(o[0], len(o)) for o in orbs]


def matrices(t, r):
    """Every A with kernel exactly W and image exactly r, as column tuples: |GL_(t-3)| of them."""
    rvals = [sa.combine(list(r), c) for c in range(1, 1 << len(r))]
    out = []
    for ys in itertools.product(rvals, repeat=len(r)):
        if sa.rank_f2(list(ys)) == len(r):
            out.append((0,) * K + ys)
    return sorted(out)


def class_seed(t, ri):
    return 44000 + 1000 * t + 7907 * ri


def r_classes(t, ri, r):
    """[(rep, members)] for the closures of matrices(t, r) under conjugation by NGENS random units of
    the stabiliser of r in K, with stats."""
    units, st = random_units(t, stab_subs(t, r), NGENS, class_seed(t, ri))
    pairs = [unit_pair(g, t) for g in units]
    mats = matrices(t, r)
    cl = orbits_under(mats, pairs, conj)
    half = orbits_under(mats, pairs[:NGENS // 2], conj)
    st.update({"units": len(units), "units_ok": all(in_group(g, t, (r,)) for g in units),
               "stable": len(half) == len(cl), "matrices": len(mats)})
    return [(c[0], c) for c in cl], st


def classify(t):
    out = []
    for ri, (r, size) in enumerate(r_orbits(t)):
        cl, st = r_classes(t, ri, r)
        out.append({"r": r, "size": size, "type": r_type(t, r), "classes": cl, "stats": st})
    return out


# ---------- the encoding ----------

def add_hints(cnf, names, t, au):
    """The conditions (S), (a), (b) and (51) of the docstring; returns (M, linear conditions,
    non-zero clauses), M[i][l][j] the variables of M_i (i = 1, 2)."""
    A, B = names[0], names[2]
    n = t - K
    M = [None] + [[[cnf.new() for j in range(n)] for l in range(n)] for i in (1, 2)]
    lin = 0
    for i in (1, 2):
        for j in range(n):
            for r in range(t):
                cnf.xor_eq([A[i][r][K + j]] + [M[i][l][j] for l in range(n) if (au[K + l] >> r) & 1],
                           0)
                lin += 1
    for i in (1, 2):
        for j in range(1, t):
            for l in range(n):
                lits = [B[(i, 2 + j)][K + l]]
                if j >= K:
                    lits.append(M[i][l][j - K])
                cnf.xor_eq(lits, 0)
                lin += 1
    for a in range(n):
        for b in range(n):
            cnf.xor_eq([cnf.AND(M[1][a][l], M[2][l][b]) for l in range(n)]
                       + [cnf.AND(M[2][a][l], M[1][l][b]) for l in range(n)], 0)
            lin += 1
    z = [[cnf.xor_def([M[1][l][j], M[2][l][j]]) for j in range(n)] for l in range(n)]
    nz = 0
    for mat in (M[1], M[2], z):
        for plus_i in (False, True):
            cnf.clauses.append([-mat[l][j] if plus_i and l == j else mat[l][j]
                                for l in range(n) for j in range(n)])
            nz += 1
    return M, lin, nz


def encode_class(t, au, hints=True):
    """(cnf, names, info): encode_shape(t, 3, 'c') with A_u fixed on e_3, ..., e_(t-1); with hints,
    the conditions of add_hints. info: linear conditions, non-zero clauses, the first hint clause and
    variable, and the M variables."""
    cnf, names = csh.encode_shape(t, K, "c")
    A = names[0]
    for c in range(K, t):
        for row in range(t):
            cnf.clauses.append([A[0][row][c]] if (au[c] >> row) & 1 else [-A[0][row][c]])
    info = {"lin": 0, "nonzero": 0, "start": len(cnf.clauses), "first_var": cnf.nv + 1, "M": None}
    if hints:
        info["M"], info["lin"], info["nonzero"] = add_hints(cnf, names, t, au)
    return cnf, names, info


def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


def instance_name(t, typ, ri, ci):
    return f"c_t{t}_{typ}_r{ri}_c{ci:03d}"


def instances(t):
    """(specs in round-robin order, summary) at rank t - 3."""
    cls = classify(t)
    sps, summary = [], {"r_orbits": []}
    for ri, e in enumerate(cls):
        summary["r_orbits"].append({"r": list(e["r"]), "size": e["size"], "type": e["type"],
                                    "classes": [[list(rep), len(m)] for rep, m in e["classes"]],
                                    "stats": e["stats"]})
        for ci, (rep, members) in enumerate(e["classes"]):
            sps.append({"name": instance_name(t, e["type"], ri, ci),
                        "kind": "main" if t == T else "control", "t": t, "type": e["type"],
                        "ri": ri, "ci": ci, "r": list(e["r"]), "au": list(rep),
                        "class_size": len(members), "r_size": e["size"]})
    sps.sort(key=lambda s: (s["ci"], s["ri"]))
    return sps, summary


def build(spec):
    return encode_class(spec["t"], tuple(spec["au"]))


# ---------- selfcheck ----------

def check_classes(t, cls):
    """Validity of a computed split: class sizes add up, members have kernel W and image R, every
    unit lies in its stabiliser, and class sizes divide |Stab_K(R)| = |K| / (orbit size of R)."""
    go = group_order(t)
    n = gl_order(t - K)
    ok_sum = ok_members = ok_units = ok_div = stable = True
    for e in cls:
        ok_sum = ok_sum and sum(len(m) for _, m in e["classes"]) == n
        ok_members = ok_members and all(A[:K] == (0,) * K and rref(list(A)) == e["r"]
                                        and len(e["r"]) == t - K
                                        for _, m in e["classes"] for A in m)
        ok_units = ok_units and e["stats"]["units_ok"]
        h = go // e["size"] if go % e["size"] == 0 else None
        ok_div = ok_div and h is not None and all(h % len(m) == 0 for _, m in e["classes"])
        stable = stable and e["stats"]["stable"]
    return {"sizes_add_up": ok_sum, "members": ok_members, "units_in_H": ok_units,
            "divide_H": ok_div, "stable": stable,
            "classes": sum(len(e["classes"]) for e in cls),
            "per_r": [len(e["classes"]) for e in cls]}


def exact_check(t):
    """At small t: |K| by enumeration, orbit-stabiliser for each R, and the computed classes equal
    the exact orbits of the stabiliser."""
    G = group_elements(t)
    cls = classify(t)
    ok_stab = ok_cl = True
    for e in cls:
        H = [g for g in G if keeps(g, t, e["r"])]
        ok_stab = ok_stab and len(H) * e["size"] == len(G)
        ex = group_orbits(matrices(t, e["r"]), [unit_pair(g, t) for g in H], conj)
        ok_cl = ok_cl and sorted(map(tuple, ex)) == sorted(tuple(m) for _, m in e["classes"])
    return {"group": len(G), "orbits": len(cls), "stabilisers": ok_stab, "classes_exact": ok_cl,
            "classes": sum(len(e["classes"]) for e in cls),
            "w_classes": [len(e["classes"]) for e in cls if e["type"] == "W"]}


def hint_info(t, e):
    rep = e["classes"][0][0]
    cnf, _, info = encode_class(t, rep)
    base = len(csh.encode_shape(t, K, "c")[0].clauses)
    return {"lin": info["lin"], "nonzero": info["nonzero"], "units": info["start"] - base,
            "consistent": units_consistent(cnf), "cnf_vars": cnf.nv, "cnf_clauses": len(cnf.clauses)}


def type_sizes(orbs, t):
    out = {}
    for r, size in orbs:
        typ = r_type(t, r)
        out[str(typ)] = out.get(str(typ), 0) + size
    return out, len({str(r_type(t, r)) for r, _ in orbs}) == len(orbs)


def selfcheck():
    st = {"case_b": cb.selfcheck(random.Random(61))["graded"],
          "case_b_shapes": csh.selfcheck()["graded"], "group_order": {}, "gens_in_group": {},
          "r_orbits": {}, "exact": {}, "split": {}, "hints": {}}
    for t in SMALL + (T,):
        st["group_order"][str(t)] = group_order(t)
        st["gens_in_group"][str(t)] = all(in_group(g, t) for g in generators(t))
        orbs = r_orbits(t)
        sizes, distinct = type_sizes(orbs, t)
        st["r_orbits"][str(t)] = {"by_type": sizes, "types_distinct": distinct,
                                  "total": sum(s for _, s in orbs),
                                  "candidates": len(candidates(t)),
                                  "divide": all(group_order(t) % s == 0 for _, s in orbs)}
    for t in SMALL:
        st["exact"][str(t)] = exact_check(t)
        st["hints"][str(t)] = hint_info(t, classify(t)[0])
    cls = classify(T)
    info = check_classes(T, cls)
    info["reps_rank_4"] = all(len(rref(list(rep))) == 4 for e in cls for rep, _ in e["classes"])
    info["types"] = [e["type"] for e in cls]
    info["w_classes"] = [len(e["classes"]) for e in cls if e["type"] == "W"]
    st["split"] = info
    st["hints"][str(T)] = hint_info(T, cls[0])
    ro, ex, sp, hi = st["r_orbits"], st["exact"], st["split"], st["hints"]
    st["graded"] = {
        "case_b": all(st["case_b"].values()),
        "case_b_shapes": all(st["case_b_shapes"].values()),
        "group_order": all(st["group_order"][str(t)] == n for t, n in HAND_K.items())
        and all(ex[str(t)]["group"] == HAND_K[t] for t in SMALL),
        "gens_in_group": all(st["gens_in_group"].values()),
        "r_totals": all(ro[str(t)]["total"] == ro[str(t)]["candidates"] == HAND_R[t]
                        and ro[str(t)]["divide"] for t in HAND_R),
        "exact": all(v["stabilisers"] and v["classes_exact"] for v in ex.values()),
        "classes_valid": sp["sizes_add_up"] and sp["members"] and sp["units_in_H"]
        and sp["divide_H"],
        "t7_reps": sp["reps_rank_4"],
        "hints": all(hi[str(t)]["lin"] == HAND_LIN[t] and hi[str(t)]["nonzero"] == NONZERO
                     and hi[str(t)]["units"] == AU_UNITS[t] and hi[str(t)]["consistent"]
                     for t in HAND_LIN),
        "hand_r_orbits": all(ro[str(t)]["by_type"] == HAND_R_ORBITS[t]
                             and ro[str(t)]["types_distinct"] for t in HAND_R_ORBITS),
        "hand_w_classes": ex["6"]["w_classes"] == [HAND_W_CLASSES[6]]
        and sp["w_classes"] == [HAND_W_CLASSES[7]]}
    return st


# ---------- solving ----------

def child(spec, solver, path):
    from pysat.solvers import Solver
    cnf, names, _ = build(spec)
    start = time.time()
    used = None
    for name in (sa.SOLVERS if solver == "auto" else (solver,)):
        try:
            s = Solver(name=name, bootstrap_with=cnf.clauses)
            used = name
            break
        except Exception:
            continue
    if used is None:
        raise RuntimeError("no SAT solver available")
    ok = s.solve()
    res = {"status": "SAT" if ok else "UNSAT", "solver": used, "vars": cnf.nv,
           "clauses": len(cnf.clauses), "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, spec["t"], spec["t"] + K - 1)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def write(res, out_dir):
    with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
        json.dump(res, f, indent=1)


def solve_one(spec, solver, budget_seconds, out_dir):
    path = os.path.join(out_dir, spec["name"] + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update(spec)
    res.update({"wall_seconds": round(time.time() - start, 2),
                "budget_seconds": round(budget_seconds, 1)})
    if res["status"] == "SAT":
        t = spec["t"]
        d = t + K - 1
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and csh.in_shape(As, ss, B, t, K, "c")
                           and tuple(cols_of(As[0], t)) == tuple(spec["au"]))
        res["facts"] = csh.model_facts(As, ss, B, t, K, "c")
        res["rank_u"] = sa.rank_f2(sa.rows_of(at[1], t))
    write(res, out_dir)
    print(f"solve {spec['name']}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def run_group(sps, solver, group_seconds, cap_seconds, out_dir, start):
    """The instances in order, each with an equal share of what is left (at least MIN_BUDGET
    seconds, at most cap_seconds); once the group budget is used up the rest are SKIPPED."""
    counts = {}
    for k, sp in enumerate(sps):
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(sp, status="SKIPPED")
            write(res, out_dir)
        else:
            budget = min(cap_seconds, max(min(MIN_BUDGET, left), left / (len(sps) - k)))
            res = solve_one(sp, solver, budget, out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


def run_controls(solver, group_seconds, out_dir):
    start = time.time()
    counts = {}
    res = cb.solve(2, 1, solver, 120, out_dir)
    counts["cb_t2_k1_" + res["status"]] = 1
    sps = []
    for t in SMALL:
        s, summary = instances(t)
        with open(os.path.join(out_dir, f"classes_t{t}.json"), "w") as f:
            json.dump(summary, f, indent=1)
        sps += s
    out = run_group(sps, solver, group_seconds - (time.time() - start), 60, out_dir, time.time())
    for key, v in out.items():
        counts["controls_" + key] = v
    print(f"SUMMARY controls instances {len(sps)} {json.dumps(counts, sort_keys=True)}", flush=True)
    return counts


def run_solve(part_index, parts, solver, group_seconds, cap_seconds, out_dir):
    start = time.time()
    sps, summary = instances(T)
    with open(os.path.join(out_dir, "classes_t7.json"), "w") as f:
        json.dump(summary, f, indent=1)
    mine = sps[part_index::parts]
    print(f"classified: {len(summary['r_orbits'])} orbits of R, {len(sps)} classes, "
          f"{len(mine)} in part {part_index} of {parts}, {round(time.time() - start, 1)} s",
          flush=True)
    out = run_group(mine, solver, group_seconds, cap_seconds, out_dir, start)
    print(f"SUMMARY solve part {part_index}/{parts} instances {len(mine)} of {len(sps)} "
          f"{json.dumps(out, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m44/predictions.md) ----------

def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["selfcheck_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if (fn.startswith("c_t") or fn.startswith("cb_")) and fn.endswith(".json") \
                and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    main = {"counts": {}, "undecided": [], "times": {}}
    for name, r in results.items():
        st = r.get("status")
        if name.startswith("cb_"):
            if st in ("SAT", "UNSAT"):
                graded[name] = st == "SAT" and bool(r.get("verified"))
            else:
                ungraded[name] = st
        elif r["kind"] == "control":
            if st in ("SAT", "UNSAT"):
                graded[name] = st == "UNSAT"
            else:
                ungraded[name] = st
        else:
            main["counts"][st] = main["counts"].get(st, 0) + 1
            main["times"][name] = r.get("wall_seconds")
            if st != "UNSAT":
                main["undecided"].append(name)
            if st == "SAT":
                fa = r.get("facts") or {}
                graded[name + "_verified"] = bool(r.get("verified"))
                graded[name + "_ranks"] = (fa.get("max_rank", 99) <= 4 and r.get("rank_u") == 4
                                           and fa.get("dim_X1_cap_R", 0) >= 2)
    return {"graded": graded, "ungraded": ungraded, "main": main,
            "any_sat_7": any(r.get("status") == "SAT" for r in results.values()
                             if r.get("kind") == "main")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--part-index", type=int, default=0)
    ap.add_argument("--parts", type=int, default=1)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--group-minutes", type=float, default=140.0)
    ap.add_argument("--cap-minutes", type=float, default=25.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="{}")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.solver, args.group_minutes * 60, args.out_dir)
    elif args.part == "solve":
        run_solve(args.part_index, args.parts, args.solver, args.group_minutes * 60,
                  args.cap_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} main {out['main']['counts']}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
