# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m43: shape (d2) of Case B at rank 4 for t = 7 and dim V = 9 (notes/a28.md, Lemma 84), split
by the image R of A_u and then by the matrix A_u itself.

Setting and encoding as in case_b.py and case_b_shapes.py. The forms d2c0 and d2c1 of Lemma 37
(notes/case-b-shapes.md) at (t, k) = (7, 3) fix

    x0 = sigma(u) = e_0,  P = phi(V) = span(e_1, ..., e_6),  A_u kills W = span(e_0, e_1, e_2),
    sigma(v_1) = e_1,  sigma(v_2) = beta(v_1, v_2) = delta  (e_2 in d2c0, e_0 + e_2 in d2c1),
    A_(v_1): e_0, e_1 -> 0, e_2 -> delta;  A_(v_2) kills e_0, e_1, e_2;  phi(v_(2+j)) = e_j.

Job m40a left both forms UNKNOWN after 45 minutes each, with A_u free apart from its kernel. Every
base change in

    K = {g in GL(X) : g e_0 = e_0, g e_1 = e_1, g e_2 = e_2, g P = P}

keeps the form (the basis vectors v_(2+j) are chosen again over g e_j), so R = Im A_u can be taken to
be a representative of its K-orbit, and then A_u a representative of its class under the stabiliser
of R in K. By Lemma 78 (notes/a24.md), delta lies in R. Lemma 84 counts the K-orbits of R by hand:
7 for d2c0 and 5 for d2c1.

How the split is computed. The orbits of R (dimension 4, containing delta) are closures under the
elementary transvections in K, which generate it, so they are exact. For each representative R, the
classes of A_u (the 20160 matrices with kernel W and image R) are closures under conjugation by
NGENS random units of the algebra {g : g e_i in span(e_i) for i < 3, g P <= P, g R <= R}, whose units
are exactly the stabiliser of R in K. Every unit is checked to lie in it, so every computed class lies
inside one true class, and the split is complete whether or not the units generate the stabiliser;
missing generators could only give more instances. At t = 4, 5 and 6 (A_u of rank t - 3) the whole
of K is enumerated and the computed classes must equal the exact ones.

Each instance is the CNF of case_b_shapes.encode_shape(7, 3, form) with the columns of A_u on
e_3, ..., e_6 fixed by 28 unit clauses, and these facts as conditions: for n = v_1, v_2 in ker phi,
Im A_n lies in R ((2) and (3) of a10.md: A_n maps P into R and kills x0); beta(v_2, v_j) lies in R
for j >= 3, and A_(v_2) has rank exactly 1 (Lemma 78). The first two are 60 linear conditions; rank 1
is written as A_(v_2) e_c = lambda_c y for c >= 3, plus one clause asking for a non-zero column.

Controls: case_b's (t, k) = (2, 1) example must be SAT; every class at t = 4, 5, 6 (dim V = t + 2)
must be UNSAT, since A(t) = t there. Lemma 78 is not proved there, but extra conditions cannot turn
UNSAT into SAT. There is no positive control in a d2 form: a satisfiable instance at any t <= 6 would
contradict A(t) = t.

Matrices are kept as tuples of columns (column c = image of e_c, a bit mask). sat_aniso.py uses
t^2-bit masks with entry (r, c) at bit t r + c.

Parts: selfcheck (pure Python), controls, solve --form d2c0|d2c1 [--half k --halves n], grade.

Usage: python m43.py --part selfcheck|controls|solve|grade [--form d2c0] [--half 0] [--halves 2]
                     [--group-minutes 140] [--cap-minutes 10] [--out-dir DIR]
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
D = T + K - 1
FORMS = {"d2c0": 4, "d2c1": 5}
NGENS = 24
MIN_BUDGET = 20.0
SMALL = (4, 5, 6)
# Hand counts (notes/a28.md, Lemma 84), for A_u of rank t - 3.
HAND_K = {4: 4, 5: 96, 6: 10752, 7: 5160960}
HAND_R = {4: 1, 5: 15, 6: 155, 7: 1395}
HAND_R_ORBITS = {(4, "d2c0"): [1], (4, "d2c1"): [1],
                 (5, "d2c0"): [1, 1, 1, 6, 6], (5, "d2c1"): [1, 1, 1, 12],
                 (6, "d2c0"): [1, 7, 7, 14, 14, 28, 84], (6, "d2c1"): [1, 14, 14, 14, 112],
                 (7, "d2c0"): [15, 35, 105, 120, 140, 140, 840],
                 (7, "d2c1"): [15, 140, 140, 140, 960]}
HAND_HINTS = {4: 33, 5: 42, 6: 51, 7: 60}       # 6 t + 3 (t - 1)
AU_UNITS = {4: 4, 5: 10, 6: 18, 7: 28}          # t (t - 3)


# ---------- vectors, subspaces, matrices (as in m42.py) ----------

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


def subspaces(t, k, containing=0):
    """Every k-dimensional subspace of F_2^t (as rref tuples) that contains the vector containing,
    enumerated directly as reduced echelon forms."""
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
            rows = tuple(rows)
            if not containing or in_span(rows, containing):
                out.append(rows)
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


# ---------- the group K and stabilisers ----------

def group_order(t):
    """|K|: the g_P in GL(P) that fix e_1 and e_2, so prod over 2 <= i <= t - 2 of 2^(t-1) - 2^i."""
    out = 1
    for i in range(2, t - 1):
        out *= (1 << (t - 1)) - (1 << i)
    return out


def generators(t):
    """The elementary transvections g e_j = e_j + e_i (other e_c fixed) with 3 <= j < t and
    1 <= i < t, i != j: they lie in K and generate it."""
    gens = []
    for j in range(K, t):
        for i in range(1, t):
            if i != j:
                gens.append(identity(t) ^ (1 << (t * i + j)))
    return gens


def keeps(g, t, rows):
    return image_cols(cols_of(g, t), rows) == tuple(rows)


def in_group(g, t, extra=()):
    return (sa.rank_f2(sa.rows_of(g, t)) == t and all(sa.mat_apply(g, x, t) == x for x in (1, 2, 4))
            and keeps(g, t, p_basis(t - 1)) and all(keeps(g, t, s) for s in extra))


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


def random_units(t, subs, count, seed):
    """count uniform random units of the stabiliser algebra of subs (seeded); with the lines
    span(e_0), span(e_1), span(e_2) among subs, each fixes e_0, e_1 and e_2."""
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

def r_orbits(t, form):
    """[(rep, size)] for the K-orbits of the subspaces R of dimension t - 3 that contain delta, exact
    (closure under generators of K), ordered by least element."""
    rs = subspaces(t, t - K, FORMS[form])
    orbs = orbits_under(rs, [cols_of(g, t) for g in generators(t)], image_cols)
    return [(o[0], len(o)) for o in orbs]


def matrices(t, r):
    """Every A with kernel exactly W and image exactly r, as column tuples: |GL_(t-3)| of them."""
    rvals = [sa.combine(list(r), c) for c in range(1, 1 << len(r))]
    out = []
    for ys in itertools.product(rvals, repeat=len(r)):
        if sa.rank_f2(list(ys)) == len(r):
            out.append((0,) * K + ys)
    return sorted(out)


def class_seed(t, form, ri):
    return 93000 + 1000 * t + 7907 * ri + (0 if form == "d2c0" else 500)


def r_classes(t, form, ri, r):
    """[(rep, members)] for the closures of matrices(t, r) under conjugation by NGENS random units of
    the stabiliser of r in K, with stats."""
    units, st = random_units(t, [(1,), (2,), (4,), p_basis(t - 1), r], NGENS,
                             class_seed(t, form, ri))
    pairs = [unit_pair(g, t) for g in units]
    mats = matrices(t, r)
    cl = orbits_under(mats, pairs, conj)
    half = orbits_under(mats, pairs[:NGENS // 2], conj)
    st.update({"units": len(units), "units_ok": all(in_group(g, t, (r,)) for g in units),
               "stable": len(half) == len(cl), "matrices": len(mats)})
    return [(c[0], c) for c in cl], st


def classify(t, form):
    out = []
    for ri, (r, size) in enumerate(r_orbits(t, form)):
        cl, st = r_classes(t, form, ri, r)
        out.append({"r": r, "size": size, "classes": cl, "stats": st})
    return out


def invariants(t, r):
    return {"dim_R_W": dim_meet(r, w_basis()), "dim_R_Y": dim_meet(r, rref([2, 4])),
            "e0_in_R": in_span(r, 1), "R_in_P": dim_meet(r, p_basis(t - 1)) == len(r)}


# ---------- the encoding ----------

def encode_class(t, form, au, r, hints=True):
    """(cnf, names, number of linear conditions): encode_shape(t, 3, form) with A_u fixed on
    e_3, ..., e_(t-1); with hints, Im A_(v_1) and Im A_(v_2) in r, beta(v_2, v_j) in r for j >= 3,
    and A_(v_2) of rank exactly 1."""
    cnf, names = csh.encode_shape(t, K, form)
    A, B = names[0], names[2]
    d = t + K - 1
    for c in range(K, t):
        for row in range(t):
            cnf.clauses.append([A[0][row][c]] if (au[c] >> row) & 1 else [-A[0][row][c]])
    if not hints:
        return cnf, names, 0
    ann_r = ann(r, t)
    n = 0
    for i in (1, 2):
        for c in range(t):
            for f in ann_r:
                cnf.xor_eq([A[i][row][c] for row in range(t) if (f >> row) & 1], 0)
                n += 1
    for j in range(K, d):
        for f in ann_r:
            cnf.xor_eq([B[(2, j)][row] for row in range(t) if (f >> row) & 1], 0)
            n += 1
    lam = [cnf.new() for _ in range(K, t)]
    y = [cnf.new() for _ in range(t)]
    for ci, c in enumerate(range(K, t)):
        for row in range(t):
            p = cnf.AND(lam[ci], y[row])
            a = A[2][row][c]
            cnf.clauses += [[-a, p], [a, -p]]
    cnf.clauses.append([A[2][row][c] for c in range(K, t) for row in range(t)])
    return cnf, names, n


def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


def instance_name(t, form, ri, ci):
    return f"d2_t{t}_{form}_r{ri}_c{ci:03d}"


def instances(t, form):
    """(specs in round-robin order, summary) for one form at rank t - 3."""
    cls = classify(t, form)
    sps, summary = [], {"r_orbits": []}
    for ri, e in enumerate(cls):
        summary["r_orbits"].append({"r": list(e["r"]), "size": e["size"],
                                    "invariants": invariants(t, e["r"]),
                                    "classes": [[list(rep), len(m)] for rep, m in e["classes"]],
                                    "stats": e["stats"]})
        for ci, (rep, members) in enumerate(e["classes"]):
            sps.append({"name": instance_name(t, form, ri, ci),
                        "kind": "main" if t == T else "control", "t": t, "form": form, "ri": ri,
                        "ci": ci, "r": list(e["r"]), "au": list(rep), "class_size": len(members),
                        "r_size": e["size"]})
    sps.sort(key=lambda s: (s["ci"], s["ri"]))
    return sps, summary


def build(spec):
    return encode_class(spec["t"], spec["form"], tuple(spec["au"]), tuple(spec["r"]))


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


def exact_check(t, form):
    """At small t: |K| by enumeration, orbit-stabiliser for each R, and the computed classes equal
    the exact orbits of the stabiliser."""
    G = group_elements(t)
    cls = classify(t, form)
    ok_stab = ok_cl = True
    for e in cls:
        H = [g for g in G if keeps(g, t, e["r"])]
        ok_stab = ok_stab and len(H) * e["size"] == len(G)
        ex = orbits_under(matrices(t, e["r"]), [unit_pair(g, t) for g in H], conj)
        ok_cl = ok_cl and sorted(map(tuple, ex)) == sorted(tuple(m) for _, m in e["classes"])
    return {"group": len(G), "orbits": len(cls), "stabilisers": ok_stab, "classes_exact": ok_cl,
            "classes": sum(len(e["classes"]) for e in cls)}


def hint_info(t, form, e):
    rep = e["classes"][0][0]
    cnf, _, n = encode_class(t, form, rep, e["r"])
    base = len(csh.encode_shape(t, K, form)[0].clauses)
    cnf_u = encode_class(t, form, rep, e["r"], hints=False)[0]
    return {"hints": n, "units": len(cnf_u.clauses) - base, "consistent": units_consistent(cnf),
            "cnf_vars": cnf.nv, "cnf_clauses": len(cnf.clauses)}


def selfcheck():
    st = {"case_b": cb.selfcheck(random.Random(61))["graded"],
          "case_b_shapes": csh.selfcheck()["graded"], "group_order": {}, "gens_in_group": {},
          "r_orbits": {}, "exact": {}, "split": {}, "hints": {}}
    for t in SMALL + (T,):
        st["group_order"][str(t)] = group_order(t)
        st["gens_in_group"][str(t)] = all(in_group(g, t) for g in generators(t))
        for form in FORMS:
            orbs = r_orbits(t, form)
            st["r_orbits"][f"t{t}_{form}"] = {"sizes": sorted(s for _, s in orbs),
                                              "total": sum(s for _, s in orbs),
                                              "divide": all(group_order(t) % s == 0
                                                            for _, s in orbs)}
    for t in SMALL:
        for form in FORMS:
            st["exact"][f"t{t}_{form}"] = exact_check(t, form)
        st["hints"][f"t{t}"] = hint_info(t, "d2c0", classify(t, "d2c0")[0])
    for form in FORMS:
        cls = classify(T, form)
        info = check_classes(T, cls)
        info["reps_rank_4"] = all(len(rref(list(rep))) == 4 for e in cls for rep, _ in e["classes"])
        info["invariants"] = [invariants(T, e["r"]) for e in cls]
        st["split"][form] = info
        st["hints"][form] = hint_info(T, form, cls[0])
    ro, ex, sp, hi = st["r_orbits"], st["exact"], st["split"], st["hints"]
    st["graded"] = {
        "case_b": all(st["case_b"].values()),
        "case_b_shapes": all(st["case_b_shapes"].values()),
        "group_order": all(st["group_order"][str(t)] == n for t, n in HAND_K.items())
        and all(ex[f"t{t}_{f}"]["group"] == HAND_K[t] for t in SMALL for f in FORMS),
        "gens_in_group": all(st["gens_in_group"].values()),
        "r_totals": all(ro[f"t{t}_{f}"]["total"] == HAND_R[t] and ro[f"t{t}_{f}"]["divide"]
                        for t in HAND_R for f in FORMS),
        "exact": all(v["stabilisers"] and v["classes_exact"] for v in ex.values()),
        "classes_valid": all(v["sizes_add_up"] and v["members"] and v["units_in_H"]
                             and v["divide_H"] for v in sp.values()),
        "t7_reps": all(v["reps_rank_4"] for v in sp.values()),
        "hints": all(hi[f"t{t}"]["hints"] == HAND_HINTS[t] and hi[f"t{t}"]["units"] == AU_UNITS[t]
                     and hi[f"t{t}"]["consistent"] for t in SMALL)
        and all(hi[f]["hints"] == HAND_HINTS[T] and hi[f]["units"] == AU_UNITS[T]
                and hi[f]["consistent"] for f in FORMS),
        "hand_r_orbits": all(ro[f"t{t}_{f}"]["sizes"] == HAND_R_ORBITS[(t, f)]
                             for t, f in HAND_R_ORBITS)}
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
                           and csh.in_shape(As, ss, B, t, K, spec["form"])
                           and tuple(cols_of(As[0], t)) == tuple(spec["au"]))
        res["max_rank"] = max(sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d))
        res["rank_u"] = sa.rank_f2(sa.rows_of(at[1], t))
        res["rank_v2"] = sa.rank_f2(sa.rows_of(at[4], t))
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
        for form in FORMS:
            s, summary = instances(t, form)
            with open(os.path.join(out_dir, f"classes_t{t}_{form}.json"), "w") as f:
                json.dump(summary, f, indent=1)
            sps += s
    out = run_group(sps, solver, group_seconds - (time.time() - start), 60, out_dir, time.time())
    for key, v in out.items():
        counts["controls_" + key] = v
    print(f"SUMMARY controls instances {len(sps)} {json.dumps(counts, sort_keys=True)}", flush=True)
    return counts


def run_solve(form, half, halves, solver, group_seconds, cap_seconds, out_dir):
    start = time.time()
    sps, summary = instances(T, form)
    with open(os.path.join(out_dir, f"classes_t7_{form}.json"), "w") as f:
        json.dump(summary, f, indent=1)
    mine = sps[half::halves]
    print(f"classified {form}: {len(summary['r_orbits'])} orbits of R, {len(sps)} classes, "
          f"{len(mine)} in this half, {round(time.time() - start, 1)} s", flush=True)
    out = run_group(mine, solver, group_seconds, cap_seconds, out_dir, start)
    print(f"SUMMARY solve {form} half {half}/{halves} instances {len(mine)} of {len(sps)} "
          f"{json.dumps(out, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m43/predictions.md) ----------

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
        if (fn.startswith("d2_") or fn.startswith("cb_")) and fn.endswith(".json") \
                and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    per_form = {}
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
            ps = per_form.setdefault(r["form"], {"counts": {}, "undecided": [], "times": {}})
            ps["counts"][st] = ps["counts"].get(st, 0) + 1
            ps["times"][name] = r.get("wall_seconds")
            if st != "UNSAT":
                ps["undecided"].append(name)
            if st == "SAT":
                graded[name + "_verified"] = bool(r.get("verified"))
                graded[name + "_ranks"] = (r.get("max_rank", 99) <= 4 and r.get("rank_u") == 4
                                           and r.get("rank_v2") == 1)
    return {"graded": graded, "ungraded": ungraded, "per_form": per_form,
            "any_sat_7": any(r.get("status") == "SAT" for r in results.values()
                             if r.get("kind") == "main")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--form", choices=sorted(FORMS), default="d2c0")
    ap.add_argument("--half", type=int, default=0)
    ap.add_argument("--halves", type=int, default=1)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--group-minutes", type=float, default=140.0)
    ap.add_argument("--cap-minutes", type=float, default=10.0)
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
        run_solve(args.form, args.half, args.halves, args.solver, args.group_minutes * 60,
                  args.cap_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} "
              + " ".join(f"{k} {v['counts']}" for k, v in sorted(out["per_form"].items())),
              flush=True)
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
