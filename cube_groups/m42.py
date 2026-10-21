# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m42: the rank-3 configurations (B6) and (B5) for t = 7 and dim V = 9 (notes/a27.md,
Lemma 83), split by the pair (ker A_u, Im A_u) and then by the matrix A_u itself.

Setting and encoding as in sat_aniso.py. By Proposition 29(c) (notes/a24.md), if an anisotropic
system with t = 7 and dim V = 9 has no element of rank 4, each element u of rank 3 is in (A5)
(job m41), (B6) or (B5). In shape ("B", p), x0 = sigma(u) is not in P = phi(V), dim P = p and
ker phi has dimension kd = 9 - p: (B6) is p = 6, (B5) is p = 5. The normal form is

    sigma(u) = e_0,  P = span(e_1, ..., e_p),  v_0 = u,  phi(v_i) = 0 for 0 < i < kd,
    phi(v_(kd - 1 + j)) = e_j for 1 <= j <= p,

and it is kept by G = {g in GL(X) : g e_0 = e_0, g P = P}. As in Lemma 70 (notes/a17.md), every
system with u in shape ("B", p) is conjugate by G to one in which the pair (X_1, R) =
(ker A_u, Im A_u) is a chosen representative of its G-orbit, and then, by the stabiliser H of the
pair, to one in which A_u is a chosen representative of its class.

How the split is computed. The G-orbits of X_1 (dimension 4, containing e_0) are closures under the
elementary transvections that lie in G (they generate G). For each orbit representative X_1, the
orbits of R (dimension 3) are closures under 64 random elements of the stabiliser of (e_0, P, X_1):
the invertible elements of the algebra {g : g span(e_0) <= span(e_0), g P <= P, g X_1 <= X_1},
drawn uniformly (seeded). The classes of A_u (the 168 matrices with kernel exactly X_1 and image
exactly R) are closures under conjugation by 64 random elements of H, the units of the algebra that
also keeps R. Every generator is checked to lie in its group, so each computed orbit or class lies
inside one true orbit, and the split is complete whether or not the generators generate the group;
missing generators could only give more instances.

Each instance is the CNF of sat_aniso.encode (no echelon form) with sigma(u), A_u and phi fixed by
unit clauses (encode_fixed, as in m41.py) and the hints of Proposition 29(c), (2) and (3) of a10.md
for the elements of ker phi: A_n x0 = 0, A_n maps P + span(x0) into R, sigma(n) lies in X_1, and
beta(n, n') lies in X_1.

Controls: at t = 2, 4 and 6 the same classification is compared with exact orbits (t = 2, 4) and with
the counts of jobs m27 and m30 (t = 6); the instances at t = 2 (SAT exactly for R = span(e_1), as in
job m30) and t = 4 (dim V = 5, all UNSAT as A(4) = 4) are solved; and the planted system at t = 6
(three copies of Lemma 63 (ii), as in m32.py and m41.py), with its hints, must be SAT.

Matrices are t^2-bit masks with entry (r, c) at bit t r + c, as in sat_aniso.py.

Parts: selfcheck (pure Python), controls, solve --shape B6|B5 [--half k --halves n], grade.

Usage: python m42.py --part selfcheck|controls|solve|grade [--shape B6] [--half 0] [--halves 2]
                     [--group-minutes 140] [--cap-minutes 8] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

import sat_aniso as sa

T = 7
D = 9
RHO = 3
SHAPES = {"B6": 6, "B5": 5}
NGENS = 64
MIN_BUDGET = 20.0
# Hand counts (notes/a27.md, Lemma 83; t = 4 and t = 6 from jobs m27 and m30).
HAND_SUBSPACES = {(7, 4, 1): 1395, (7, 3, 0): 11811, (6, 3, 1): 155, (6, 3, 0): 1395,
                  (4, 2, 1): 7, (4, 2, 0): 35, (2, 1, 1): 1, (2, 1, 0): 3}
HAND_GROUP = {(7, 6): 20158709760, (7, 5): 639959040, (6, 5): 9999360, (6, 4): 645120,
              (4, 3): 168, (4, 2): 48, (2, 1): 1}
HAND_PAIRS = {(7, 6): 13, (7, 5): 49, (6, 5): 11, (6, 4): 39, (4, 3): 7, (4, 2): 19, (2, 1): 3}
HAND_PAIRS_BY_X = {(7, 6): {1395: 13}, (7, 5): {155: 20, 1240: 29}, (6, 5): {155: 11},
                   (6, 4): {35: 18, 120: 21}}
HAND_T4_B3_SIZES = [7, 21, 21, 28, 42, 42, 84]
M30_CLASSES = {(6, 5): 66, (6, 4): 401}
HAND_HINTS = {"B6": 79, "B5": 111, "t4_B3": 14, "t4_B2": 26, "t2_B1": 0, "planted": 45}
MAIN_UNITS = T + T * T + (D - 1) * T                       # 112
SMALL = ((2, 1, 1, 2), (4, 3, 2, 5), (4, 2, 2, 5))       # (t, p, rho, d): exact checks, controls
MID = ((6, 5, 3), (6, 4, 3))


# ---------- vectors, subspaces, matrices ----------

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


def kernel(A, t):
    return rref(sa.nullspace(sa.rows_of(A, t), t))


def column_space(A, t):
    return rref(cols_of(A, t))


def ann(rows, t):
    """Basis of {f : f . s = 0 for every s in rows}."""
    return sa.nullspace(list(rows), t)


def p_basis(p):
    return rref([1 << j for j in range(1, p + 1)])


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


# ---------- the group G and stabilisers ----------

def group_order(t, p):
    """|G| for shape ("B", p): block triangular with diagonal blocks (1, GL_p, GL_(t-p-1))."""
    return 2 ** ((p + 1) * (t - p - 1)) * gl_order(p) * gl_order(t - p - 1)


def generators(t, p):
    """The elementary transvections g e_j = e_j + e_i (other e_c fixed) that lie in G."""
    inP = set(range(1, p + 1))
    gens = []
    for j in range(1, t):
        for i in range(t):
            if i == j or (j in inP and i not in inP):
                continue
            gens.append(identity(t) ^ (1 << (t * i + j)))
    return gens


def keeps(g, t, rows):
    return image_cols(cols_of(g, t), rows) == tuple(rows)


def in_group(g, t, p, extra=()):
    return (sa.rank_f2(sa.rows_of(g, t)) == t and sa.mat_apply(g, 1, t) == 1
            and keeps(g, t, p_basis(p)) and all(keeps(g, t, s) for s in extra))


def group_elements(t, p):
    """Every element of G, by closure (only for small t)."""
    gens = generators(t, p)
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


# ---------- pair orbits and classes ----------

def pair_orbits(t, p, rho):
    """[pair dicts] for the G-orbits of (X_1 containing e_0, dim t - rho; R, dim rho), ordered by
    the orbit of X_1 and then by the least R."""
    pb = p_basis(p)
    xs = subspaces(t, t - rho, 1)
    rs = subspaces(t, rho)
    gens = generators(t, p)
    xorbs = orbits_under(xs, [cols_of(g, t) for g in gens], image_cols)
    out, stats = [], {"x_orbits": [len(o) for o in xorbs], "units": [], "units_ok": True}
    for xi, xorb in enumerate(xorbs):
        x1 = xorb[0]
        units, ust = random_units(t, [(1,), pb, x1], NGENS, 42000 + 100 * t + p + 7919 * xi)
        stats["units"].append(ust)
        stats["units_ok"] = stats["units_ok"] and len(units) == NGENS and all(
            in_group(g, t, p, (x1,)) for g in units)
        for rorb in orbits_under(rs, [cols_of(g, t) for g in units], image_cols):
            out.append({"x1": x1, "r": rorb[0], "size": len(xorb) * len(rorb), "x_orbit": xi,
                        "x_orbit_size": len(xorb)})
    return out, stats


def matrices(t, x1, r):
    """Every A with kernel exactly x1 and image exactly r: |GL_rho| of them."""
    comp = []
    for f in range(t):
        if len(rref(list(x1) + comp + [1 << f])) > len(x1) + len(comp):
            comp.append(1 << f)
    binv = sa.mat_inv(sa.from_cols(list(x1) + comp, t), t)
    rvals = [sa.combine(list(r), c) for c in range(1, 1 << len(r))]
    out = []
    for ys in itertools.product(rvals, repeat=len(r)):
        if sa.rank_f2(list(ys)) == len(r):
            out.append(sa.mat_mul(sa.from_cols([0] * len(x1) + list(ys), t), binv, t))
    return sorted(out)


def conj(gi, A, t):
    g, ginv = gi
    return sa.mat_mul(sa.mat_mul(g, A, t), ginv, t)


def pair_classes(t, p, x1, r, seed):
    """[(rep, members)] for the closures of matrices(t, x1, r) under conjugation by NGENS random
    units of the stabiliser H of (e_0, P, X_1, R), with stats."""
    units, st = random_units(t, [(1,), p_basis(p), x1, r], NGENS, seed)
    pairs = [(g, sa.mat_inv(g, t)) for g in units]
    mats = matrices(t, x1, r)
    cl = orbits_under(mats, pairs, lambda gi, A: conj(gi, A, t))
    half = orbits_under(mats, pairs[:NGENS // 2], lambda gi, A: conj(gi, A, t))
    st.update({"units": len(units), "units_ok": all(in_group(g, t, p, (x1, r)) for g in units),
               "stable": len(half) == len(cl), "matrices": len(mats)})
    return [(c[0], c) for c in cl], st


def class_seed(t, p, pi):
    return 91000 + 1000 * t + 10 * p + 7907 * pi


def invariants(t, p, x1, r):
    pb = p_basis(p)
    h0 = rref(list(pb) + [1])
    return {"d": dim_meet(x1, r), "x0_in_R": in_span(r, 1), "dim_R_P": dim_meet(r, pb),
            "dim_X1_P": dim_meet(x1, pb), "R_in_H0": dim_meet(r, h0) == len(r),
            "X1_in_H0": dim_meet(x1, h0) == len(x1)}


def classify(t, p, rho):
    """(pairs, per-pair class lists, stats) for shape ("B", p)."""
    pairs, pst = pair_orbits(t, p, rho)
    cls = []
    for pi, pr in enumerate(pairs):
        cl, st = pair_classes(t, p, pr["x1"], pr["r"], class_seed(t, p, pi))
        cls.append((cl, st))
    return pairs, cls, pst


# ---------- the encoding ----------

def phis_for(d, p):
    kd = d - p
    return (None,) + (0,) * (kd - 1) + tuple(1 << j for j in range(1, p + 1))


def encode_fixed(t, d, au, s0, phis):
    """sat_aniso.encode (no echelon form) with A_0 = au, s_0 = s0 and B_0i = phis[i] fixed by unit
    clauses (as encode_fixed in m41.py, without fixed s_i)."""
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]

    def unit(var, bit):
        cnf.clauses.append([var] if bit else [-var])

    for r in range(t):
        unit(S[0][r], (s0 >> r) & 1)
        for c in range(t):
            unit(A[0][r][c], (au >> (t * r + c)) & 1)
    for i in range(1, d):
        if phis[i] is None:
            continue
        for r in range(t):
            unit(B[(0, i)][r], (phis[i] >> r) & 1)
    return cnf, names


def add_hints(cnf, names, t, kd, au, s0, pvecs):
    """For n = v_i, 0 < i < kd (in ker phi): A_n x0 = 0 and sigma(n) in X_1 by (3) of a10.md; A_n
    maps P + span(x0) into R and beta(n, n') lies in X_1 by (2). Returns the number of linear
    conditions added."""
    A, S, B = names[0], names[1], names[2]
    ann_x1 = ann(kernel(au, t), t)
    ann_r = ann(column_space(au, t), t)
    ext = rref(list(pvecs) + [s0])
    n = 0
    for i in range(1, kd):
        for row in range(t):
            cnf.xor_eq([A[i][row][c] for c in range(t) if (s0 >> c) & 1], 0)
            n += 1
        for y in ext:
            for f in ann_r:
                cnf.xor_eq([A[i][row][c] for row in range(t) if (f >> row) & 1
                            for c in range(t) if (y >> c) & 1], 0)
                n += 1
        for f in ann_x1:
            cnf.xor_eq([S[i][row] for row in range(t) if (f >> row) & 1], 0)
            n += 1
    for i, j in itertools.combinations(range(1, kd), 2):
        for f in ann_x1:
            cnf.xor_eq([B[(i, j)][row] for row in range(t) if (f >> row) & 1], 0)
            n += 1
    return n


# ---------- the planted control (three copies of Lemma 63 (ii), as in m32.py and m41.py) ----------

def sigma_old(v):
    """X: E_i = bit 2i, F_i = bit 2i + 1; V: a_i = bit 2i, b_i = bit 2i + 1;
    sigma(a_i) = sigma(b_i) = E_i, sigma(a_i + b_i) = F_i, no cross terms."""
    out = 0
    for i in range(3):
        a, b = (v >> (2 * i)) & 1, (v >> (2 * i + 1)) & 1
        if a ^ b:
            out ^= 1 << (2 * i)
        elif a:
            out ^= 1 << (2 * i + 1)
    return out


def alpha_old(v):
    """A_(a_i) = A_(b_i) = the projection onto span(F_i) along the rest, A_(a_i + b_i) = 0."""
    out = 0
    for i in range(3):
        if ((v >> (2 * i)) ^ (v >> (2 * i + 1))) & 1:
            out ^= sa.entries(6, [(2 * i + 1, 2 * i + 1)])
    return out


def planted():
    """(As, ss, B) at t = 6, d = 6 in the basis h_0 = a_1 + a_2 + a_3 = u, h_1 = a_1, h_2 = a_2
    (phi = 0), h_3, h_4, h_5 = b_1, b_2, b_3, after the change of X-basis of m32.py (skew)."""
    t = 6
    nb = sa.from_cols([21, 2, 8, 32, 6, 16], t)
    c = sa.mat_inv(nb, t)
    hs = [21, 1, 4, 2, 8, 32]
    As = [sa.mat_mul(sa.mat_mul(c, alpha_old(v), t), nb, t) for v in hs]
    ss = [sa.mat_apply(c, sigma_old(v), t) for v in hs]
    B = {(i, k): sa.mat_apply(c, sigma_old(hs[i] ^ hs[k]) ^ sigma_old(hs[i]) ^ sigma_old(hs[k]), t)
         for i in range(t) for k in range(i + 1, t)}
    return As, ss, B


# ---------- instances ----------

def instance_name(t, p, pi, ci):
    return f"r3b_t{t}_B{p}_o{pi:03d}_c{ci:03d}"


def instances(t, d, p, rho):
    """(specs in round-robin order, summary) for shape ("B", p)."""
    pairs, cls, pst = classify(t, p, rho)
    sps, summary = [], {"pair_stats": pst, "pairs": []}
    for pi, (pr, (cl, st)) in enumerate(zip(pairs, cls)):
        summary["pairs"].append({"x1": list(pr["x1"]), "r": list(pr["r"]), "size": pr["size"],
                                 "x_orbit": pr["x_orbit"], "invariants": invariants(t, p, pr["x1"],
                                                                                    pr["r"]),
                                 "classes": [[rep, len(m)] for rep, m in cl], "stats": st})
        for ci, (rep, members) in enumerate(cl):
            sps.append({"name": instance_name(t, p, pi, ci), "kind": "main" if t == T else "control",
                        "t": t, "d": d, "p": p, "pair": pi, "cls": ci, "x1": list(pr["x1"]),
                        "r": list(pr["r"]), "au": rep, "class_size": len(members),
                        "pair_size": pr["size"]})
    sps.sort(key=lambda s: (s["cls"], s["pair"]))
    return sps, summary


def planted_spec():
    return {"name": "r3b_planted", "kind": "planted", "t": 6, "d": 6, "p": 3,
            "au": planted()[0][0]}


def params(spec):
    """(t, d, au, s0, phis, kd, pvecs) of an instance."""
    if spec["kind"] == "planted":
        As, ss, B = planted()
        phis = (None,) + tuple(B[(0, i)] for i in range(1, 6))
        return 6, 6, As[0], ss[0], phis, 3, [phis[i] for i in (3, 4, 5)]
    t, d, p = spec["t"], spec["d"], spec["p"]
    return t, d, spec["au"], 1, phis_for(d, p), d - p, list(p_basis(p))


def build(spec):
    t, d, au, s0, phis, kd, pvecs = params(spec)
    cnf, names = encode_fixed(t, d, au, s0, phis)
    n = add_hints(cnf, names, t, kd, au, s0, pvecs)
    return cnf, names, n


# ---------- selfcheck ----------

def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


def check_classes(t, p, rho, pairs, cls):
    """Validity of a computed split: class sizes add up, members have the right kernel and image,
    every generator lies in its group, and class sizes divide |H| = |G| / (pair orbit size)."""
    go = group_order(t, p)
    ok_sum = ok_members = ok_units = ok_div = True
    stable = True
    for pr, (cl, st) in zip(pairs, cls):
        ok_sum = ok_sum and sum(len(m) for _, m in cl) == gl_order(rho)
        ok_members = ok_members and all(kernel(A, t) == pr["x1"] and column_space(A, t) == pr["r"]
                                        for _, m in cl for A in m)
        ok_units = ok_units and st["units_ok"]
        h = go // pr["size"] if go % pr["size"] == 0 else None
        ok_div = ok_div and h is not None and all(h % len(m) == 0 for _, m in cl)
        stable = stable and st["stable"]
    return {"sizes_add_up": ok_sum, "members": ok_members, "units_in_H": ok_units,
            "divide_H": ok_div, "stable": stable,
            "classes": sum(len(cl) for cl, _ in cls)}


def exact_check(t, p, rho):
    """At small t: the computed pair orbits and classes equal the exact orbits of G and H."""
    G = group_elements(t, p)
    pairs, pst = pair_orbits(t, p, rho)
    xs, rs = subspaces(t, t - rho, 1), subspaces(t, rho)
    allp = sorted((x, r) for x in xs for r in rs)
    exact = orbits_under(allp, [cols_of(g, t) for g in generators(t, p)],
                         lambda gc, xr: (image_cols(gc, xr[0]), image_cols(gc, xr[1])))
    which = {xr: k for k, o in enumerate(exact) for xr in o}
    ks = [which[(pr["x1"], pr["r"])] for pr in pairs]
    ok_pairs = (len(set(ks)) == len(pairs) == len(exact)
                and all(len(exact[k]) == pr["size"] for k, pr in zip(ks, pairs)))
    ok_h = ok_cl = True
    cls = []
    for pi, pr in enumerate(pairs):
        H = [g for g in G if keeps(g, t, pr["x1"]) and keeps(g, t, pr["r"])]
        ok_h = ok_h and len(H) * pr["size"] == len(G)
        mats = matrices(t, pr["x1"], pr["r"])
        ex = orbits_under(mats, [(g, sa.mat_inv(g, t)) for g in H], lambda gi, A: conj(gi, A, t))
        cl, st = pair_classes(t, p, pr["x1"], pr["r"], class_seed(t, p, pi))
        cls.append((cl, st))
        ok_cl = ok_cl and sorted(map(tuple, ex)) == sorted(tuple(m) for _, m in cl)
    return {"group": len(G), "pairs": len(pairs), "sizes": sorted(pr["size"] for pr in pairs),
            "pairs_exact": ok_pairs, "H_orbit_stabiliser": ok_h, "classes_exact": ok_cl,
            "classes": sum(len(cl) for cl, _ in cls), "units_ok": pst["units_ok"]}


def selfcheck():
    st = {"subspaces": {}, "rref_canonical": True, "group_order": {}, "gens_in_group": {},
          "exact": {}, "split": {}, "hints": {}}
    for (t, k, c), n in HAND_SUBSPACES.items():
        subs = subspaces(t, k, c)
        st["subspaces"][f"{t},{k},{c}"] = len(subs)
        st["rref_canonical"] = st["rref_canonical"] and all(rref(s) == s for s in subs)
    for (t, p) in HAND_GROUP:
        st["group_order"][f"t{t}_B{p}"] = group_order(t, p)
        st["gens_in_group"][f"t{t}_B{p}"] = all(in_group(g, t, p) for g in generators(t, p))
    probes = {}
    for t, p, rho, d in SMALL:
        st["exact"][f"t{t}_B{p}"] = exact_check(t, p, rho)
        probes[(t, p)] = pair_orbits(t, p, rho)[0][0]
    for t, p, rho in MID + tuple((T, p, RHO) for p in SHAPES.values()):
        pairs, cls, pst = classify(t, p, rho)
        probes[(t, p)] = pairs[0]
        go = group_order(t, p)
        by_x = {}
        for pr in pairs:
            by_x[pr["x_orbit_size"]] = by_x.get(pr["x_orbit_size"], 0) + 1
        info = {"pairs": len(pairs), "by_x_orbit_size": {str(k): v for k, v in sorted(by_x.items())},
                "total": sum(pr["size"] for pr in pairs),
                "pairs_divide_G": all(go % pr["size"] == 0 for pr in pairs),
                "x_units_ok": pst["units_ok"]}
        info.update(check_classes(t, p, rho, pairs, cls))
        if t == T:
            info["reps_rank_3"] = all(sa.rank_f2(cols_of(rep, t)) == 3 for cl, _ in cls
                                      for rep, _ in cl)
        st["split"][f"t{t}_B{p}"] = info
    # Hint counts and the unit clauses of one instance per shape.
    for key, (t, p, d) in {"B6": (7, 6, 9), "B5": (7, 5, 9), "t4_B3": (4, 3, 5),
                           "t4_B2": (4, 2, 5), "t2_B1": (2, 1, 2)}.items():
        pr = probes[(t, p)]
        au = matrices(t, pr["x1"], pr["r"])[0]
        spec = {"name": "probe", "kind": "main", "t": t, "d": d, "p": p, "au": au}
        cnf, names, n = build(spec)
        base = len(sa.encode(t, d, echelon=False)[0].clauses)
        st["hints"][key] = {"hints": n, "consistent": units_consistent(cnf)}
        if t == T:
            cnf2, _ = encode_fixed(t, d, au, 1, phis_for(d, p))
            st["hints"][key]["units"] = len(cnf2.clauses) - base
            st["hints"][key]["cnf_vars"] = cnf.nv
            st["hints"][key]["cnf_clauses"] = len(cnf.clauses)
    As, ss, B = planted()
    at, sv = sa.tables(As, ss, B, 6)
    pc, pn, n = build(planted_spec())
    st["hints"]["planted"] = {"hints": n, "consistent": units_consistent(pc)}
    st["planted"] = {"system": sa.is_system(at, sv, 6, 6), "anisotropic": sa.anisotropic(sv),
                     "ker_phi_3": [B[(0, i)] for i in (1, 2)] == [0, 0],
                     "rank_u_3": sa.rank_f2(cols_of(As[0], 6)) == 3,
                     "x0_not_in_P": not in_span(rref([B[(0, i)] for i in (3, 4, 5)]), ss[0]),
                     "cnf_accepts": sa.satisfies(pc, sa.assignment(pc, pn, As, ss, B, 6, 6))}
    sp = st["split"]
    ex = st["exact"]
    st["graded"] = {
        "subspaces": all(st["subspaces"][f"{t},{k},{c}"] == n
                         for (t, k, c), n in HAND_SUBSPACES.items()) and st["rref_canonical"],
        "group_order": all(st["group_order"][f"t{t}_B{p}"] == n for (t, p), n in HAND_GROUP.items()),
        "gens_in_group": all(st["gens_in_group"].values()),
        "exact_group": all(ex[f"t{t}_B{p}"]["group"] == HAND_GROUP[(t, p)] for t, p, _, _ in SMALL),
        "exact_pairs": all(ex[k]["pairs_exact"] and ex[k]["H_orbit_stabiliser"]
                           and ex[k]["classes_exact"] and ex[k]["units_ok"] for k in ex),
        "hand_pairs": all((ex if t < 6 else sp)[f"t{t}_B{p}"]["pairs"] == n
                          for (t, p), n in HAND_PAIRS.items()),
        "hand_pairs_by_x": all(sp[f"t{t}_B{p}"]["by_x_orbit_size"] == {str(k): v for k, v
                                                                       in sorted(m.items())}
                               for (t, p), m in HAND_PAIRS_BY_X.items()),
        "t4_B3_sizes": ex["t4_B3"]["sizes"] == HAND_T4_B3_SIZES,
        "totals": all(v["total"] == HAND_SUBSPACES[(int(k[1]), int(k[1]) - 3, 1)]
                      * HAND_SUBSPACES[(int(k[1]), 3, 0)] for k, v in sp.items()),
        "pairs_divide_G": all(v["pairs_divide_G"] and v["x_units_ok"] for v in sp.values()),
        "classes_valid": all(v["sizes_add_up"] and v["members"] and v["units_in_H"]
                             and v["divide_H"] for v in sp.values()),
        "t6_classes_as_m30": all(sp[f"t{t}_B{p}"]["classes"] == n
                                 for (t, p), n in M30_CLASSES.items()),
        "t7_reps": all(sp[f"t7_B{p}"]["reps_rank_3"] for p in SHAPES.values()),
        "hints": all(st["hints"][k]["hints"] == n and st["hints"][k]["consistent"]
                     for k, n in HAND_HINTS.items()),
        "units": all(st["hints"][k]["units"] == MAIN_UNITS for k in SHAPES),
        "planted": all(st["planted"].values())}
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
        As, ss, B = sa.decode(s.get_model(), names, spec["t"], spec["d"])
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
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
        t, d, au, s0, phis, kd, pvecs = params(spec)
        As, ss = res["A"], res["s"]
        B = {(i, k): v for i, k, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        nf = (As[0] == au and ss[0] == s0
              and all(phis[i] is None or B[(0, i)] == phis[i] for i in range(1, d)))
        res["verified"] = sa.is_system(at, sv, d, t) and sa.anisotropic(sv) and nf
        ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
        res["max_rank"] = max(ranks)
        res["rank_u"] = ranks[0]
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


def run_controls(solver, out_dir):
    start = time.time()
    counts = {}
    res = solve_one(planted_spec(), solver, 300, out_dir)
    counts["planted_" + res["status"]] = 1
    for t, p, rho, d in SMALL:
        sps, summary = instances(t, d, p, rho)
        with open(os.path.join(out_dir, f"classes_t{t}_B{p}.json"), "w") as f:
            json.dump(summary, f, indent=1)
        out = run_group(sps, solver, 12 * 60 - (time.time() - start), 120, out_dir, time.time())
        for key, v in out.items():
            counts[f"t{t}_B{p}_{key}"] = v
    print(f"SUMMARY controls {json.dumps(counts, sort_keys=True)}", flush=True)
    return counts


def run_solve(shape, half, halves, solver, group_seconds, cap_seconds, out_dir):
    start = time.time()
    p = SHAPES[shape]
    sps, summary = instances(T, D, p, RHO)
    with open(os.path.join(out_dir, f"classes_t7_{shape}.json"), "w") as f:
        json.dump(summary, f, indent=1)
    mine = sps[half::halves]
    print(f"classified {shape}: {len(summary['pairs'])} pair orbits, {len(sps)} classes, "
          f"{len(mine)} in this half, {round(time.time() - start, 1)} s", flush=True)
    out = run_group(mine, solver, group_seconds, cap_seconds, out_dir, start)
    print(f"SUMMARY solve {shape} half {half}/{halves} instances {len(mine)} of {len(sps)} "
          f"{json.dumps(out, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m42/predictions.md) ----------

def expected_control(spec):
    """t = 2: SAT exactly for R = span(e_1) (job m30); t = 4, dim V = 5: UNSAT (A(4) = 4)."""
    if spec["t"] == 2:
        return "SAT" if list(spec["r"]) == [2] else "UNSAT"
    return "UNSAT"


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
        if fn.startswith("r3b_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    per_shape = {}
    for name, r in results.items():
        st = r.get("status")
        if r["kind"] == "planted":
            if st in ("SAT", "UNSAT"):
                graded[name] = st == "SAT" and bool(r.get("verified"))
            else:
                ungraded[name] = st
        elif r["kind"] == "control":
            if st in ("SAT", "UNSAT"):
                graded[name] = st == expected_control(r)
                if st == "SAT":
                    graded[name + "_verified"] = bool(r.get("verified"))
            else:
                ungraded[name] = st
        else:
            key = f"B{r['p']}"
            ps = per_shape.setdefault(key, {"counts": {}, "undecided": [], "times": {}})
            ps["counts"][st] = ps["counts"].get(st, 0) + 1
            ps["times"][name] = r.get("wall_seconds")
            if st != "UNSAT":
                ps["undecided"].append(name)
            if st == "SAT":
                graded[name + "_verified"] = bool(r.get("verified"))
                graded[name + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    return {"graded": graded, "ungraded": ungraded, "per_shape": per_shape,
            "any_sat_7": any(r.get("status") == "SAT" for r in results.values()
                             if r["kind"] == "main")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--shape", choices=sorted(SHAPES), default="B6")
    ap.add_argument("--half", type=int, default=0)
    ap.add_argument("--halves", type=int, default=1)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--group-minutes", type=float, default=140.0)
    ap.add_argument("--cap-minutes", type=float, default=8.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="{}")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.solver, args.out_dir)
    elif args.part == "solve":
        run_solve(args.shape, args.half, args.halves, args.solver, args.group_minutes * 60,
                  args.cap_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} "
              + " ".join(f"{k} {v['counts']}" for k, v in sorted(out["per_shape"].items())),
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
