# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Shape c of Case B with dim(X_1 n R) = k - 1 at t = 2k (at t = 6: d = 2), as a split search by
the triple (M_1, ..., M_(k-1), Abar_u) (notes/a6-d2.md).

Setting and encoding as in shape_c.py and shape_c3.py, with m = t - k = k. A_u kills
X_1 = span(e_0, ..., e_(k-1)), so it induces a map Abar_u of X/X_1 whose matrix in the basis
[e_k], ..., [e_(t-1)] is the lower-right m x m block of A_u. Its image is L = [R] (dimension k - d)
and its kernel is D = T^-1(X_1 n R) (dimension d). The case d = k - 1 is rank Abar_u = 1:
Abar_u = a b^T with a spanning L and b a functional with kernel D. Over F_2, Abar_u^2 = (b^T a) Abar_u,
so exactly one of

    J: b^T a = 0, Abar_u^2 = 0, L lies in D, A_u^3 = 0 (at t = 6: Jordan blocks 3, 2, 1);
    E: b^T a = 1, Abar_u idempotent, L n D = 0, A_u fixes the vector that spans Im A_u^2.

Lemma 39 (the symmetries of the normal form) conjugates Abar_u by the same g in GL_m that conjugates
the M_i, so the instances are the orbits of triples (M_1, ..., M_(k-1), Abar_u) under GL_m x GL_(k-1):
for each orbit of commuting tuples (shape_c.orbits), the orbits of the rank-1 matrices under the
stabiliser of its least tuple. The CNF of shape_c.encode_split gets, by hand results:

    (D2) the lower-right block of A_u is Abar_u (unit clauses);
    (B2) [beta(v_i, h)] = M_i [phi(h)] for 1 <= i < k and every basis element h (Lemma 38(a)):
         the lower rows of beta(v_i, v_(k-1+j)) are 0, those of beta(v_i, v_(2k-1+j)) are column j
         of M_i (unit clauses);
    (W2) A_(v_(k-1+j)) maps X_1 into X_1 (Proposition 27(c2)) and induces M_j + (a map into L) on
         X/X_1 (Lemma 46(a)): unit clauses and parity equations;
    (Q2) q(y) lies in D and M_n q(y) lies in D for every n in N (Lemma 38(e)), with q(y) the class
         of sigma(h_y): parity equations;
    (K2) M_(n_y) q(y) lies in L n D (Lemma 46(c)): = 0 in type E, in L in type J: parity equations;
    (T2) T q(y) = y + G_y y (Lemma 46(b)) on the rows of X_1: quadratic, with AND clauses;
    (J2) in type J, if I + M_(n_y) maps X/X_1 into L for some y, then by Lemma 54(d)
         Im A_u^2 = T(L) = span(y), q(y) = a, G_y y = 0 and the columns of G_y lie in span(y).

Filters (Corollaries 23(a) and 28, proved at t = 6): type E keeps a triple only if every non-zero
element of span(M_1, ..., M_(k-1)) is singular and none is I + K with K mapping into L; type J
drops the triples with two or more y as in (J2). At (4, 2) the same code gives control instances
(A(4) = 4, so every one of them is UNSAT).

Parts: selfcheck (pure Python: counts of rank-1 matrices, the orbit partition of the triples,
instance counts), solve (every kept triple at (t, k) of the given types, in passes with growing time
budgets, under a total budget; needs python-sat), grade (the pre-registered predictions of
m19/predictions.md).

Usage: python shape_c4.py --part selfcheck|solve|grade [--t T --k K] [--types EJ]
                          [--budgets 45,300] [--group-minutes 60] [--names-file F] [--out-dir DIR]
"""
import argparse
import functools
import json
import os
import subprocess
import sys
import time

import case_b_shapes as cs
import sat_aniso as sa
import shape_c as sc


# ---------- matrices on X/X_1 ----------

def m_of_y(Ms, yb):
    """M_(n_y) for y = sum of the e_j over the bits j - 1 of yb."""
    M = 0
    for j, Mj in enumerate(Ms, start=1):
        if (yb >> (j - 1)) & 1:
            M ^= Mj
    return M


def all_singular(Ms, m):
    return all(sa.rank_f2(sa.rows_of(m_of_y(Ms, yb), m)) < m for yb in range(1, 1 << len(Ms)))


def rank1_matrices(m):
    return [M for M in range(1, 1 << (m * m)) if sa.rank_f2(sa.rows_of(M, m)) == 1]


def image_vector(Ab, m):
    """a: the non-zero column of a rank-1 matrix (its image is span(a))."""
    for c in range(m):
        v = sa.mat_apply(Ab, 1 << c, m)
        if v:
            return v
    raise ValueError("zero matrix")


def row_functional(Ab, m):
    """b: the non-zero row of a rank-1 matrix (its kernel is {q : parity(b & q) = 0})."""
    for row in sa.rows_of(Ab, m):
        if row:
            return row
    raise ValueError("zero matrix")


def jtype(Ab, m):
    """'J' if Abar_u^2 = 0 (so A_u^3 = 0), else 'E' (Abar_u idempotent)."""
    return "J" if sa.mat_mul(Ab, Ab, m) == 0 else "E"


def in_line(v, a):
    return v == 0 or v == a


def unit_ys(Ms, m, a):
    """The non-zero y (bit j - 1 <-> e_j) such that I + M_(n_y) maps X/X_1 into span(a)."""
    I = sc.identity(m)
    out = []
    for yb in range(1, 1 << len(Ms)):
        K = m_of_y(Ms, yb) ^ I
        if all(in_line(sa.mat_apply(K, 1 << c, m), a) for c in range(m)):
            out.append(yb)
    return out


def keep(Ms, m, Ab):
    """Corollary 23(a) and Corollary 28(a) in type E; Corollary 28(b) in type J."""
    a = image_vector(Ab, m)
    ys = unit_ys(Ms, m, a)
    if jtype(Ab, m) == "E":
        return all_singular(Ms, m) and not ys
    return len(ys) <= 1


# ---------- the orbits of triples ----------

def group_elements(m, r):
    return [(g, sa.mat_inv(g, m), R) for g in sc.gl(m) for R in sc.gl(r)]


def stabiliser(tup, m, r):
    """The elements (g, g^-1, R) of GL_m x GL_r that fix the tuple."""
    return [(g, gi, R) for g, gi, R in group_elements(m, r) if sc.act(g, gi, R, tup, m) == tup]


def conj(gi, Ab, g, m):
    return sa.mat_mul(sa.mat_mul(gi, Ab, m), g, m)


@functools.lru_cache(maxsize=None)
def triples(m, r):
    """[(orbit index, least tuple, Abar)] over all orbits of triples (tuple, rank-1 matrix) under
    GL_m x GL_r: for each orbit of commuting r-tuples, the least rank-1 matrix of each orbit under
    the stabiliser of the orbit's least tuple."""
    out = []
    for idx, (tup, _, _) in enumerate(sc.orbits(m, r)):
        stab = stabiliser(tup, m, r)
        left = set(rank1_matrices(m))
        while left:
            Ab = min(left)
            out.append((idx, tup, Ab))
            left -= {conj(gi, Ab, g, m) for g, gi, _ in stab}
    return out


def instances(m, r, types="EJ"):
    """[(orbit index, tuple, Abar, type)] of the kept triples, type E before type J."""
    out = []
    for ty in ("E", "J"):
        if ty not in types:
            continue
        for idx, Ms, Ab in triples(m, r):
            if jtype(Ab, m) == ty and keep(Ms, m, Ab):
                out.append((idx, Ms, Ab, ty))
    return out


# ---------- the encoding ----------

def w_index(k, j):
    """Index of v_(k-1+j), the element of W with phi = e_j (1 <= j <= k - 1)."""
    return k - 1 + j


def p_index(k, j):
    """Index of v_(2k-1+j), the basis element with phi = e_(k+j) (0 <= j < m)."""
    return 2 * k - 1 + j


def hs_of(k, yb):
    return [w_index(k, j) for j in range(1, k) if (yb >> (j - 1)) & 1]


def yvec(yb):
    """y as a vector of X (bit j - 1 of yb <-> e_j)."""
    return yb << 1


def q_vars(S, B, k, m, yb):
    """For each coordinate c < m of X/X_1, the variables whose sum is coordinate c of q(y)."""
    hs = hs_of(k, yb)
    out = []
    for c in range(m):
        vs = [S[i][k + c] for i in hs]
        vs += [B[(hs[a], hs[b])][k + c] for a in range(len(hs)) for b in range(a + 1, len(hs))]
        out.append(vs)
    return out


def gy_vars(A, k, yb, r, j):
    """The variables whose sum is entry (r, j) of G_y (r, j < k)."""
    return [A[i][r][j] for i in hs_of(k, yb)]


def row_of(f, M, m):
    """The functional f^T M: bit c is the sum over l of f_l M[l][c]."""
    return sum(1 << c for c in range(m) if sa.parity(f & sa.mat_apply(M, 1 << c, m)))


def lin(cnf, f, qv, rhs):
    """sum over c of f_c (sum of qv[c]) = rhs."""
    cnf.xor_eq([x for c, vs in enumerate(qv) if (f >> c) & 1 for x in vs], rhs)


def add_units(cnf, names, t, k, Ms, Ab):
    """(D2), (B2), (W2)."""
    A, B = names[0], names[2]
    m = t - k
    a = image_vector(Ab, m)
    ann = sa.nullspace([a], m)
    for l in range(m):
        for c in range(m):
            v = A[0][k + l][k + c]
            cnf.clauses.append([v] if (Ab >> (m * l + c)) & 1 else [-v])
    for i, M in enumerate(Ms, start=1):
        for j in range(1, k):
            for l in range(m):
                cnf.clauses.append([-B[(i, w_index(k, j))][k + l]])
        for j in range(m):
            col = sa.mat_apply(M, 1 << j, m)
            for l in range(m):
                v = B[(i, p_index(k, j))][k + l]
                cnf.clauses.append([v] if (col >> l) & 1 else [-v])
    for j, M in enumerate(Ms, start=1):
        i = w_index(k, j)
        for c in range(k):
            for l in range(m):
                cnf.clauses.append([-A[i][k + l][c]])
        for c in range(m):
            col = sa.mat_apply(M, 1 << c, m)
            for f in ann:
                cnf.xor_eq([A[i][k + l][k + c] for l in range(m) if (f >> l) & 1],
                           sa.parity(f & col))


def add_q(cnf, names, t, k, Ms, Ab):
    """(Q2) and (K2)."""
    S, B = names[1], names[2]
    m = t - k
    I = sc.identity(m)
    a, b = image_vector(Ab, m), row_functional(Ab, m)
    ann = sa.nullspace([a], m)
    ty = jtype(Ab, m)
    for yb in range(1, 1 << (k - 1)):
        qv = q_vars(S, B, k, m, yb)
        My = m_of_y(Ms, yb)
        for nb in range(1 << k):
            Mn = (I if nb & 1 else 0) ^ m_of_y(Ms, nb >> 1)
            if Mn:
                lin(cnf, row_of(b, Mn, m), qv, 0)
        if ty == "E":
            for row in sa.rows_of(My, m):
                lin(cnf, row, qv, 0)
        else:
            for f in ann:
                lin(cnf, row_of(f, My, m), qv, 0)


def add_t2(cnf, names, t, k, Ms, Ab):
    """(T2): rows r < k of T q(y) = y + G_y y."""
    A, S, B = names[0], names[1], names[2]
    m = t - k
    for yb in range(1, 1 << (k - 1)):
        qv = q_vars(S, B, k, m, yb)
        qz = [vs[0] if len(vs) == 1 else cnf.xor_def(vs) for vs in qv]
        yv = yvec(yb)
        for r in range(k):
            lits = [cnf.AND(qz[c], A[0][r][k + c]) for c in range(m)]
            for j in range(1, k):
                if (yv >> j) & 1:
                    lits += gy_vars(A, k, yb, r, j)
            cnf.xor_eq(lits, (yv >> r) & 1)


def add_j2(cnf, names, t, k, Ms, Ab):
    """(J2), in type J only."""
    A, S, B = names[0], names[1], names[2]
    m = t - k
    if jtype(Ab, m) != "J":
        return
    a = image_vector(Ab, m)
    ys = unit_ys(Ms, m, a)
    if len(ys) > 1:
        cnf.clauses.append([])
    for yb in ys:
        yv = yvec(yb)
        for r in range(k):
            cnf.xor_eq([A[0][r][k + c] for c in range(m) if (a >> c) & 1], (yv >> r) & 1)
        qv = q_vars(S, B, k, m, yb)
        for c in range(m):
            cnf.xor_eq(list(qv[c]), (a >> c) & 1)
        for r in range(k):
            cnf.xor_eq([x for j in range(1, k) if (yv >> j) & 1 for x in gy_vars(A, k, yb, r, j)],
                       0)
        anny = sa.nullspace([yv], k)
        for j in range(k):
            for f in anny:
                cnf.xor_eq([x for r in range(k) if (f >> r) & 1 for x in gy_vars(A, k, yb, r, j)],
                           0)


FAMILIES = ("units", "q", "t2", "j2")
ADDERS = {"units": add_units, "q": add_q, "t2": add_t2, "j2": add_j2}


def add_d2(cnf, names, t, k, Ms, Ab):
    for fam in FAMILIES:
        ADDERS[fam](cnf, names, t, k, Ms, Ab)


def encode_d2(t, k, Ms, Ab):
    if t != 2 * k:
        raise ValueError("d = k - 1 as rank Abar_u = 1 needs t = 2k")
    if sa.rank_f2(sa.rows_of(Ab, t - k)) != 1:
        raise ValueError("Abar_u must have rank 1")
    cnf, names = sc.encode_split(t, k, Ms)
    add_d2(cnf, names, t, k, Ms, Ab)
    return cnf, names


# ---------- direct checks on coordinates ----------

def block(M, t, k):
    """The lower-right (t - k) x (t - k) block of a t x t matrix, as an m x m mask."""
    m = t - k
    return sum(((M >> (t * (k + l) + k + c)) & 1) << (m * l + c) for l in range(m) for c in range(m))


def q_of(ss, B, k, yb):
    hs = hs_of(k, yb)
    x = 0
    for i in hs:
        x ^= ss[i]
    for a in range(len(hs)):
        for b in range(a + 1, len(hs)):
            x ^= B[(hs[a], hs[b])]
    return x >> k


def g_of(As, k, yb):
    """A_(h_y) (its restriction to X_1 is G_y)."""
    G = 0
    for i in hs_of(k, yb):
        G ^= As[i]
    return G


def t_of(As, t, k, z):
    """T [z] = A_u (lift of z), for z a vector of X/X_1."""
    x = 0
    for c in range(t - k):
        if (z >> c) & 1:
            x ^= cs.col(As[0], k + c, t)
    return x


def q_ok(q, Ms, m, Ab, yb):
    """(Q2) and (K2) for one value q of q(y)."""
    I = sc.identity(m)
    a, b = image_vector(Ab, m), row_functional(Ab, m)
    for nb in range(1 << (len(Ms) + 1)):
        Mn = (I if nb & 1 else 0) ^ m_of_y(Ms, nb >> 1)
        if Mn and sa.parity(b & sa.mat_apply(Mn, q, m)):
            return False
    mq = sa.mat_apply(m_of_y(Ms, yb), q, m)
    return mq == 0 if jtype(Ab, m) == "E" else in_line(mq, a)


def sat_units(As, ss, B, t, k, Ms, Ab):
    m = t - k
    a = image_vector(Ab, m)
    if block(As[0], t, k) != Ab:
        return False
    for i, M in enumerate(Ms, start=1):
        for j in range(1, k):
            if B[(i, w_index(k, j))] >> k:
                return False
        for j in range(m):
            if B[(i, p_index(k, j))] >> k != sa.mat_apply(M, 1 << j, m):
                return False
    for j, M in enumerate(Ms, start=1):
        i = w_index(k, j)
        for c in range(k):
            if cs.col(As[i], c, t) >> k:
                return False
        for c in range(m):
            if not in_line((cs.col(As[i], k + c, t) >> k) ^ sa.mat_apply(M, 1 << c, m), a):
                return False
    return True


def sat_q(As, ss, B, t, k, Ms, Ab):
    m = t - k
    return all(q_ok(q_of(ss, B, k, yb), Ms, m, Ab, yb) for yb in range(1, 1 << (k - 1)))


def sat_t2(As, ss, B, t, k, Ms, Ab):
    low = (1 << k) - 1
    for yb in range(1, 1 << (k - 1)):
        yv = yvec(yb)
        tq = t_of(As, t, k, q_of(ss, B, k, yb))
        if (tq & low) != ((yv ^ sa.mat_apply(g_of(As, k, yb), yv, t)) & low):
            return False
    return True


def sat_j2(As, ss, B, t, k, Ms, Ab):
    m = t - k
    low = (1 << k) - 1
    if jtype(Ab, m) != "J":
        return True
    a = image_vector(Ab, m)
    ys = unit_ys(Ms, m, a)
    if len(ys) > 1:
        return False
    for yb in ys:
        yv = yvec(yb)
        if (t_of(As, t, k, a) & low) != yv:
            return False
        if q_of(ss, B, k, yb) != a:
            return False
        G = g_of(As, k, yb)
        if (sa.mat_apply(G, yv, t) & low) != 0:
            return False
        if any(not in_line(cs.col(G, j, t) & low, yv) for j in range(k)):
            return False
    return True


CHECKS = {"units": sat_units, "q": sat_q, "t2": sat_t2, "j2": sat_j2}


def satisfies_d2(As, ss, B, t, k, Ms, Ab):
    """(D2) to (J2) checked directly on coordinates, without the CNF."""
    return all(CHECKS[fam](As, ss, B, t, k, Ms, Ab) for fam in FAMILIES)


def model_facts(As, ss, B, t, k, Ab):
    """What the hand results predict for a model: every rank <= t - k (Proposition 26(a)), the
    facts of Lemma 38 (shape_c.model_facts), the block Abar_u, d = k - 1, and A_u^3 = 0 exactly in
    type J."""
    facts = sc.model_facts(As, ss, B, t, k)
    facts["block_is_Ab"] = block(As[0], t, k) == Ab
    R = sa.independent([cs.col(As[0], c, t) for c in range(t)])
    X1 = [1 << c for c in range(k)]
    facts["dim_X1_cap_R"] = len(X1) + len(R) - sa.rank_f2(X1 + R)
    A3 = sa.mat_mul(sa.mat_mul(As[0], As[0], t), As[0], t)
    facts["A_u_cubed_zero"] = A3 == 0
    facts["type_ok"] = (A3 == 0) == (jtype(Ab, t - k) == "J")
    return facts


# ---------- selfcheck ----------

def selfcheck():
    st = {}
    graded = {}
    expect = {"2,1": (9, 3, 16), "3,2": (49, 21, 7456)}
    for m, r in ((2, 1), (3, 2)):
        key = f"{m},{r}"
        r1 = rank1_matrices(m)
        trip = triples(m, r)
        group = group_elements(m, r)
        partition_ok = True
        total = 0
        for idx, (tup, _, _) in enumerate(sc.orbits(m, r)):
            stab = stabiliser(tup, m, r)
            s = 0
            for i2, _, Ab in trip:
                if i2 != idx:
                    continue
                fixed = sum(1 for g, gi, _ in stab if conj(gi, Ab, g, m) == Ab)
                s += len(stab) // fixed
                total += len(group) // fixed
            partition_ok = partition_ok and s == len(r1)
        inst = instances(m, r)
        st[key] = {"rank1": len(r1), "nilpotent": sum(1 for M in r1 if jtype(M, m) == "J"),
                   "triples": len(trip), "first_tuple_triples": sum(1 for i, _, _ in trip if i == 0),
                   "triple_total": total, "expected_total": expect[key][2] * len(r1),
                   "partition_ok": partition_ok,
                   "instances": {ty: sum(1 for x in inst if x[3] == ty) for ty in "EJ"},
                   "pair_orbits_in_E": sorted({x[0] for x in inst if x[3] == "E"})}
        graded[key + "_rank1"] = len(r1) == expect[key][0]
        graded[key + "_nilpotent"] = st[key]["nilpotent"] == expect[key][1]
        graded[key + "_partition"] = partition_ok and total == st[key]["expected_total"]
        graded[key + "_first_tuple"] = st[key]["first_tuple_triples"] == 2
        graded[key + "_both_types"] = all(st[key]["instances"][ty] > 0 for ty in "EJ")
    # The 5 field orbits of Corollary 23(d) (an invertible element in the span) are not in type E.
    field = [i for i, (tup, _, _) in enumerate(sc.orbits(3, 2)) if not all_singular(tup, 3)]
    graded["3,2_E_singular"] = not set(field) & set(st["3,2"]["pair_orbits_in_E"])
    st["graded"] = graded
    return st


# ---------- solving ----------

def instance_name(t, k, idx, Ab, ty):
    return f"d2_t{t}_k{k}_o{idx:02d}_a{Ab:03d}{ty}"


def child(t, k, Ms, Ab, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_d2(t, k, Ms, Ab)
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
        As, ss, B = sa.decode(s.get_model(), names, t, t + k - 1)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_one(t, k, inst, solver, budget_seconds, out_dir, pass_no):
    idx, Ms, Ab, ty = inst
    d = t + k - 1
    name = instance_name(t, k, idx, Ab, ty)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--k",
           str(k), "--ms", ",".join(str(M) for M in Ms), "--ab", str(Ab), "--solver", solver,
           "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "k": k, "d": d, "orbit": idx, "Ms": list(Ms), "Ab": Ab, "type": ty,
                "name": name, "pass": pass_no, "budget_seconds": round(budget_seconds),
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and cs.in_shape(As, ss, B, t, k, "c")
                           and sc.satisfies_split(As, t, k, Ms)
                           and satisfies_d2(As, ss, B, t, k, Ms, Ab))
        res["facts"] = model_facts(As, ss, B, t, k, Ab)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, k, types, solver, budgets, group_seconds, out_dir, names_only=None):
    """Every kept triple at (t, k) of the given types, in passes: pass p gives each instance that
    is still undecided budgets[p] seconds, under the total budget. Instances not reached in pass 0
    are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    insts = [x for x in instances(t - k, k - 1, types)
             if names_only is None or instance_name(t, k, x[0], x[2], x[3]) in names_only]
    start = time.time()
    results = {}
    pending = list(insts)
    for p, budget in enumerate(budgets):
        nxt = []
        for inst in pending:
            name = instance_name(t, k, inst[0], inst[2], inst[3])
            left = group_seconds - (time.time() - start)
            if left < 1:
                if p == 0:
                    res = {"status": "SKIPPED", "t": t, "k": k, "orbit": inst[0],
                           "Ms": list(inst[1]), "Ab": inst[2], "type": inst[3], "name": name}
                    with open(os.path.join(out_dir, name + ".json"), "w") as f:
                        json.dump(res, f, indent=1)
                    results[name] = res
                nxt.append(inst)
                continue
            res = solve_one(t, k, inst, solver, min(budget, left), out_dir, p)
            results[name] = res
            if res["status"] in ("UNKNOWN", "SKIPPED"):
                nxt.append(inst)
        pending = nxt
        if not pending:
            break
    counts = {}
    for r in results.values():
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    return {"t": t, "k": k, "types": types, "instances": len(insts), "counts": counts,
            "undecided": [instance_name(t, k, x[0], x[2], x[3]) for x in pending]}


# Pre-registered (m19/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
# ERROR are reported and not graded.
CONTROLS = ((4, 2),)
EXPLORATORY = ((6, 3),)


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("d2_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {}
    for t, k in CONTROLS + EXPLORATORY:
        for ty in "EJ":
            names = [instance_name(t, k, x[0], x[2], x[3]) for x in instances(t - k, k - 1, ty)]
            status[f"{t},{k},{ty}"] = {n: results.get(n, {}).get("status", "missing")
                                       for n in names}
    for t, k in CONTROLS:
        for ty in "EJ":
            for name, s in status[f"{t},{k},{ty}"].items():
                if s in ("SAT", "UNSAT"):
                    graded[name] = s == "UNSAT"
                else:
                    ungraded[name] = s
    for name, r in results.items():
        if r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - r["k"]
        graded[name + "_facts"] = all(fa.get(key) for key in
                                      ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e",
                                       "block_is_Ab", "type_ok"))
        graded[name + "_d"] = fa.get("dim_X1_cap_R") == r["k"] - 1
    counts = {key: {s: list(v.values()).count(s) for s in sorted(set(v.values()))}
              for key, v in status.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    undecided = {key: [n for n, s in v.items() if s not in ("SAT", "UNSAT")]
                 for key, v in status.items()}
    out = {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
           "undecided": undecided}
    for ty in "EJ":
        out[f"all_unsat_6_3_{ty}"] = all(s == "UNSAT" for s in status[f"6,3,{ty}"].values())
    out["all_unsat_6_3"] = out["all_unsat_6_3_E"] and out["all_unsat_6_3_J"]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=4)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--types", default="EJ")
    ap.add_argument("--ms", default="")
    ap.add_argument("--ab", type=int, default=0)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budgets", default="45,300")
    ap.add_argument("--group-minutes", type=float, default=60.0)
    ap.add_argument("--names-file", default="")
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        Ms = tuple(int(x) for x in args.ms.split(",") if x)
        child(args.t, args.k, Ms, args.ab, args.solver, args.child_out)
    elif args.part == "solve":
        names_only = None
        if args.names_file:
            with open(args.names_file) as f:
                names_only = {line.strip() for line in f if line.strip()}
        budgets = [float(x) for x in args.budgets.split(",") if x]
        out = solve_all(args.t, args.k, args.types, args.solver, budgets,
                        args.group_minutes * 60, args.out_dir, names_only)
        print(f"SUMMARY solve t{args.t} k{args.k} types {args.types} instances "
              f"{out['instances']} {json.dumps(out['counts'], sort_keys=True)} undecided "
              f"{len(out['undecided'])}", flush=True)
        with open(os.path.join(args.out_dir, f"solve_t{args.t}_k{args.k}_{args.types}.json"),
                  "w") as f:
            json.dump(out, f, indent=1)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"all_unsat_6_3 {out['all_unsat_6_3']} E {out['all_unsat_6_3_E']} "
              f"J {out['all_unsat_6_3_J']}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
