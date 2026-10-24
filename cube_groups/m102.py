# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m102: the rank-0 case of (B7)_8 (t = 8, dim V = 11, dim P = 7) split by the commuting space
T(N) of Lemma 104 (notes/a93.md, notes/a94.md, cube_groups/m102-predictions.md).

What came back on 2026-10-24 (job m101, notes/a94.md): every graded check held (16 of 16 in each
half), all eight positive controls were SAT with verified models (the four "relax_n" ones with
anisotropy kept on N, one of them with A_(v_2) = A_(v_3) = A_u J pi, J the all-ones matrix), but all
68 sweeps (m100's instance plus A_(v_1) = 0 and "x0 not in C") were UNKNOWN at 180 s.

The split (by hand, notes/a94.md). In the rank-0 case A_n = A_u-bar T_n pi for n in N = ker phi,
with n -> T_n linear, T_u = I and the T_n commuting (Lemma 104). So T(N) is a space of commuting
3 x 3 matrices that contains I, of dimension 1, 2 or 3, and N_0 = ker T has dimension 3, 2 or 1.
The basis of N can be chosen so that

    t1   dim T(N) = 1:  T_(v_1) = T_(v_2) = T_(v_3) = 0             (N_0 = span(v_1, v_2, v_3))
    t2   dim T(N) = 2:  T_(v_1) = T_(v_2) = 0, T_(v_3) = M          (N_0 = span(v_1, v_2))
    t3   dim T(N) = 3:  T_(v_1) = 0, T_(v_2) = M_1, T_(v_3) = M_2   (N_0 = span(v_1))

and then every A_n with n in N is fixed. A 3-dimensional commuting space is a commutative
subalgebra (it lies in the algebra its elements generate, which has dimension <= 3 by Schur's
bound). Conjugating the whole system by g in G with g A_u = A_u g (and re-choosing the complement
of N so that phi keeps its normal form) replaces T(N) by g_Q T(N) g_Q^(-1), where g_Q is the map g
induces on Q = X / X_1. So one instance per orbit of the group Kbar = {g_Q} on the spaces is
enough. Kbar is found by machine: for each of the 168 g_Q in GL(Q), an element g of GL_8(F_2) with
g e_0 = e_0, g P = P, g X_1 = X_1, g A_u = A_u g and inducing g_Q is searched for in the affine
space of solutions of these linear conditions, and every g found is checked outside the search.
A g_Q for which no g is found is left out, which can only give more instances.

Every w != 0 in N_0 has A_w = 0, so Lemma 105 applies to each: beta(w, V) + span(sigma(w)) lies
in X_1, and (A_u not idempotent) x0 is not in it.

Parts (one shard of the 13 pairs per job, as m100 and m101):

    check    GL_3(F_2) and the commuting spaces (counts and orbits against the hand counts), Kbar
             for every class of the shard and the orbit representatives, the added conditions,
             and m101's sweep CNF as an unchanged prefix
    control  positive controls: t1 without anisotropy, and (shard a) t2 with M = J with
             anisotropy on N, which a model of job m101 satisfies after a change of basis of N
    sweep    the t1 instance of every class of the shard, capped
    pilot    every t3 and t2 orbit representative of one class, capped, for timing
    grade    the graded checks of m102-predictions.md

Usage: python m102.py --part check|control|sweep|pilot|grade --shard a|b [--cap-seconds S]
       [--pilot-minutes M] [--out-dir D]
"""
import argparse
import functools
import hashlib
import itertools
import json
import os
import random
import subprocess
import sys
import time

import m100
import m101
import sat_aniso as sa

T, D, KD = m100.T, m100.D, m100.KD
NX1, X0, X1_MASK = m101.NX1, m101.X0, m101.X1_MASK
Q = T - NX1                              # Q = X / X_1 with basis pi(e_5), pi(e_6), pi(e_7)
I3 = sa.entries(Q, [(0, 0), (1, 1), (2, 2)])
J3 = (1 << (Q * Q)) - 1                  # the all-ones matrix
PILOT = {"a": (0, 0), "b": (11, 0)}
TRIES = 300
MODES = m101.MODES


def mm3(a, b):
    return sa.mat_mul(a, b, Q)


GL3 = tuple(g for g in range(1 << (Q * Q)) if sa.rank_f2(sa.rows_of(g, Q)) == Q)
INV3 = {g: sa.mat_inv(g, Q) for g in GL3}


# ---------- the commuting spaces T(N) ----------

@functools.lru_cache(maxsize=None)
def t_spaces():
    """(the 2-dimensional spaces span(I, M), the 3-dimensional commuting spaces containing I), each
    as a sorted tuple of its elements."""
    two = sorted({tuple(sorted((0, I3, m, m ^ I3))) for m in range(1 << (Q * Q)) if m not in (0, I3)})
    three = set()
    for m1 in range(1 << (Q * Q)):
        if m1 in (0, I3):
            continue
        for m2 in range(m1 + 1, 1 << (Q * Q)):
            if sa.rank_f2([I3, m1, m2]) == 3 and mm3(m1, m2) == mm3(m2, m1):
                three.add(tuple(sorted(m100.span([I3, m1, m2]))))
    return two, sorted(three)


def conj_space(g, s):
    gi = INV3[g]
    return tuple(sorted(mm3(mm3(g, m), gi) for m in s))


def orbits(spaces, group):
    """[representative, size of its orbit] for the orbits of the conjugation action of group."""
    left = set(spaces)
    out = []
    for s in spaces:
        if s not in left:
            continue
        orb = {conj_space(g, s) for g in group}
        out.append([list(s), len(orb)])
        left -= orb
    return out


def basis_of(s):
    """Elements M (and M_2) that span s together with I."""
    m1 = min(m for m in s if m not in (0, I3))
    if len(s) == 4:
        return [m1]
    return [m1, min(m for m in s if m not in (0, I3, m1, m1 ^ I3))]


# ---------- the group Kbar ----------

def g_constraints(au, gq, t=T):
    """Linear conditions on the t * t entries of g (bit t * r + c, as sat_aniso; bit t * t is the
    constant): g e_0 = e_0, g P in P, g X_1 in X_1, pi g = gq pi on e_5..e_7, g A_u = A_u g."""
    nb = t * t
    cons = []

    def var(r, c):
        return 1 << (t * r + c)

    def eq(mask, rhs):
        cons.append(mask | (rhs << nb))

    for r in range(t):
        eq(var(r, 0), int(r == 0))
    for j in range(1, t):
        eq(var(0, j), 0)
    for c in range(NX1):
        for r in range(NX1, t):
            eq(var(r, c), 0)
    for c in range(NX1, t):
        y = sa.mat_apply(gq, 1 << (c - NX1), Q)
        for r in range(NX1, t):
            eq(var(r, c), (y >> (r - NX1)) & 1)
    for r in range(t):
        for c in range(t):
            mask = 0
            for k in range(t):
                if (au >> (t * k + c)) & 1:
                    mask ^= var(r, k)
                if (au >> (t * r + k)) & 1:
                    mask ^= var(k, c)
            eq(mask, 0)
    return cons


def g_ok(au, gq, g, t=T):
    """The conditions on g, checked directly (not through g_constraints)."""
    cols = [sa.mat_apply(g, 1 << c, t) for c in range(t)]
    return (sa.rank_f2(cols) == t and cols[0] == X0
            and all((cols[j] & 1) == 0 for j in range(1, t))
            and all((cols[c] >> NX1) == 0 for c in range(NX1))
            and all((cols[c] >> NX1) == sa.mat_apply(gq, 1 << (c - NX1), Q) for c in range(NX1, t))
            and sa.mat_mul(g, au, t) == sa.mat_mul(au, g, t))


def lift_g(au, gq, rng, tries=TRIES):
    """An invertible g with the conditions, or None if none was found."""
    nb = T * T
    basis = sa.nullspace(g_constraints(au, gq), nb + 1)
    part = next((b for b in basis if (b >> nb) & 1), None)
    if part is None:
        return None
    hom = [b ^ part if (b >> nb) & 1 else b for b in basis if b != part]
    for _ in range(tries):
        x = part
        for b in hom:
            if rng.random() < 0.5:
                x ^= b
        g = x & ((1 << nb) - 1)
        if g_ok(au, gq, g):
            return g
    return None


def kbar(spec):
    """{g_Q: a checked g} for the class of spec."""
    rng = random.Random(1020 + 100 * spec["pair"] + spec["cls"])
    out = {}
    for gq in GL3:
        g = lift_g(spec["au"], gq, rng)
        if g is not None:
            out[gq] = g
    return out


def class_cases(spec):
    """The instances of one class: t1, then one per orbit of Kbar on the 3- and 2-dimensional
    spaces."""
    two, three = t_spaces()
    grp = sorted(kbar(spec))
    return ([case_t1()] + [case_t3(*basis_of(s)) for s, _ in orbits(three, grp)]
            + [case_t2(basis_of(s)[0]) for s, _ in orbits(two, grp)])


# ---------- the cases ----------

def case_t1():
    return {"kind": "t1", "maps": [0, 0]}


def case_t2(m):
    return {"kind": "t2", "maps": [0, m]}


def case_t3(m1, m2):
    return {"kind": "t3", "maps": [m1, m2]}


def case_label(case):
    m2, m3 = case["maps"]
    if case["kind"] == "t1":
        return "t1"
    if case["kind"] == "t2":
        return f"t2_m{m3:03d}"
    return f"t3_m{m2:03d}_{m3:03d}"


def inst_name(spec, case):
    return spec["name"] + "_" + case_label(case)


def n0_ws(case):
    """The non-zero elements of N_0 as index sets of v_1, v_2, v_3."""
    base = {"t1": (1, 2, 3), "t2": (1, 2), "t3": (1,)}[case["kind"]]
    return [w for k in range(1, len(base) + 1) for w in itertools.combinations(base, k)]


def extra_in_x1(case):
    return {"t1": (2, 3), "t2": (2,), "t3": ()}[case["kind"]]


def a_of_t(au, tm, t=T):
    """A_u-bar T pi: zero on X_1 = span(e_0..e_4), and e_c -> A_u lift(T pi e_c) for c >= 5."""
    cols = [0] * NX1 + [sa.mat_apply(au, sa.mat_apply(tm, 1 << (c - NX1), Q) << NX1, t)
                        for c in range(NX1, t)]
    return sa.from_cols(cols, t)


# ---------- the added conditions ----------

def add_fixed_map(cnf, names, i, a, t=T):
    A = names[0]
    for r in range(t):
        for c in range(t):
            cnf.clauses.append([A[i][r][c]] if (a >> (t * r + c)) & 1 else [-A[i][r][c]])
    return t * t


def add_in_x1_at(cnf, names, i, t, d, nx1=NX1):
    """beta(v_i, e_j) in X_1 for j != i (Lemma 105 (a))."""
    B = names[2]
    n = 0
    for j in range(d):
        if j == i:
            continue
        for r in range(nx1, t):
            cnf.clauses.append([-B[m101.bkey(i, j)][r]])
            n += 1
    return n


def w_generators(names, d, w):
    """sigma(w) and beta(w, e_j), each as the list of variable vectors that sum to it."""
    S, B = names[1], names[2]
    gens = [[S[i] for i in w] + [B[(i, j)] for i, j in itertools.combinations(w, 2)]]
    for j in range(d):
        vecs = [B[m101.bkey(i, j)] for i in w if i != j]
        if vecs:
            gens.append(vecs)
    return gens


def add_case_two_w(cnf, names, t, d, w, nx1=NX1):
    """x0 = e_0 not in beta(w, V) + span(sigma(w)), through a functional f on the first nx1
    coordinates with f(e_0) = 1. Returns the number of generators."""
    f = [cnf.new() for _ in range(nx1)]
    cnf.clauses.append([f[0]])
    gens = w_generators(names, d, w)
    for vecs in gens:
        cnf.xor_eq([cnf.AND(f[r], vec[r]) for vec in vecs for r in range(nx1)], 0)
    return len(gens)


def build(spec, case, mode="sweep"):
    """(cnf, names, counts): m101's instance (A_(v_1) = 0 and the rest) plus the case."""
    cnf, names, counts = m101.build(spec, mode)
    counts["m101_clauses"] = len(cnf.clauses)
    au = spec["au"]
    counts["maps"] = sum(add_fixed_map(cnf, names, i, a_of_t(au, tm))
                         for i, tm in zip((2, 3), case["maps"]))
    counts["in_x1_extra"] = sum(add_in_x1_at(cnf, names, i, T, D) for i in extra_in_x1(case))
    counts["case_two_extra"] = (sum(add_case_two_w(cnf, names, T, D, w)
                                    for w in n0_ws(case) if w != (1,))
                                if m101.case_two_required(spec) else 0)
    return cnf, names, counts


# ---------- checking a model ----------

def model_gens(ss, B, w, d=D):
    sig = 0
    for i in w:
        sig ^= ss[i]
    for i, j in itertools.combinations(w, 2):
        sig ^= B[(i, j)]
    gens = [sig]
    for j in range(d):
        others = [i for i in w if i != j]
        if others:
            vec = 0
            for i in others:
                vec ^= B[m101.bkey(i, j)]
            gens.append(vec)
    return gens


def extra_checks(spec, case, res):
    As, ss = res["A"], res["s"]
    B = {(i, k): v for i, k, v in res["B"]}
    ws = [w for w in n0_ws(case) if w != (1,)]
    return {"t_maps": all(As[i] == a_of_t(spec["au"], tm) for i, tm in zip((2, 3), case["maps"])),
            "in_x1_extra": all((B[m101.bkey(i, j)] & ~X1_MASK) == 0
                               for i in extra_in_x1(case) for j in range(D) if j != i),
            "case_two_extra": all(X0 not in m100.span(model_gens(ss, B, w)) for w in ws)}


def needed(spec, mode):
    need = m101.needed(spec, mode) + ["t_maps", "in_x1_extra"]
    if m101.case_two_required(spec):
        need.append("case_two_extra")
    return need


# ---------- solving ----------

def child(spec, case, mode, path):
    from pysat.solvers import Solver
    cnf, names, _ = build(spec, case, mode)
    start = time.time()
    used = None
    for name in sa.SOLVERS:
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
        As, ss, B = sa.decode(s.get_model(), names, T, D)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_one(spec, case, mode, budget, out_dir, part):
    tag = inst_name(spec, case) + "_" + mode
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--case", json.dumps(case), "--mode", mode, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({k: spec[k] for k in ("name", "pair", "cls", "dmeet", "class_size")})
    row.update({"instance": inst_name(spec, case), "kind": case["kind"], "maps": case["maps"],
                "mode": mode, "part": part, "wall_seconds": round(time.time() - start, 2),
                "budget_seconds": budget})
    if res["status"] == "SAT":
        row["check"] = m101.check_model(spec, res)
        row["check"].update(extra_checks(spec, case, res))
        row["verified"] = all(row["check"][k] for k in needed(spec, mode))
    print(f"solve {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


def append_row(out_dir, shard, row):
    rows = m100.load(out_dir, f"m102{shard}_rows.json") or []
    rows.append(row)
    with open(os.path.join(out_dir, f"m102{shard}_rows.json"), "w") as f:
        json.dump(rows, f, indent=1)


# ---------- the parts ----------

def run_check(shard, out_dir):
    g = {}
    two, three = t_spaces()
    g["gl3_168"] = len(GL3) == 168 and all(mm3(a, INV3[a]) == I3 for a in GL3)
    g["spaces_255_183"] = (len(two), len(three)) == (255, 183)
    sets3 = [set(s) for s in three]
    g["three_are_algebras"] = all(mm3(a, b) in s for s in sets3 for a in s for b in s)
    o2, o3 = orbits(two, GL3), orbits(three, GL3)
    g["gl3_orbits_dim2"] = sorted(n for _, n in o2) == [21, 24, 28, 42, 56, 84]
    g["gl3_orbits_dim3"] = sorted(n for _, n in o3) == [7, 7, 8, 21, 28, 28, 84]
    classes = {}
    ok_identity = ok_closed = ok_cover = ok_lift = ok_aot = True
    for spec in m100.shard_specs(shard):
        kb = kbar(spec)
        grp = sorted(kb)
        ok_identity = ok_identity and I3 in kb
        ok_lift = ok_lift and all(g_ok(spec["au"], gq, gg) for gq, gg in kb.items())
        closed = all(mm3(a, b) in kb for a in grp for b in grp)
        ok_closed = ok_closed and closed
        r2, r3 = orbits(two, grp), orbits(three, grp)
        ok_cover = ok_cover and (sum(n for _, n in r2), sum(n for _, n in r3)) == (255, 183)
        ok_aot = ok_aot and a_of_t(spec["au"], I3) == spec["au"] and a_of_t(spec["au"], 0) == 0
        classes[spec["name"]] = {"kbar_order": len(grp), "kbar": grp, "closed": closed,
                                 "dim3": [[basis_of(s), n] for s, n in r3],
                                 "dim2": [[basis_of(s), n] for s, n in r2],
                                 "instances": 1 + len(r2) + len(r3)}
    g["kbar_identity"] = ok_identity
    g["kbar_lifts_checked"] = ok_lift
    g["kbar_closed"] = ok_closed
    g["orbits_cover"] = ok_cover
    g["a_of_t_I_is_au"] = ok_aot
    spec = m100.spec_of(*m100.CONTROLS[shard][0])
    ref, _, _ = m101.build(spec, "sweep")
    h_ref, n_ref = m100.clause_hash(ref), len(ref.clauses)
    del ref
    cases = [case_t1(), case_t2(J3), case_t3(*basis_of(three[0]))]
    want = {"t1": (60, 70), "t2": (30, 23), "t3": (0, 0)}
    info = {"spec": spec["name"]}
    ok_counts = ok_prefix = True
    for case in cases:
        cnf, _, counts = build(spec, case, "sweep")
        prefix = sa.CNF()
        prefix.clauses = cnf.clauses[:n_ref]
        ok_prefix = ok_prefix and counts["m101_clauses"] == n_ref and m100.clause_hash(prefix) == h_ref
        ok_counts = ok_counts and (counts["maps"], counts["in_x1_extra"],
                                   counts["case_two_extra"]) == (128,) + want[case["kind"]]
        info[case_label(case)] = dict(counts, clauses=len(cnf.clauses))
        del cnf, prefix
    g["m101_prefix"] = ok_prefix
    g["added_counts"] = ok_counts
    with open(m101.__file__, "rb") as f:
        info["m101_sha256"] = hashlib.sha256(f.read()).hexdigest()
    info["graded"] = g
    info["gl3_orbits"] = {"dim2": [[basis_of(s), n] for s, n in o2],
                          "dim3": [[basis_of(s), n] for s, n in o3]}
    info["classes"] = classes
    with open(os.path.join(out_dir, f"m102{shard}_check.json"), "w") as f:
        json.dump(info, f, indent=1)
    bad = sorted(k for k, v in g.items() if not v)
    orders = {}
    for c in classes.values():
        orders[c["kbar_order"]] = orders.get(c["kbar_order"], 0) + 1
    total = sum(c["instances"] for c in classes.values())
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} kbar_orders "
          f"{json.dumps(orders, sort_keys=True)} instances {total} pilot "
          f"{classes[m100.spec_of(*PILOT[shard])['name']]['instances']}", flush=True)


def control_list(shard):
    two, three = t_spaces()
    if shard == "a":
        return [((0, 0), case_t1(), "relax"), ((0, 0), case_t2(J3), "relax_n"),
                ((3, 0), case_t1(), "relax")]
    return [((9, 0), case_t1(), "relax"), ((11, 0), case_t1(), "relax"),
            ((11, 0), case_t3(*basis_of(three[0])), "relax_n")]


def run_control(shard, cap, out_dir):
    counts = {}
    for (pi, ci), case, mode in control_list(shard):
        row = solve_one(m100.spec_of(pi, ci), case, mode, cap, out_dir, "control")
        append_row(out_dir, shard, row)
        key = f"{case['kind']} {mode} {row['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY control {shard} {json.dumps(counts, sort_keys=True)} cap {cap}", flush=True)


def run_sweep(shard, cap, out_dir):
    counts, by_d = {}, {}
    for spec in m100.shard_specs(shard):
        row = solve_one(spec, case_t1(), "sweep", cap, out_dir, "sweep")
        append_row(out_dir, shard, row)
        counts[row["status"]] = counts.get(row["status"], 0) + 1
        key = f"d{spec['dmeet']}"
        by_d.setdefault(key, {})
        by_d[key][row["status"]] = by_d[key].get(row["status"], 0) + 1
    print(f"SUMMARY sweep {shard} {json.dumps(counts, sort_keys=True)} by_d "
          f"{json.dumps(by_d, sort_keys=True)} cap {cap}", flush=True)


def run_pilot(shard, cap, minutes, out_dir):
    spec = m100.spec_of(*PILOT[shard])
    cases = class_cases(spec)[1:]
    start = time.time()
    counts, skipped = {}, 0
    for case in cases:
        if time.time() - start > minutes * 60:
            skipped += 1
            continue
        row = solve_one(spec, case, "sweep", cap, out_dir, "pilot")
        append_row(out_dir, shard, row)
        key = f"{case['kind']} {row['status']}"
        counts[key] = counts.get(key, 0) + 1
    with open(os.path.join(out_dir, f"m102{shard}_pilot.json"), "w") as f:
        json.dump({"class": spec["name"], "cases": len(cases), "skipped": skipped,
                   "counts": counts}, f, indent=1)
    print(f"SUMMARY pilot {shard} {spec['name']} cases {len(cases)} skipped {skipped} "
          f"{json.dumps(counts, sort_keys=True)} cap {cap}", flush=True)


def grade(shard, out_dir):
    g = {}
    chk = m100.load(out_dir, f"m102{shard}_check.json")
    if chk is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    rows = m100.load(out_dir, f"m102{shard}_rows.json") or []
    sweep = [r for r in rows if r["part"] == "sweep"]
    g["sweep_complete"] = sorted(r["instance"] for r in sweep) == sorted(
        inst_name(s, case_t1()) for s in m100.shard_specs(shard))
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g["verified_" + r["instance"] + "_" + r["mode"]] = bool(r.get("verified"))
    if shard == "a":
        known = [r for r in rows if r["part"] == "control" and r["kind"] == "t2"]
        g["known_t2_control_sat"] = bool(known) and all(
            r["status"] == "SAT" and r.get("verified") for r in known)
    pilot = m100.load(out_dir, f"m102{shard}_pilot.json")
    return {"graded": g,
            "sweep": {r["instance"]: [r["status"], r["wall_seconds"], r["dmeet"]] for r in sweep},
            "control": {r["instance"] + "_" + r["mode"]: [r["status"], r["wall_seconds"]]
                        for r in rows if r["part"] == "control"},
            "pilot": {r["instance"]: [r["status"], r["wall_seconds"]]
                      for r in rows if r["part"] == "pilot"},
            "pilot_skipped": None if pilot is None else pilot["skipped"],
            "unsat": sorted(r["instance"] for r in rows
                            if r["part"] != "control" and r["status"] == "UNSAT")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "control", "sweep", "pilot", "grade", "child"],
                    default="check")
    ap.add_argument("--shard", choices=sorted(m100.SHARDS), default="a")
    ap.add_argument("--cap-seconds", type=float, default=120.0)
    ap.add_argument("--pilot-minutes", type=float, default=40.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--case")
    ap.add_argument("--mode", choices=MODES, default="sweep")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), json.loads(args.case), args.mode, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "control":
        run_control(args.shard, args.cap_seconds, args.out_dir)
    elif args.part == "sweep":
        run_sweep(args.shard, args.cap_seconds, args.out_dir)
    elif args.part == "pilot":
        run_pilot(args.shard, args.cap_seconds, args.pilot_minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        with open(os.path.join(args.out_dir, f"m102{args.shard}_grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        st, pt = {}, {}
        for s, _, _ in out["sweep"].values():
            st[s] = st.get(s, 0) + 1
        for s, _ in out["pilot"].values():
            pt[s] = pt.get(s, 0) + 1
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} "
              f"failed {bad[:12]} sweep {json.dumps(st, sort_keys=True)} pilot "
              f"{json.dumps(pt, sort_keys=True)} skipped {out['pilot_skipped']} control "
              f"{json.dumps(out['control'], sort_keys=True)} unsat {out['unsat']}", flush=True)


if __name__ == "__main__":
    main()
