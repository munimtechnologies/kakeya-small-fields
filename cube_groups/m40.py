# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m40: Case B at rank 4 for t = 7 and dim V = 9 (notes/a26.md), an exact SAT search split by
the shapes of Proposition 27 and, in shape (c), by the plane of Corollary 51.

Setting and encoding as in case_b.py and case_b_shapes.py. By Proposition 29(b) (notes/a24.md) an
element u of rank 4 in an anisotropic system with t = 7 and dim V = 9 has k = 3; in Case B,
P = beta(u, V) is a hyperplane missing x0 and N = U+ = ker phi has dimension 3. Lemma 37 of
notes/case-b-shapes.md (with Lemma 35 of notes/case-b.md) puts u in one of the forms c, d1, d2c0,
d2c1 at (t, k) = (7, 3); both lemmas hold for every t. Lemma 42 rules out d1 by hand for every t.

Shape (c) is split once more (Lemma 81 of notes/a26.md). By Corollary 51, X_1 n R contains a plane
Q of X_1 = span(e_0, e_1, e_2). Base changes of (v_1, v_2) act on Y = span(e_1, e_2) by GL_2(F_2)
and fix e_0, and the 7 planes of X_1 fall into 3 orbits: Y itself, the 3 planes through e_0, and
the 3 other planes. With q_1, q_2 a basis of the representative, A_u P = R gives p_1, p_2 in P
with A_u p_i = q_i, independent of Y, so they can be taken as e_3, e_4: the form also fixes
A_u e_3 = q_1 and A_u e_4 = q_2 (14 unit clauses).

    cY   Q = Y = span(e_1, e_2)            A_u e_3 = e_1,        A_u e_4 = e_2
    cX   Q = span(e_0, e_1)                A_u e_3 = e_0,        A_u e_4 = e_1
    cG   Q = span(e_0 + e_1, e_2)          A_u e_3 = e_0 + e_1,  A_u e_4 = e_2

Controls: case_b's (t, k) = (2, 1) example must be SAT; form c at (3, 2) and (4, 2) UNSAT (A(3) = 3,
A(4) = 4); forms d1, d2c0, d2c1 at (6, 3) UNSAT (Lemma 42, Corollary 22, job m12); form d1 at (7, 3)
UNSAT (Lemma 42).

Parts: selfcheck (pure Python), solve --inst NAME (needs python-sat), grade (the pre-registered
predictions of m40/predictions.md).

Usage: python m40.py --part selfcheck|solve|grade [--inst NAME] [--budget-minutes 5] [--out-dir DIR]
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

T, K = 7, 3
DV = T + K - 1
Q_REPS = {"cY": (2, 4), "cX": (1, 2), "cG": (3, 4)}
Q_ORBIT_SIZES = {"cY": 1, "cX": 3, "cG": 3}
CASE_B_UNITS = T + T * K + (DV - 1) * T          # 84
SHAPE_UNITS = 63
Q_UNITS = 2 * T

CONTROLS = {"cb_t2_k1": "SAT", "sh_t3_k2_c": "UNSAT", "sh_t4_k2_c": "UNSAT",
            "sh_t6_k3_d1": "UNSAT", "sh_t6_k3_d2c0": "UNSAT", "sh_t6_k3_d2c1": "UNSAT",
            "sh_t7_k3_d1": "UNSAT"}
EXPLORATORY = ("sh_t7_k3_d2c0", "sh_t7_k3_d2c1", "sh_t7_k3_c_cY", "sh_t7_k3_c_cX",
               "sh_t7_k3_c_cG")


# ---------- the planes of X_1 (Lemma 81) ----------

def gl2_on_y():
    """The 6 maps of X_1 = span(e_0, e_1, e_2) that fix e_0 and act on Y by GL_2(F_2), as
    (image of e_1, image of e_2)."""
    out = []
    for a, b in itertools.product((2, 4, 6), repeat=2):
        if a != b:
            out.append((a, b))
    return out


def apply_y(g, x):
    out = x & 1
    if x & 2:
        out ^= g[0]
    if x & 4:
        out ^= g[1]
    return out


def planes():
    vecs = range(1, 8)
    out = set()
    for a, b in itertools.combinations(vecs, 2):
        out.add(frozenset({0, a, b, a ^ b}))
    return sorted(out, key=sorted)


def plane_orbits():
    left = set(planes())
    out = []
    while left:
        p = min(left, key=sorted)
        orb = {frozenset(apply_y(g, x) for x in p) for g in gl2_on_y()}
        out.append(orb)
        left -= orb
    return out


def rep_plane(q):
    a, b = Q_REPS[q]
    return frozenset({0, a, b, a ^ b})


# ---------- the encoding ----------

def encode_cq(q):
    """case_b_shapes.encode_shape(7, 3, 'c') with A_u e_3 = q_1 and A_u e_4 = q_2 fixed."""
    cnf, names = csh.encode_shape(T, K, "c")
    A = names[0]
    for c, want in zip((3, 4), Q_REPS[q]):
        for r in range(T):
            cnf.clauses.append([A[0][r][c]] if (want >> r) & 1 else [-A[0][r][c]])
    return cnf, names


def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


def parse(inst):
    """('cb', t, k, None) | ('sh', t, k, shape) | ('cq', 7, 3, q) from an instance name."""
    parts = inst.split("_")
    t, k = int(parts[1][1:]), int(parts[2][1:])
    if parts[0] == "cb":
        return "cb", t, k, None
    if len(parts) == 5:
        return "cq", t, k, parts[4]
    return "sh", t, k, parts[3]


def in_cq(As, ss, B, q):
    return (csh.in_shape(As, ss, B, T, K, "c")
            and tuple(csh.col(As[0], c, T) for c in (3, 4)) == Q_REPS[q])


# ---------- selfcheck ----------

def selfcheck():
    st = {}
    st["case_b"] = cb.selfcheck(random.Random(61))["graded"]
    st["case_b_shapes"] = csh.selfcheck()["graded"]
    orbs = plane_orbits()
    st["planes"] = len(planes())
    st["plane_orbit_sizes"] = sorted(len(o) for o in orbs)
    st["reps_in_orbits"] = {q: next(len(o) for o in orbs if rep_plane(q) in o) for q in Q_REPS}
    st["reps_distinct_orbits"] = len({next(i for i, o in enumerate(orbs) if rep_plane(q) in o)
                                      for q in Q_REPS}) == 3
    n_base = len(sa.encode(T, DV, echelon=False)[0].clauses)
    st["units"] = {}
    st["consistent"] = {}
    for shape in csh.SHAPES:
        cnf = csh.encode_shape(T, K, shape)[0]
        st["units"][shape] = len(cnf.clauses) - n_base
        st["consistent"][shape] = units_consistent(cnf)
    for q in Q_REPS:
        cnf = encode_cq(q)[0]
        st["units"]["c_" + q] = len(cnf.clauses) - n_base
        st["consistent"]["c_" + q] = units_consistent(cnf)
        st["cnf_vars"], st["cnf_clauses"] = cnf.nv, len(cnf.clauses)
    want = {s: CASE_B_UNITS + SHAPE_UNITS for s in csh.SHAPES}
    want.update({"c_" + q: CASE_B_UNITS + SHAPE_UNITS + Q_UNITS for q in Q_REPS})
    st["graded"] = {
        "case_b": all(st["case_b"].values()),
        "case_b_shapes": all(st["case_b_shapes"].values()),
        "planes": st["planes"] == 7 and st["plane_orbit_sizes"] == [1, 3, 3],
        "reps": st["reps_distinct_orbits"] and st["reps_in_orbits"] == Q_ORBIT_SIZES,
        "units": st["units"] == want,
        "consistent": all(st["consistent"].values())}
    return st


# ---------- solving ----------

def child(inst, solver, path):
    from pysat.solvers import Solver
    _, t, k, q = parse(inst)
    cnf, names = encode_cq(q)
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


def solve_cq(inst, solver, budget_seconds, out_dir):
    path = os.path.join(out_dir, inst + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--inst", inst,
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
    _, t, k, q = parse(inst)
    res.update({"t": t, "k": k, "shape": "c", "q": q, "d": t + k - 1, "name": inst,
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, t + k - 1)
        res["verified"] = (sa.is_system(at, sv, t + k - 1, t) and sa.anisotropic(sv)
                           and in_cq(As, ss, B, q))
        res["facts"] = csh.model_facts(As, ss, B, t, k, "c")
    with open(os.path.join(out_dir, inst + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {inst}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve(inst, solver, budget_seconds, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    kind, t, k, extra = parse(inst)
    if kind == "cb":
        return cb.solve(t, k, solver, budget_seconds, out_dir)
    if kind == "sh":
        return csh.solve(t, k, extra, solver, budget_seconds, out_dir)
    return solve_cq(inst, solver, budget_seconds, out_dir)


# ---------- grading (pre-registered in m40/predictions.md) ----------

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
        if (fn.startswith("cb_") or fn.startswith("sh_")) and fn.endswith(".json") \
                and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    for name, want in CONTROLS.items():
        r = results.get(name)
        if r is None:
            continue
        if r["status"] not in ("SAT", "UNSAT"):
            ungraded[name] = r["status"]
            continue
        graded[name] = r["status"] == want and (want == "UNSAT" or bool(r.get("verified")))
    # A verified model of an exploratory instance must have every rank <= 4 (Proposition 29(b)),
    # dim(X_1 n R) >= 2 in shape c (Corollary 51) and rank A_(v_2) = 1 in shape d2 (Lemma 78).
    for name in EXPLORATORY:
        r = results.get(name)
        if r is None or r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= 4
        if r["shape"] == "c":
            graded[name + "_cor51"] = fa.get("dim_X1_cap_R", 0) >= 2
        else:
            graded[name + "_lemma78"] = fa.get("rank_n2") == 1
    status = {n: results[n]["status"] for n in EXPLORATORY if n in results}
    return {"graded": graded, "ungraded": ungraded, "status": status,
            "times": {n: r.get("wall_seconds") for n, r in results.items()},
            "any_sat": any(s == "SAT" for s in status.values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--inst", default="sh_t7_k3_d1")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=5.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.inst, args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        res = solve(args.inst, args.solver, args.budget_minutes * 60, args.out_dir)
        print(f"SUMMARY {res['name']} {res['status']}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat {out['any_sat']} {json.dumps(out['status'], sort_keys=True)}", flush=True)
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
