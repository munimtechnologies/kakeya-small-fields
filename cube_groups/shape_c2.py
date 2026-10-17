# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Case B with U+ of dimension 2 (k = 2), split by Lemma 41 of notes/shape-c.md.

Setting and encoding as in shape_c.py with k = 2, m = t - 2: u = v_0, v = v_1 (sigma(v) = e_1),
w = v_2 (phi(w) = e_1), x0 = e_0, X_1 = span(e_0, e_1), M = M_v on X/X_1 in the basis e_2, ...,
e_(t-1), q = [sigma(w)] and T[x] = A_u x. Lemma 40 puts every Case B element in one of three types,
and Mq decides which:

    type   Mq        beta(v, w)    T q          also
    i      0         0             e_1
    ii     q         e_0           e_0 + e_1
    iii    other     e_0 + e_1     e_0          T M q = e_1

Lemma 41: if some anisotropic system with dim X = t and dim V = t + 1 has a Case B element of rank
t - 2, it has one in the normal form of shape c (Lemmas 35 and 37) where M is the least matrix of its
similarity class (shape_c.orbits(m, 1)), q is the least vector of its orbit under the centraliser
C(M) of M in GL_m, sigma(w) = c + (q on e_2, ..., e_(t-1)) with c = 0 in types i and iii and
c in {0, e_0} in type ii, beta(v, w), A_w e_0 = e_1, A_w e_1 = beta(v, w) and T q (and T M q) as in
the table. So Case B at (t, 2) exists iff one of the instances below is satisfiable.

Vectors are bit masks (e_r = 1 << r); m x m matrices as in shape_c.py.

Parts: selfcheck (pure Python: centralisers, q-orbits and instance counts against hand counts),
solve (every instance at t, each in a child process with a time budget, under a total budget;
needs python-sat), grade (the pre-registered predictions of m14/predictions.md).

Usage: python shape_c2.py --part selfcheck|solve|grade [--t T] [--budget-minutes 3]
                          [--group-minutes 150] [--out-dir DIR]
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

TYPES = ("i", "ii", "iii")
BETA_VW = {"i": 0, "ii": 1, "iii": 3}
T_Q = {"i": 2, "ii": 3, "iii": 1}
T_MQ_III = 2


# ---------- centralisers, q-orbits, instances ----------

@functools.lru_cache(maxsize=None)
def centraliser(M, m):
    return tuple(g for g in sc.gl(m) if sa.mat_mul(g, M, m) == sa.mat_mul(M, g, m))


@functools.lru_cache(maxsize=None)
def q_orbits(M, m):
    """[(least q, orbit size)] of the non-zero vectors of F_2^m under C(M), sorted."""
    cent = centraliser(M, m)
    left = set(range(1, 1 << m))
    out = []
    while left:
        q = min(left)
        orb = {sa.mat_apply(g, q, m) for g in cent}
        out.append((q, len(orb)))
        left -= orb
    return sorted(out)


def lemma40_type(M, q, m):
    mq = sa.mat_apply(M, q, m)
    if mq == 0:
        return "i"
    if mq == q:
        return "ii"
    return "iii"


def x1_parts(typ):
    return (0, 1) if typ == "ii" else (0,)


@functools.lru_cache(maxsize=None)
def instances(t):
    """[(M, q, type, c)] in a fixed order: class by class, then q, then c."""
    m = t - 2
    out = []
    for (M,), _, _ in sc.orbits(m, 1):
        for q, _ in q_orbits(M, m):
            typ = lemma40_type(M, q, m)
            for c in x1_parts(typ):
                out.append((M, q, typ, c))
    return tuple(out)


# ---------- the encoding ----------

def added_clause_count(t, M, q, typ):
    """Clauses that encode_q adds to shape_c.encode_split: 4t unit clauses (sigma(w), beta(v, w),
    A_w e_0, A_w e_1) and, per row, 2^(p - 1) clauses for a parity equation on p variables."""
    m = t - 2
    n = 4 * t + t * (1 << (bin(q).count("1") - 1))
    if typ == "iii":
        n += t * (1 << (bin(sa.mat_apply(M, q, m)).count("1") - 1))
    return n


def encode_q(t, M, q, typ, c):
    cnf, names = sc.encode_split(t, 2, (M,))
    A, S, B = names[0], names[1], names[2]
    m = t - 2

    def fix(vars_, want):
        for r in range(t):
            cnf.clauses.append([vars_[r]] if (want >> r) & 1 else [-vars_[r]])

    def t_eq(z, want):
        for r in range(t):
            cnf.xor_eq([A[0][r][2 + l] for l in range(m) if (z >> l) & 1], (want >> r) & 1)

    fix(S[2], c | (q << 2))
    fix(B[(1, 2)], BETA_VW[typ])
    fix([A[2][r][0] for r in range(t)], 2)
    fix([A[2][r][1] for r in range(t)], BETA_VW[typ])
    t_eq(q, T_Q[typ])
    if typ == "iii":
        t_eq(sa.mat_apply(M, q, m), T_MQ_III)
    return cnf, names


def satisfies_q(As, ss, B, t, M, q, typ, c):
    """Do the coordinates carry the values that encode_q fixes (on top of shape_c's split)?"""
    m = t - 2

    def t_of(z):
        return sa.combine([cs.col(As[0], 2 + l, t) for l in range(m)], z)

    ok = (ss[2] == c | (q << 2) and B[(1, 2)] == BETA_VW[typ] and cs.col(As[2], 0, t) == 2
          and cs.col(As[2], 1, t) == BETA_VW[typ] and t_of(q) == T_Q[typ])
    if typ == "iii":
        ok = ok and t_of(sa.mat_apply(M, q, m)) == T_MQ_III
    return ok


# ---------- selfcheck ----------

def selfcheck():
    st = {"q_orbits": {}, "instances": {}, "centralisers": {}, "types_3": {}}
    orbit_stab = True
    for m in (1, 2, 3):
        reps = [o[0][0] for o in sc.orbits(m, 1)]
        st["q_orbits"][str(m)] = sum(len(q_orbits(M, m)) for M in reps)
        st["instances"][str(m)] = len(instances(m + 2))
        st["centralisers"][str(m)] = sorted(len(centraliser(M, m)) for M in reps)
        for M in reps:
            orbs = q_orbits(M, m)
            orbit_stab = orbit_stab and sum(s for _, s in orbs) == (1 << m) - 1
            orbit_stab = orbit_stab and all(len(centraliser(M, m)) % s == 0 for _, s in orbs)
    for M in (o[0][0] for o in sc.orbits(3, 1)):
        for q, _ in q_orbits(M, 3):
            typ = lemma40_type(M, q, 3)
            st["types_3"][typ] = st["types_3"].get(typ, 0) + 1
    st["graded"] = {
        "q_orbits": st["q_orbits"] == {"1": 2, "2": 10, "3": 38},
        "instances": st["instances"] == {"1": 3, "2": 13, "3": 47},
        "centralisers": st["centralisers"] == {"1": [1, 1], "2": [1, 2, 2, 3, 6, 6],
                                                "3": [2, 2, 3, 3, 4, 4, 6, 6, 7, 7, 8, 8,
                                                      168, 168]},
        "types_3": st["types_3"] == {"i": 9, "ii": 9, "iii": 20},
        "orbit_stabiliser": orbit_stab}
    return st


# ---------- solving ----------

def instance_name(t, idx):
    return f"q2_t{t}_i{idx:02d}"


def child(t, idx, solver, path):
    from pysat.solvers import Solver
    M, q, typ, c = instances(t)[idx]
    cnf, names = encode_q(t, M, q, typ, c)
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
        As, ss, B = sa.decode(s.get_model(), names, t, t + 1)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_one(t, idx, solver, budget_seconds, out_dir):
    d = t + 1
    M, q, typ, c = instances(t)[idx]
    name = instance_name(t, idx)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t),
           "--idx", str(idx), "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "k": 2, "d": d, "idx": idx, "M": M, "q": q, "type": typ, "c": c,
                "name": name, "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and cs.in_shape(As, ss, B, t, 2, "c")
                           and sc.satisfies_split(As, t, 2, (M,))
                           and satisfies_q(As, ss, B, t, M, q, typ, c))
        res["facts"] = sc.model_facts(As, ss, B, t, 2)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, solver, budget_seconds, group_seconds, out_dir):
    """Every instance at t, in order; once the total budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for idx, (M, q, typ, c) in enumerate(instances(t)):
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = {"status": "SKIPPED", "t": t, "idx": idx, "M": M, "q": q, "type": typ, "c": c,
                   "name": instance_name(t, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(t, idx, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return {"t": t, "instances": len(instances(t)), "counts": counts}


# Pre-registered (m14/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
# ERROR are reported and not graded.
CONTROLS = (3, 4)
EXPLORATORY = (5,)


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("q2_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {str(t): [results.get(instance_name(t, i), {}).get("status", "missing")
                       for i in range(len(instances(t)))] for t in CONTROLS + EXPLORATORY}
    # Controls: every instance UNSAT (A(3) = 3, A(4) = 4).
    for t in CONTROLS:
        for i, s in enumerate(status[str(t)]):
            name = instance_name(t, i)
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    # A verified model anywhere must satisfy Proposition 26(a) and Lemma 38.
    for name, r in results.items():
        if r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - 2
        graded[name + "_lemma38"] = all(fa.get(key) for key in
                                        ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e"))
    counts = {key: {s: v.count(s) for s in sorted(set(v))} for key, v in status.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    undecided = [n for n, r in sorted(results.items())
                 if r["t"] == 5 and r["status"] not in ("SAT", "UNSAT")]
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
            "undecided_5": undecided, "all_unsat_5": all(s == "UNSAT" for s in status["5"])}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=3)
    ap.add_argument("--idx", type=int, default=0)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=3.0)
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.t, args.idx, args.solver, args.child_out)
    elif args.part == "solve":
        out = solve_all(args.t, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY solve t{args.t} instances {out['instances']} "
              f"{json.dumps(out['counts'], sort_keys=True)}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"all_unsat_5 {out['all_unsat_5']}", flush=True)
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
