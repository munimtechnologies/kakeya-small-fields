# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Shape c of Case B at t = 2k - 1 with an element of U+ whose map is 0 (notes/a7.md).

At (t, k) = (7, 4) (dim V = 10, rank A_u = 3), every Case B element is in shape c, with
R = Im A_u inside X_1 = ker A_u (Corollary 31), and U+ has an element v_1 != 0 with sigma(v_1) in Y
and A_(v_1) = 0, so M_1 = 0 (Corollary 32). In the normal form of Lemmas 35, 37 and 39 with that v_1
(X_1 = span(e_0, ..., e_(k-1)); v_1, ..., v_(k-1) in N with sigma(v_j) = e_j; v_(k-1+j) in W with
phi(v_(k-1+j)) = e_j), the hand results give:

    (D), (W), (K) of shape_c3.py, which hold whenever R lies in X_1 (then L = [R] = 0 in Lemma 46;
        (D) says R lies in X_1, which for t = 2k - 1 is weaker than R = X_1)
    (U) beta(v_1, v_(k-1+j)) lies in span(e_1) for 1 <= j <= k - 1     (Lemma 58: U+(v_1) = W)
    (G) A_(v_k) e_1 = 0, where phi(v_k) = e_1                            (Lemma 58: G_y y = 0)

and (M_2, ..., M_(k-1)) is the least tuple of an orbit of shape_c3.kept_orbits(t - k, k - 2) (the
recombinations of Lemma 39 that fix v_1 act on it as in shape_c.orbits). So A(7) <= 9 holds if none
of the 16 CNFs at (7, 4) is satisfiable. (3, 2) and (5, 3) are controls: there dim V = t + k - 1
exceeds A(3) = 3 and A(5) = 5, so every instance must be UNSAT whatever clauses are added.

The selfcheck also checks the step of Corollary 32 that uses Schur's bound (Jacobson 1944): a space
of commuting m x m matrices over F_2 that contains I has dimension at most m, for m = 2 and 3.

Parts: selfcheck (pure Python), solve (every instance at (t, k), each in a child process with a time
budget, under a total budget; needs python-sat), grade (the pre-registered predictions of
m21/predictions.md).

Usage: python a7_c.py --part selfcheck|solve|grade [--t T --k K] [--budget-minutes 9]
                      [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import case_b_shapes as cs
import sat_aniso as sa
import shape_c as sc
import shape_c3 as s3


# ---------- the instances ----------

def reps(t, k):
    """[(orbit index, Ms)] with Ms = (0, M_2, ..., M_(k-1)), one per kept orbit of (M_2, ...)."""
    if t != 2 * k - 1 or k < 2:
        raise ValueError("this search needs t = 2k - 1 and k >= 2")
    if k == 2:
        return [(0, (0,))]
    return [(i, (0,) + tuple(tup)) for i, tup in s3.kept_orbits(t - k, k - 2)]


# ---------- Schur's bound for m <= 3 ----------

def span_set(gens):
    out = {0}
    for g in gens:
        out |= {x ^ g for x in out}
    return out


def commuting_dim_ok(m):
    """True if every space of pairwise commuting m x m matrices that contains I has dimension at
    most m. Checked as: for every m - 1 commuting matrices that are independent together with I,
    every matrix commuting with all of them lies in their span with I."""
    I = sc.identity(m)
    mats = range(1 << (m * m))
    cent = {A: {B for B in mats if sa.mat_mul(A, B, m) == sa.mat_mul(B, A, m)} for A in mats}
    for gens in itertools.combinations(mats, m - 1):
        if sa.rank_f2([I] + list(gens)) != m:
            continue
        if any(b not in cent[a] for a, b in itertools.combinations(gens, 2)):
            continue
        common = set(mats)
        for g in gens:
            common &= cent[g]
        if not common <= span_set([I] + list(gens)):
            return False
    return True


# ---------- the encoding ----------

def add_a7(cnf, names, t, k, Ms):
    """Append (D), (W), (K), (U) and (G) to cnf."""
    s3.add_d3(cnf, names, t, k, Ms)
    A, B = names[0], names[2]
    for j in range(1, k):
        key = (1, s3.w_index(k, j))
        for c in range(t):
            if c != 1:
                cnf.clauses.append([-B[key][c]])
    wk = s3.w_index(k, 1)
    for r in range(k):
        cnf.clauses.append([-A[wk][r][1]])


def extra_count(t, k):
    """Unit clauses that (U) and (G) add."""
    return (k - 1) * (t - 1) + k


def encode_a7(t, k, Ms):
    if t != 2 * k - 1:
        raise ValueError("this search needs t = 2k - 1")
    if len(Ms) != k - 1 or Ms[0] != 0:
        raise ValueError("Ms must be (0, M_2, ..., M_(k-1))")
    cnf, names = sc.encode_split(t, k, Ms)
    add_a7(cnf, names, t, k, Ms)
    return cnf, names


def satisfies_extra(As, B, t, k):
    """(U) and (G) checked directly on coordinates."""
    wk = s3.w_index(k, 1)
    return (all((B[(1, s3.w_index(k, j))] & ~2) == 0 for j in range(1, k))
            and (cs.col(As[wk], 1, t) & ((1 << k) - 1)) == 0)


def satisfies_a7(As, ss, B, t, k, Ms):
    return s3.satisfies_d3(As, ss, B, t, k, Ms) and satisfies_extra(As, B, t, k)


def model_facts(As, ss, B, t, k):
    """What the hand results predict for a model: every rank <= t - k, the facts of Lemma 38 that
    shape_c.model_facts checks, R inside X_1 and A_(v_1) = 0."""
    facts = sc.model_facts(As, ss, B, t, k)
    facts["R_in_X1"] = all((cs.col(As[0], c, t) >> k) == 0 for c in range(t))
    facts["A_v1_zero"] = As[1] == 0
    return facts


# ---------- selfcheck ----------

def selfcheck():
    counts = {f"{t},{k}": len(reps(t, k)) for t, k in ((3, 2), (5, 3), (7, 4))}
    all_reps = [(t, k, Ms) for t, k in ((3, 2), (5, 3), (7, 4)) for _, Ms in reps(t, k)]
    st = {"counts": counts, "indices_7_4": [i for i, _ in reps(7, 4)],
          "schur_2": commuting_dim_ok(2), "schur_3": commuting_dim_ok(3)}
    # Hand counts: (3, 2) has the single instance M_1 = 0; (5, 3) one per singular class of
    # M_2(F_2) (0, the nilpotent class, diag(0, 1)); (7, 4) the 16 kept pair orbits of job m18.
    st["graded"] = {"counts": counts == {"3,2": 1, "5,3": 3, "7,4": 16},
                    "first_is_zero": all(Ms[0] == 0 for _, _, Ms in all_reps),
                    "all_singular": all(s3.all_singular(Ms, t - k) for t, k, Ms in all_reps),
                    "schur_2": st["schur_2"], "schur_3": st["schur_3"]}
    return st


# ---------- solving ----------

def instance_name(t, k, idx):
    return f"a7_t{t}_k{k}_o{idx:02d}"


def child(t, k, Ms, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_a7(t, k, Ms)
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


def solve_one(t, k, idx, Ms, solver, budget_seconds, out_dir):
    d = t + k - 1
    name = instance_name(t, k, idx)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--k",
           str(k), "--ms", ",".join(str(M) for M in Ms), "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "k": k, "d": d, "orbit": idx, "Ms": list(Ms), "name": name,
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and cs.in_shape(As, ss, B, t, k, "c")
                           and sc.satisfies_split(As, t, k, Ms)
                           and satisfies_a7(As, ss, B, t, k, Ms))
        res["facts"] = model_facts(As, ss, B, t, k)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, k, solver, budget_seconds, group_seconds, out_dir):
    """Every instance at (t, k), in order; once the total budget is used up the rest are
    SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    todo = reps(t, k)
    start = time.time()
    counts = {}
    for idx, Ms in todo:
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = {"status": "SKIPPED", "t": t, "k": k, "orbit": idx, "Ms": list(Ms),
                   "name": instance_name(t, k, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(t, k, idx, Ms, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return {"t": t, "k": k, "instances": len(todo), "counts": counts}


# Pre-registered (m21/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
# ERROR are reported and not graded.
CONTROLS = ((3, 2), (5, 3))
EXPLORATORY = ((7, 4),)


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("a7_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {}
    for t, k in CONTROLS + EXPLORATORY:
        status[f"{t},{k}"] = [results.get(instance_name(t, k, i), {}).get("status", "missing")
                              for i, _ in reps(t, k)]
    # Controls: every instance UNSAT (A(3) = 3, A(5) = 5).
    for t, k in CONTROLS:
        for (i, _), s in zip(reps(t, k), status[f"{t},{k}"]):
            name = instance_name(t, k, i)
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    # A verified model anywhere must satisfy Proposition 26(a), Lemma 38, R in X_1, A_(v_1) = 0.
    for name, r in results.items():
        if r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - r["k"]
        graded[name + "_facts"] = all(fa.get(key) for key in
                                      ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e",
                                       "R_in_X1", "A_v1_zero"))
    counts = {key: {s: v.count(s) for s in sorted(set(v))} for key, v in status.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
            "all_unsat_7_4": all(s == "UNSAT" for s in status["7,4"])}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=5)
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--ms", default="")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=9.0)
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        Ms = tuple(int(x) for x in args.ms.split(",") if x)
        child(args.t, args.k, Ms, args.solver, args.child_out)
    elif args.part == "solve":
        out = solve_all(args.t, args.k, args.solver, args.budget_minutes * 60,
                        args.group_minutes * 60, args.out_dir)
        print(f"SUMMARY solve t{args.t} k{args.k} instances {out['instances']} "
              f"{json.dumps(out['counts'], sort_keys=True)}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"all_unsat_7_4 {out['all_unsat_7_4']}", flush=True)
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
