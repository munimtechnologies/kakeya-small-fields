# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m25: rank 4 in Case B at t = 6, split finer by Lemma 41 (notes/a12.md).

Job m23 ran the 32 classes of M = M_v at (t, k) = (6, 2) through shape_c.py, 5 minutes each, and
decided none of them. Lemma 41 of notes/shape-c.md splits each class further by the orbit of
q = [sigma(w)] under the centraliser C(M) and fixes sigma(w), beta(v, w), A_w on ker A_u and T q
(and T M q); shape_c2.py builds these CNFs for every t. Leaving out M = 0 and M = I (Corollary 36),
this gives 146 instances at t = 6: 124 pairs (M, q), 22 of type i, 22 of type ii and 80 of type
iii, with type ii counted twice. Case B at rank 4 and t = 6 exists iff one of them is satisfiable.

Order of the run: the selfcheck (counts against the hand counts of a12.md); the controls t = 3 and
t = 4 of shape_c2 (3 and 13 instances, UNSAT as A(3) = 3 and A(4) = 4); the 47 instances at t = 5
(UNSAT by Corollary 24 of case-a.md, which this re-checks with M = 0 and M = I included); then the
146 instances at t = 6, round robin over the classes (the first q of every class, then the
second, ...). Each instance runs in a child process that gets (M, q, type, c) on its command line,
so the child does not recompute the centralisers.

Usage: python a6_r4q.py --part controls|solve|grade [--budget-minutes 3] [--group-minutes 150]
                        [--out-dir DIR]
"""
import argparse
import json
import os
import subprocess
import sys
import time

import case_b_shapes as cs
import sat_aniso as sa
import shape_c as sc
import shape_c2 as s2

T = 6
CONTROLS = (3, 4)
CHECK = 5


def todo(t):
    """[(shape_c2 index, (M, q, type, c))] at t. At t = 6, M = 0 and M = I are left out
    (Corollary 36); at t <= 5 every instance is kept."""
    ident = sc.identity(t - 2)
    return [(idx, inst) for idx, inst in enumerate(s2.instances(t))
            if t < 6 or inst[0] not in (0, ident)]


def round_robin(items):
    """Interleave by M: the first instance of every M (classes in their order), then the second,
    and so on."""
    by_m = {}
    for item in items:
        by_m.setdefault(item[1][0], []).append(item)
    groups = list(by_m.values())
    out = []
    for r in range(max((len(g) for g in groups), default=0)):
        out.extend(g[r] for g in groups if r < len(g))
    return out


# ---------- selfcheck (pure Python) ----------

def selfcheck():
    m = T - 2
    ident = sc.identity(m)
    reps = [o[0][0] for o in sc.orbits(m, 1)]
    group = len(sc.gl(m))
    pairs = {M: s2.q_orbits(M, m) for M in reps}
    types = {}
    for M in reps:
        if M in (0, ident):
            continue
        for q, _ in pairs[M]:
            typ = s2.lemma40_type(M, q, m)
            types[typ] = types.get(typ, 0) + 1
    cents = {M: len(s2.centraliser(M, m)) for M in reps}
    orbit_stab = all(sum(s for _, s in pairs[M]) == (1 << m) - 1
                     and all(cents[M] % s == 0 for _, s in pairs[M]) for M in reps)
    kept = todo(T)
    rr = round_robin(kept)
    st = {"classes": len(reps), "group": group,
          "class_sizes_sum": sum(group // c for c in cents.values()),
          "q_orbits_all": sum(len(v) for v in pairs.values()),
          "pairs_kept": sum(len(pairs[M]) for M in reps if M not in (0, ident)),
          "types_kept": types, "instances_all": len(s2.instances(T)),
          "instances_kept": len(kept),
          "pairs_by_class": sorted(len(pairs[M]) for M in reps),
          "controls": {str(t): len(todo(t)) for t in CONTROLS + (CHECK,)}}
    st["graded"] = {
        "classes": len(reps) == 34 and group == 20160,
        "centralisers": all(group % c == 0 for c in cents.values())
        and st["class_sizes_sum"] == 1 << 16,
        "orbit_stabiliser": orbit_stab,
        "q_orbits": st["q_orbits_all"] == 126 and st["pairs_kept"] == 124,
        "types": types == {"i": 22, "ii": 22, "iii": 80},
        "instances": st["instances_all"] == 149 and st["instances_kept"] == 146,
        "round_robin": sorted(rr) == sorted(kept) and len({inst[0] for _, inst in rr[:32]}) == 32,
        "controls": st["controls"] == {"3": 3, "4": 13, "5": 47}}
    return st


# ---------- solving ----------

def child_cmd(t, inst, solver, path):
    M, q, typ, c = inst
    return [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t),
            "--inst", json.dumps([M, q, typ, c]), "--solver", solver, "--child-out", path]


def child(t, inst, solver, path):
    from pysat.solvers import Solver
    M, q, typ, c = inst
    cnf, names = s2.encode_q(t, M, q, typ, c)
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


def solve_one(t, idx, inst, solver, budget_seconds, out_dir):
    d = t + 1
    M, q, typ, c = inst
    name = s2.instance_name(t, idx)
    path = os.path.join(out_dir, name + ".child.json")
    start = time.time()
    try:
        subprocess.run(child_cmd(t, inst, solver, path), timeout=budget_seconds, check=True)
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
                           and s2.satisfies_q(As, ss, B, t, M, q, typ, c))
        res["facts"] = sc.model_facts(As, ss, B, t, 2)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def run(t, items, budget_seconds, group_seconds, out_dir):
    """Each instance in a child process; once the group budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for idx, inst in items:
        left = group_seconds - (time.time() - start)
        if left < 1:
            M, q, typ, c = inst
            res = {"status": "SKIPPED", "t": t, "idx": idx, "M": M, "q": q, "type": typ, "c": c,
                   "name": s2.instance_name(t, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(t, idx, inst, "auto", min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


# ---------- grading ----------

def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("q2_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


# Pre-registered (m25/predictions.md). Graded: the selfcheck; every decided instance at t = 3, 4
# and 5 UNSAT; every SAT answer verified, with ranks <= t - 2, the facts of Lemma 38 and
# dim D >= 1. The 146 instances at t = 6 are exploratory; UNKNOWN, SKIPPED and ERROR are reported,
# not graded.
def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    status = {}
    for t in CONTROLS + (CHECK, T):
        status[str(t)] = {s2.instance_name(t, idx): results.get(s2.instance_name(t, idx), {})
                          .get("status", "missing") for idx, _ in todo(t)}
    for t in CONTROLS + (CHECK,):
        for name, s in status[str(t)].items():
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    for name, r in results.items():
        if r.get("status") != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - 2
        graded[name + "_lemma38"] = all(fa.get(key) for key in
                                        ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e"))
        graded[name + "_d"] = fa.get("dim_D", 0) >= 1
    counts = {t: {s: list(v.values()).count(s) for s in sorted(set(v.values()))}
              for t, v in status.items()}
    by_type = {}
    for idx, (M, q, typ, c) in todo(T):
        s = status[str(T)][s2.instance_name(T, idx)]
        by_type.setdefault(typ, {}).setdefault(s, 0)
        by_type[typ][s] += 1
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    six = list(status[str(T)].values())
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "by_type_6": by_type,
            "times": times,
            "decided_6": sorted(n for n, s in status[str(T)].items() if s in ("SAT", "UNSAT")),
            "all_unsat_6": bool(six) and all(s == "UNSAT" for s in six),
            "any_sat_6": any(s == "SAT" for s in six)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["controls", "solve", "child", "grade"], default="grade")
    ap.add_argument("--t", type=int, default=T)
    ap.add_argument("--inst", default="[]")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=3.0)
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--check-budget-seconds", type=float, default=45.0)
    ap.add_argument("--check-group-minutes", type=float, default=20.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        M, q, typ, c = json.loads(args.inst)
        child(args.t, (M, q, typ, c), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)
        for t in CONTROLS:
            counts = run(t, todo(t), 120, 600, args.out_dir)
            print(f"SUMMARY control t{t} {json.dumps(counts, sort_keys=True)}", flush=True)
        counts = run(CHECK, todo(CHECK), args.check_budget_seconds,
                     args.check_group_minutes * 60, args.out_dir)
        print(f"SUMMARY check t{CHECK} {json.dumps(counts, sort_keys=True)}", flush=True)
    elif args.part == "solve":
        counts = run(T, round_robin(todo(T)), args.budget_minutes * 60,
                     args.group_minutes * 60, args.out_dir)
        print(f"SUMMARY solve t{T} {json.dumps(counts, sort_keys=True)}", flush=True)
    else:
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"counts {json.dumps(out['counts'], sort_keys=True)}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
