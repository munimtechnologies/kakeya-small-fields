# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Shape c of Case B at t = 2k with only the block of A_u fixed: an ablation of jobs m18 and m19
(notes/a6.md).

Jobs m18 (shape_c3.py, d = k) and m19 (shape_c4.py, d = k - 1) took the CNF of
shape_c.encode_split (the CNF of job m13) and appended consequences of (*) proved by hand:
(W), (K) and the orbit filter of Corollary 23(a) in m18; (B2), (W2), (Q2), (K2), (T2), (J2) and the
filters of Corollaries 23(a) and 28 in m19. Every one of their t = 6 instances came back UNSAT, so
A(6) <= 7 rests on those hand proofs. Here every instance appends only

    (Z) the lower-right m x m block of A_u is a fixed matrix Abar of rank <= 1 (unit clauses)

and nothing is filtered: Abar = 0 for every orbit of commuting tuples (shape_c.orbits; this is d = k,
R = X_1, and (Z) is (D) of shape_c3.py), and for rank 1 every orbit of triples (shape_c4.triples;
this is d = k - 1 by Lemma 56(a), and (Z) is (D2) of shape_c4.py). At t = 6, d is 2 or 3
(Proposition 27(c4)), so these instances cover shape c using only the normal form (Lemmas 35, 37,
38, 39), Lemma 56(a) and (c) and Proposition 27(c4). An UNSAT answer here does not need
Proposition 27(c2), Lemma 38(e), Lemma 46, Lemma 54 or Corollaries 23 and 28. A verified SAT answer
at t = 6 would be an anisotropic system with dim V = 8 and would show that one of those hand results
is false.

Parts: selfcheck (pure Python: instance counts), solve (every instance at (t, k), in passes with
growing time budgets, under a total budget; needs python-sat), grade (the pre-registered predictions
of m20/predictions.md).

Usage: python ablate_c.py --part selfcheck|solve|grade [--t T --k K] [--blocks zero|rank1|all]
                          [--budgets 8,60] [--group-minutes 150] [--names-file F] [--out-dir DIR]
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
import shape_c4 as s4


# ---------- the instances ----------

def instances(m, r):
    """[(orbit index, least tuple, Abar)]: Abar = 0 for every orbit of commuting r-tuples, then
    every orbit of triples with Abar of rank 1."""
    out = [(idx, tup, 0) for idx, (tup, _, _) in enumerate(sc.orbits(m, r))]
    out += [(idx, tup, Ab) for idx, tup, Ab in s4.triples(m, r)]
    return out


# ---------- the encoding ----------

def add_block(cnf, names, t, k, Ab):
    """(Z): unit clauses fixing the lower-right block of A_u to Ab."""
    A = names[0]
    m = t - k
    for l in range(m):
        for c in range(m):
            v = A[0][k + l][k + c]
            cnf.clauses.append([v] if (Ab >> (m * l + c)) & 1 else [-v])


def encode_z(t, k, Ms, Ab):
    if t != 2 * k:
        raise ValueError("the block of A_u is square only when t = 2k")
    if sa.rank_f2(sa.rows_of(Ab, t - k)) > 1:
        raise ValueError("Abar_u must have rank <= 1")
    cnf, names = sc.encode_split(t, k, Ms)
    add_block(cnf, names, t, k, Ab)
    return cnf, names


def satisfies_z(As, t, k, Ab):
    return s4.block(As[0], t, k) == Ab


def model_facts(As, ss, B, t, k, Ab):
    """Proposition 26(a) and Lemma 38 (shape_c.model_facts), the block, and d."""
    facts = sc.model_facts(As, ss, B, t, k)
    facts["block_is_Ab"] = s4.block(As[0], t, k) == Ab
    R = sa.independent([cs.col(As[0], c, t) for c in range(t)])
    X1 = [1 << c for c in range(k)]
    facts["dim_X1_cap_R"] = len(X1) + len(R) - sa.rank_f2(X1 + R)
    return facts


# ---------- selfcheck ----------

def selfcheck():
    # Hand counts: 6 similarity classes in M_2(F_2) (0, I, the nilpotent one, I + nilpotent,
    # diag(0, 1), the companion matrix of x^2 + x + 1); 38 orbits of commuting pairs in M_3(F_2)
    # (shape-c.md); 26 and 569 orbits of triples (job m19's selfcheck).
    st = {}
    for m, r, orb, trip in ((2, 1, 6, 26), (3, 2, 38, 569)):
        inst = instances(m, r)
        zero = sum(1 for x in inst if x[2] == 0)
        st[f"{m},{r}"] = {"instances": len(inst), "zero_block": zero, "rank1": len(inst) - zero,
                          "expected": [orb, trip]}
    st["graded"] = {key: v["zero_block"] == v["expected"][0] and v["rank1"] == v["expected"][1]
                    for key, v in st.items()}
    return st


# ---------- solving ----------

def instance_name(t, k, idx, Ab):
    return f"z_t{t}_k{k}_o{idx:02d}_a{Ab:03d}"


def child(t, k, Ms, Ab, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_z(t, k, Ms, Ab)
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
    idx, Ms, Ab = inst
    d = t + k - 1
    name = instance_name(t, k, idx, Ab)
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
    res.update({"t": t, "k": k, "d": d, "orbit": idx, "Ms": list(Ms), "Ab": Ab, "name": name,
                "pass": pass_no, "budget_seconds": round(budget_seconds),
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and cs.in_shape(As, ss, B, t, k, "c")
                           and sc.satisfies_split(As, t, k, Ms)
                           and satisfies_z(As, t, k, Ab))
        res["facts"] = model_facts(As, ss, B, t, k, Ab)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, k, solver, budgets, group_seconds, out_dir, names_only=None, blocks="all"):
    """Every instance at (t, k) whose block is of the given kind (zero, rank1 or all), in passes:
    pass p gives each instance that is still undecided budgets[p] seconds, under the total budget.
    Instances not reached in pass 0 are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    insts = [x for x in instances(t - k, k - 1)
             if (blocks == "all" or (blocks == "zero") == (x[2] == 0))
             and (names_only is None or instance_name(t, k, x[0], x[2]) in names_only)]
    start = time.time()
    results = {}
    pending = list(insts)
    for p, budget in enumerate(budgets):
        nxt = []
        for inst in pending:
            name = instance_name(t, k, inst[0], inst[2])
            left = group_seconds - (time.time() - start)
            if left < 1:
                if p == 0:
                    res = {"status": "SKIPPED", "t": t, "k": k, "orbit": inst[0],
                           "Ms": list(inst[1]), "Ab": inst[2], "name": name}
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
    return {"t": t, "k": k, "blocks": blocks, "instances": len(insts), "counts": counts,
            "undecided": [instance_name(t, k, x[0], x[2]) for x in pending]}


# Pre-registered (m20/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
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
        if fn.startswith("z_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {}
    for t, k in CONTROLS + EXPLORATORY:
        names = [instance_name(t, k, x[0], x[2]) for x in instances(t - k, k - 1)]
        status[f"{t},{k}"] = {n: results.get(n, {}).get("status", "missing") for n in names}
    for t, k in CONTROLS:
        for name, s in status[f"{t},{k}"].items():
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    # Jobs m18 and m19 found every (6, 3) instance of theirs UNSAT; a SAT here would contradict a
    # hand result they used (if verified) or the encoding (if not).
    graded["no_sat_6_3"] = "SAT" not in status["6,3"].values()
    for name, r in results.items():
        if r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - r["k"]
        graded[name + "_facts"] = all(fa.get(key) for key in
                                      ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e",
                                       "block_is_Ab"))
    counts = {key: {s: list(v.values()).count(s) for s in sorted(set(v.values()))}
              for key, v in status.items()}
    by_block = {}
    for name, s in status["6,3"].items():
        key = "zero" if name.endswith("_a000") else "rank1"
        by_block.setdefault(key, {})
        by_block[key][s] = by_block[key].get(s, 0) + 1
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    undecided = {key: [n for n, s in v.items() if s not in ("SAT", "UNSAT")]
                 for key, v in status.items()}
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "by_block_6_3": by_block,
            "times": times, "undecided": undecided,
            "all_unsat_6_3": all(s == "UNSAT" for s in status["6,3"].values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=4)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--ms", default="")
    ap.add_argument("--ab", type=int, default=0)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budgets", default="8,60")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--names-file", default="")
    ap.add_argument("--blocks", choices=["zero", "rank1", "all"], default="all")
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
        out = solve_all(args.t, args.k, args.solver, budgets, args.group_minutes * 60,
                        args.out_dir, names_only, args.blocks)
        print(f"SUMMARY solve t{args.t} k{args.k} blocks {args.blocks} instances "
              f"{out['instances']} {json.dumps(out['counts'], sort_keys=True)} undecided "
              f"{len(out['undecided'])}", flush=True)
        with open(os.path.join(args.out_dir, f"solve_t{args.t}_k{args.k}_{args.blocks}.json"),
                  "w") as f:
            json.dump(out, f, indent=1)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"all_unsat_6_3 {out['all_unsat_6_3']} "
              f"{json.dumps(out['by_block_6_3'], sort_keys=True)}", flush=True)
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
