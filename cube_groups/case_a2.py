# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Case A of Question R split by the radical of the form C (notes/case-a-radical.md, Corollary 25), as
an exact SAT search on top of case_a.py.

Setting as in case_a.py: the normal form of Lemma 48 of notes/case-a.md (x0 = e_0, z = e_1, v_0 = u,
phi(v_i) = e_(i-1) for 1 <= i <= t, sigma(v_1) = e_1, A_(v_0) = one orbit representative C of Lemma 49),
and R = Im C. Take the section s(p) = sum of v_(c+1) over the set bits c of p. By Corollary 25 the
radical Rad of C(p, q) = [A_(s(p)) q] in X/R is a plane P of R through e_1 that contains neither e_0
nor e_0 + e_1. For each orbit and each such plane P = span(e_1, r_2) the search adds to the CNF of
case_a.encode_case_a:

    columns  A_(v_j) r in R for 1 <= j <= t and r in (e_1, r_2)       Lemma 51(b): C(r, .) = 0
    coset    sigma(v_1 + s(r)) in P, not 0 and not r, for r in P       Lemma 51(d), (f)
    closed   beta(s(e_1), s(r_2)) in P                                 Lemma 51(e)

These hold in every model with Rad = P, so Case A at t exists if and only if one of the instances is
satisfiable (Lemmas 48 to 51, Corollary 25). They are consequences of (*): they remove no model, and
only give the solver facts it would otherwise have to find. A SAT answer counts only with a model that
passes the brute-force check of (*) and anisotropy.

Matrices are t^2-bit masks with entry (r, c) at bit t r + c, as in sat_aniso.py.

Parts: selfcheck (pure Python: the planes against hand counts), solve (every (orbit, plane) at t,
each in a child process with a time budget, under a total budget; needs python-sat; --orbits picks
some orbits only), grade (the pre-registered predictions of m16/predictions.md).

Usage: python case_a2.py --part selfcheck|solve|grade [--t T] [--orbits 0,3] [--budget-minutes 6]
                         [--group-minutes 140] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import case_a as ca
import sat_aniso as sa

E0, E1 = 1, 2


def span(gens):
    out = {0}
    for g in gens:
        out |= {x ^ g for x in out}
    return out


def image(A, t):
    return span([sa.mat_apply(A, 1 << c, t) for c in range(t)])


def planes(Au, t):
    """The planes P of Im Au with e_1 in P and e_0, e_0 + e_1 not in P, as the sorted list of their
    second basis vectors r_2 (the least vector of P outside span(e_1))."""
    R = image(Au, t)
    out = set()
    for r in R:
        if r in (0, E0, E1, E0 ^ E1):
            continue
        P = frozenset((0, E1, r, r ^ E1))
        if E0 in P or E0 ^ E1 in P:
            continue
        out.add(min(r, r ^ E1))
    return sorted(out)


def lift(p, t):
    """s(p) as a bitmask over v_0, ..., v_t: v_(c+1) for each set bit c of p."""
    return sum(1 << (c + 1) for c in range(t) if (p >> c) & 1)


# Hand counts (notes/case-a-radical.md): R contains e_1; if e_0 is not in R (d = 1) the planes of R
# through e_1 are 3 and all miss e_0 and e_0 + e_1; if e_0 is in R (d = 2) one of the 3 is span(e_0, e_1),
# leaving 2. For t = 4, R is itself a plane: 1 for d = 1, 0 for d = 2; for t = 3, R is a line.
HAND_PLANES = {3: 0, 4: 2, 5: 5 * 3 + 4 * 2}


# ---------- the added constraints ----------

def value_vars(cnf, names, h, t):
    """Variables equal to the bits of sigma(sum of v_i over the set bits i of h)."""
    S, B = names[1], names[2]
    idx = [i for i in range(h.bit_length()) if (h >> i) & 1]
    return [cnf.xor_def([S[i][r] for i in idx]
                        + [B[(i, k)][r] for i, k in itertools.combinations(idx, 2)])
            for r in range(t)]


def beta_vars(cnf, names, h1, h2, t):
    """Variables equal to the bits of beta(sum over h1 of v_i, sum over h2 of v_k)."""
    B = names[2]
    pairs = [(min(i, k), max(i, k)) for i in range(h1.bit_length()) if (h1 >> i) & 1
             for k in range(h2.bit_length()) if (h2 >> k) & 1 and k != i]
    return [cnf.xor_def([B[key][r] for key in pairs]) for r in range(t)]


def in_subspace(cnf, ys, basis, t):
    """The vector with bits ys lies in span(basis)."""
    for g in sa.nullspace(list(basis), t):
        cnf.xor_eq([ys[r] for r in range(t) if (g >> r) & 1], 0)


def add_columns(cnf, names, t, R_basis, j, r):
    """A_(v_j) r lies in span(R_basis)."""
    A = names[0]
    for g in sa.nullspace(list(R_basis), t):
        cnf.xor_eq([A[j][row][c] for row in range(t) if (g >> row) & 1
                    for c in range(t) if (r >> c) & 1], 0)


def add_coset(cnf, names, t, r2, r):
    """sigma(v_1 + s(r)) lies in P = span(e_1, r_2) and is neither 0 nor r."""
    ys = value_vars(cnf, names, (1 << 1) ^ lift(r, t), t)
    in_subspace(cnf, ys, (E1, r2), t)
    cnf.clauses.append(list(ys))
    cnf.clauses.append([-ys[b] if (r >> b) & 1 else ys[b] for b in range(t)])


def add_closed(cnf, names, t, r2):
    """beta(s(e_1), s(r_2)) lies in P = span(e_1, r_2)."""
    in_subspace(cnf, beta_vars(cnf, names, lift(E1, t), lift(r2, t), t), (E1, r2), t)


def add_radical(cnf, names, t, Au, r2):
    R_basis = sa.independent([sa.mat_apply(Au, 1 << c, t) for c in range(t)])
    for j in range(1, t + 1):
        for r in (E1, r2):
            add_columns(cnf, names, t, R_basis, j, r)
    for r in sorted(span([E1, r2])):
        add_coset(cnf, names, t, r2, r)
    add_closed(cnf, names, t, r2)


def encode_case_a2(t, Au, r2):
    cnf, names = ca.encode_case_a(t, Au)
    add_radical(cnf, names, t, Au, r2)
    return cnf, names


def conditions(As, ss, B, t, Au, r2):
    """The added constraints, checked directly on coordinates (As, ss, B)."""
    _, sv = sa.tables(As, ss, B, t + 1)
    R, P = image(Au, t), span([E1, r2])
    ys = {r: sv[(1 << 1) ^ lift(r, t)] for r in sorted(P)}
    a, b = lift(E1, t), lift(r2, t)
    return {"columns": all(sa.mat_apply(As[j], r, t) in R for j in range(1, t + 1)
                           for r in (E1, r2)),
            "coset": all(y in P and y not in (0, r) for r, y in ys.items()),
            "closed": sv[a ^ b] ^ sv[a] ^ sv[b] in P}


# ---------- selfcheck ----------

def instances(t, orbit_filter=None):
    """[(orbit index, Au, r_2)] in order."""
    out = []
    for idx, (Au, _) in enumerate(ca.orbits(t)):
        if orbit_filter is not None and idx not in orbit_filter:
            continue
        out += [(idx, Au, r2) for r2 in planes(Au, t)]
    return out


def selfcheck():
    st = {"planes_total": {}, "planes_by_orbit": {}, "d_by_orbit": {}, "plane_facts": True}
    for t in (3, 4, 5):
        orb = ca.orbits(t)
        st["planes_total"][str(t)] = len(instances(t))
        st["planes_by_orbit"][str(t)] = [len(planes(A, t)) for A, _ in orb]
        st["d_by_orbit"][str(t)] = [ca.invariants(A, t)[0] for A, _ in orb]
        for A, _ in orb:
            R = image(A, t)
            for r2 in planes(A, t):
                P = span([E1, r2])
                if not (len(P) == 4 and P <= R and E0 not in P and E0 ^ E1 not in P):
                    st["plane_facts"] = False
    by5, d5 = st["planes_by_orbit"]["5"], st["d_by_orbit"]["5"]
    st["graded"] = {
        "planes_total": all(st["planes_total"][str(t)] == HAND_PLANES[t] for t in HAND_PLANES),
        "planes_by_d_t5": all(n == {1: 3, 2: 2}[d] for n, d in zip(by5, d5)),
        "planes_by_d_t4": all(n == {1: 1, 2: 0}[d] for n, d in
                              zip(st["planes_by_orbit"]["4"], st["d_by_orbit"]["4"])),
        "plane_facts": st["plane_facts"]}
    return st


# ---------- solving ----------

def instance_name(t, idx, r2):
    return f"cb_t{t}_o{idx:02d}_p{r2:02d}"


def child(t, Au, r2, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_case_a2(t, Au, r2)
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


def solve_one(t, idx, Au, r2, solver, budget_seconds, out_dir):
    d = t + 1
    name = instance_name(t, idx, r2)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--au",
           str(Au), "--r2", str(r2), "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "d": d, "orbit": idx, "Au": Au, "r2": r2,
                "invariants": list(ca.invariants(Au, t)), "name": name,
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and ca.in_normal_form(As, ss, B, t, Au))
        res["facts"] = ca.model_facts(As, ss, B, t)
        res["conditions"] = conditions(As, ss, B, t, Au, r2)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, solver, budget_seconds, group_seconds, out_dir, orbit_filter=None):
    """Every (orbit, plane) at t, in order; once the total budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    todo = instances(t, orbit_filter)
    for idx, Au, r2 in todo:
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = {"status": "SKIPPED", "t": t, "orbit": idx, "Au": Au, "r2": r2,
                   "name": instance_name(t, idx, r2)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(t, idx, Au, r2, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return {"t": t, "instances": len(todo), "counts": counts}


# Pre-registered (m16/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
# ERROR are reported and not graded.
CONTROLS = (4,)
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
        if fn.startswith("cb_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {}
    for t in CONTROLS + EXPLORATORY:
        status[str(t)] = {r["name"]: r["status"] for r in results.values() if r["t"] == t}
    # Controls: every instance at t = 4 UNSAT (Corollary 25(b), Proposition 25, A(4) = 4).
    for t in CONTROLS:
        for name, s in sorted(status[str(t)].items()):
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    # A verified model anywhere must satisfy Proposition 25, Lemma 32 and the added constraints.
    for name, r in results.items():
        if r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - 2
        graded[name + "_lemma32"] = all(fa.get(key) for key in ("phi_onto", "ker_A_u", "A_v"))
        graded[name + "_conditions"] = all((r.get("conditions") or {"none": False}).values())
    counts = {key: {s: list(v.values()).count(s) for s in sorted(set(v.values()))}
              for key, v in status.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    by_orbit = {}
    for r in results.values():
        if r["t"] == 5:
            by_orbit.setdefault(str(r["orbit"]), []).append(r["status"])
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
            "t5_by_orbit": by_orbit,
            "all_unsat_5": bool(status["5"]) and all(s == "UNSAT" for s in status["5"].values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=4)
    ap.add_argument("--au", type=int, default=0)
    ap.add_argument("--r2", type=int, default=0)
    ap.add_argument("--orbits", default="")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=6.0)
    ap.add_argument("--group-minutes", type=float, default=140.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    orbit_filter = {int(x) for x in args.orbits.split(",") if x.strip()} or None
    if args.part == "child":
        child(args.t, args.au, args.r2, args.solver, args.child_out)
    elif args.part == "solve":
        out = solve_all(args.t, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir, orbit_filter)
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
