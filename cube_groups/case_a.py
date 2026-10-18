# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Case A of Question R at rank t - 2 (notes/question-r.md, notes/case-a.md) as an exact SAT search,
split by the orbits of A_u.

Setting and encoding as in sat_aniso.py. Case A at t: an anisotropic system with dim X = t and
dim V = d = t + 1, and an element u of rank t - 2 such that phi = beta(u, .) maps V onto X. Take v
with phi(v) = x0 = sigma(u) and z = sigma(v). Proposition 25 gives ker A_u = span(x0, z), and
z = (I + A_v) z lies in Im(I + A_v), which lies in Im A_u (Lemma 31). Lemma 48 of notes/case-a.md
gives bases of X and V with

    x0 = e_0,  z = e_1,  v_0 = u,  phi(v_i) = e_(i-1) for 1 <= i <= t,  sigma(v_1) = e_1,

A_u e_0 = A_u e_1 = 0, rank A_u = t - 2, e_1 in Im A_u, and A_u any chosen matrix of its orbit under
conjugation by G = {g in GL(X) : g e_0 = e_0, g e_1 = e_1}. So Case A at t exists iff, for one
orbit, the CNF of sat_aniso.encode (without its echelon form) with these values fixed by unit
clauses is satisfiable. With Corollary 24 of notes/case-a.md, UNSAT for every orbit at t = 5 gives
A(5) = 5.

Matrices are t^2-bit masks with entry (r, c) at bit t r + c, as in sat_aniso.py.

Parts: selfcheck (pure Python: the candidate matrices, the group G and the orbits against hand
counts, orbit-stabiliser), solve (every orbit at t, each in a child process with a time budget,
under a total budget; needs python-sat), grade (the pre-registered predictions of
m15/predictions.md).

Usage: python case_a.py --part selfcheck|solve|grade [--t T] [--budget-minutes 12]
                        [--group-minutes 120] [--out-dir DIR]
"""
import argparse
import functools
import itertools
import json
import os
import subprocess
import sys
import time

import sat_aniso as sa


# ---------- the matrices A_u and their orbits ----------

def identity(t):
    return sum(1 << (t * r + r) for r in range(t))


@functools.lru_cache(maxsize=None)
def candidates(t):
    """Every A with A e_0 = A e_1 = 0, rank t - 2 and e_1 in Im A, in increasing order."""
    out = []
    for cols in itertools.product(range(1 << t), repeat=t - 2):
        cols = list(cols)
        if sa.rank_f2(cols) == t - 2 and sa.rank_f2(cols + [2]) == t - 2:
            out.append(sa.from_cols([0, 0] + cols, t))
    return sorted(out)


def generators(t):
    """The transvections I + E_ij (i != j, j >= 2); each is its own inverse, and they generate G."""
    return [identity(t) ^ (1 << (t * i + j)) for j in range(2, t) for i in range(t) if i != j]


@functools.lru_cache(maxsize=None)
def group(t):
    """G as a sorted list, by closure of the generators."""
    gens = generators(t)
    seen = {identity(t)}
    frontier = [identity(t)]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = sa.mat_mul(g, s, t)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return sorted(seen)


def group_order(t):
    """|G| = (2^t - 4)(2^t - 8) ... (2^t - 2^(t-1)): columns 2, ..., t - 1 of g."""
    out = 1
    for j in range(2, t):
        out *= (1 << t) - (1 << j)
    return out


def conj(g, A, t):
    """g A g^-1 for a generator g (g = g^-1)."""
    return sa.mat_mul(sa.mat_mul(g, A, t), g, t)


@functools.lru_cache(maxsize=None)
def orbits(t):
    """[(least matrix, orbit size)] of the candidates under conjugation by G, sorted."""
    gens = generators(t)
    left = set(candidates(t))
    out = []
    while left:
        a = min(left)
        orb = {a}
        frontier = [a]
        while frontier:
            nxt = []
            for A in frontier:
                for g in gens:
                    B = conj(g, A, t)
                    if B not in orb:
                        orb.add(B)
                        nxt.append(B)
            frontier = nxt
        out.append((a, len(orb)))
        left -= orb
    return sorted(out)


def stabiliser(A, t):
    return sum(1 for g in group(t) if sa.mat_mul(g, A, t) == sa.mat_mul(A, g, t))


def kernel_dim(A, t):
    return t - sa.rank_f2(sa.rows_of(A, t))


def invariants(A, t):
    """(d, rank of Abar, Abar^2 == 0, rank A^2, A^3 == 0) with d = dim(X_1 n Im A), X_1 = ker A, and
    Abar the map that A induces on X / X_1 (notes/case-a.md, count of the orbits)."""
    cols = [sa.mat_apply(A, 1 << c, t) for c in range(2, t)]
    d = sum(1 for x in range(1, 4) if sa.rank_f2(cols + [x]) == t - 2)
    d = {0: 0, 1: 1, 3: 2}[d]
    abar = [c >> 2 for c in cols]
    m = t - 2
    Abar = sa.from_cols(abar, m)
    A2 = sa.mat_mul(A, A, t)
    return (d, sa.rank_f2(sa.rows_of(Abar, m)), sa.mat_mul(Abar, Abar, m) == 0,
            sa.rank_f2(sa.rows_of(A2, t)), sa.mat_mul(A2, A, t) == 0)


# Hand counts (notes/case-a.md): number of candidates, |G|, orbit sizes.
HAND = {3: (1, 4, [1]), 4: (42, 96, [6, 12, 24]),
        5: (5880, 10752, [168, 168, 168, 448, 672, 672, 896, 1344, 1344])}
# Orbits with X_1 n Im A of dimension 2 (the rest have dimension 1).
HAND_D2 = {3: 0, 4: 1, 5: 4}


# ---------- the encoding ----------

def wanted_phi(i):
    return 1 << (i - 1)


def encode_case_a(t, Au):
    """sat_aniso.encode (no echelon form, d = t + 1) with the values of the normal form fixed."""
    d = t + 1
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]
    for r in range(t):
        cnf.clauses.append([S[0][r]] if r == 0 else [-S[0][r]])
        cnf.clauses.append([S[1][r]] if r == 1 else [-S[1][r]])
        for c in range(t):
            v = A[0][r][c]
            cnf.clauses.append([v] if (Au >> (t * r + c)) & 1 else [-v])
    for i in range(1, d):
        want = wanted_phi(i)
        for r in range(t):
            v = B[(0, i)][r]
            cnf.clauses.append([v] if (want >> r) & 1 else [-v])
    return cnf, names


def unit_count(t):
    return 2 * t + 2 * t * t


def in_normal_form(As, ss, B, t, Au):
    d = t + 1
    return (len(As) == d and As[0] == Au and ss[0] == 1 and ss[1] == 2
            and all(B[(0, i)] == wanted_phi(i) for i in range(1, d)))


def model_facts(As, ss, B, t):
    """What Proposition 25 and Lemma 32 predict for a model: phi onto X, ker A_u = span(e_0, e_1),
    A_v e_0 = e_0, A_v e_1 = 0, every rank <= t - 2."""
    d = t + 1
    at, sv = sa.tables(As, ss, B, d)
    ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
    phi = {sv[1 ^ h] ^ sv[1] ^ sv[h] for h in range(1 << d)}
    return {"max_rank": max(ranks), "phi_onto": len(phi) == 1 << t,
            "ker_A_u": [x for x in range(1 << t) if sa.mat_apply(As[0], x, t) == 0] == [0, 1, 2, 3],
            "A_v": sa.mat_apply(As[1], 1, t) == 1 and sa.mat_apply(As[1], 2, t) == 0,
            "rank_A_v": sa.rank_f2(sa.rows_of(As[1], t))}


# ---------- selfcheck ----------

def selfcheck():
    st = {"candidates": {}, "group": {}, "group_formula": {}, "orbit_sizes": {},
          "stabilisers": {}, "invariants": {}}
    for t in (3, 4, 5):
        orb = orbits(t)
        st["candidates"][str(t)] = len(candidates(t))
        st["group"][str(t)] = len(group(t))
        st["group_formula"][str(t)] = group_order(t)
        st["orbit_sizes"][str(t)] = sorted(o[1] for o in orb)
        st["stabilisers"][str(t)] = [stabiliser(o[0], t) for o in orb]
        st["invariants"][str(t)] = [list(invariants(o[0], t)) for o in orb]
    st["unit_clauses"] = {str(t): len(encode_case_a(t, orbits(t)[0][0])[0].clauses)
                          - len(sa.encode(t, t + 1, echelon=False)[0].clauses) for t in (3, 4, 5)}
    st["graded"] = {
        "candidates": all(st["candidates"][str(t)] == HAND[t][0] for t in HAND),
        "group": all(st["group"][str(t)] == st["group_formula"][str(t)] == HAND[t][1]
                     for t in HAND),
        "orbit_sizes": all(st["orbit_sizes"][str(t)] == HAND[t][2] for t in HAND),
        "orbit_stabiliser": all(o[1] * s == HAND[t][1] for t in HAND
                                for o, s in zip(orbits(t), st["stabilisers"][str(t)])),
        "d_split": all([x[0] for x in st["invariants"][str(t)]].count(2) == HAND_D2[t]
                       and [x[0] for x in st["invariants"][str(t)]].count(1)
                       == len(HAND[t][2]) - HAND_D2[t] for t in HAND),
        "nilpotent_d2_t5": sum(1 for x in st["invariants"]["5"] if x[0] == 2 and x[2]) == 3,
        "unit_clauses": all(st["unit_clauses"][str(t)] == unit_count(t) for t in HAND)}
    return st


# ---------- solving ----------

def instance_name(t, idx):
    return f"ca_t{t}_o{idx:02d}"


def child(t, Au, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_case_a(t, Au)
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


def solve_one(t, idx, Au, solver, budget_seconds, out_dir):
    d = t + 1
    name = instance_name(t, idx)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--au",
           str(Au), "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "d": d, "orbit": idx, "Au": Au, "invariants": list(invariants(Au, t)),
                "name": name, "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and in_normal_form(As, ss, B, t, Au))
        res["facts"] = model_facts(As, ss, B, t)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, solver, budget_seconds, group_seconds, out_dir):
    """Every orbit at t, in order; once the total budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    reps = [o[0] for o in orbits(t)]
    start = time.time()
    counts = {}
    for idx, Au in enumerate(reps):
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = {"status": "SKIPPED", "t": t, "orbit": idx, "Au": Au,
                   "name": instance_name(t, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(t, idx, Au, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return {"t": t, "orbits": len(reps), "counts": counts}


# Pre-registered (m15/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
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
        if fn.startswith("ca_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {}
    for t in CONTROLS + EXPLORATORY:
        status[str(t)] = [results.get(instance_name(t, i), {}).get("status", "missing")
                          for i in range(len(orbits(t)))]
    # Controls: every orbit UNSAT (Proposition 25: Case A needs t >= 5; also A(3) = 3, A(4) = 4).
    for t in CONTROLS:
        for i, s in enumerate(status[str(t)]):
            name = instance_name(t, i)
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    # A verified model anywhere must satisfy Proposition 25 and Lemma 32.
    for name, r in results.items():
        if r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - 2
        graded[name + "_lemma32"] = all(fa.get(key) for key in ("phi_onto", "ker_A_u", "A_v"))
    counts = {key: {s: v.count(s) for s in sorted(set(v))} for key, v in status.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
            "all_unsat_5": all(s == "UNSAT" for s in status["5"])}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=3)
    ap.add_argument("--au", type=int, default=0)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=12.0)
    ap.add_argument("--group-minutes", type=float, default=120.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.t, args.au, args.solver, args.child_out)
    elif args.part == "solve":
        out = solve_all(args.t, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY solve t{args.t} orbits {out['orbits']} "
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
