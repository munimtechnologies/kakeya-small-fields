# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m27: the rank-3 configurations (A4), (B4) and (B5) of Corollary 39 (notes/a10.md) at t = 6,
split by the positions of ker A_u and Im A_u.

Let u be an element of an anisotropic system with dim X = t and dim V = d, x0 = sigma(u),
phi = beta(u, .), P = phi(V). A shape is ("A", p) (x0 in P, dim P = p) or ("B", p) (x0 not in P,
dim P = p). GL(X) acts on systems, so we may fix the normal form

    sigma(u) = e_0,   P = span(e_0, ..., e_(p-1)) (shape A) or span(e_1, ..., e_p) (shape B),
    V = span(h_0 = u, h_1, ..., h_(d-1)),  phi(h_i) = 0 for i < d - p,
    phi(h_(d-p+j)) = the j-th basis vector of P.

If u has rank rho, X_1 = ker A_u (dimension t - rho, it contains x0) and R = Im A_u (dimension rho)
are fixed only up to G = {g in GL(X) : g e_0 = e_0, g P = P}, which keeps the normal form (re-choose
the h_i). So the instances are the G-orbits of the pairs (X_1, R); each instance adds the linear
constraints A_u X_1 = 0 and Im A_u in R and leaves everything else free. The orbits are computed by
closure under elementary transvections that lie in G (their union covers every pair even if they
generated less than G, so the split is complete either way). Every rank-3 element of a system with
t = 6 and dim V = 7 that has no element of rank 4 is in (A4) = ("A", 5), (B4) = ("B", 4) or
(B5) = ("B", 5) (Corollary 39), so UNSAT for every orbit of a shape rules that configuration out;
a SAT answer is checked by brute force and would be a system with dim V = 7, so A(6) = 7.

Parts: selfcheck (pure Python: subspace counts, the group, the orbits, hand values), controls
(t = 2, dim V = 2 against Lemma 63, and t = 4, dim V = 5, UNSAT by A(4) = 4; needs python-sat),
solve (one shape at t = 6; needs python-sat), grade (the predictions of m27/predictions.md).
Each instance is solved in a child process with a time budget.

Usage: python a6_r3.py --part selfcheck|controls|solve|grade [--shape A5|B4|B5]
                       [--budget-minutes 3] [--group-minutes 55] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import sat_aniso as sa

T = 6
RHO = 3
SHAPES = {"A5": ("A", 5), "B4": ("B", 4), "B5": ("B", 5)}
# Controls: (t, d, rho, shape, p).
CONTROLS = ((2, 2, 1, "A", 1), (2, 2, 1, "B", 1),
            (4, 5, 2, "A", 3), (4, 5, 2, "B", 3), (4, 5, 2, "B", 2))


# ---------- subspaces ----------

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


def subspaces(t, k, containing=0):
    """Every k-dimensional subspace of F_2^t (as rref tuples) that contains the vector containing."""
    out = set()
    for vs in itertools.combinations(range(1, 1 << t), k):
        r = rref(vs)
        if len(r) == k and (not containing or in_span(r, containing)):
            out.add(r)
    return sorted(out)


def image(g, rows, t):
    return rref([sa.mat_apply(g, v, t) for v in rows])


def dim_meet(a, b):
    return len(a) + len(b) - len(rref(list(a) + list(b)))


# ---------- the normal form and its group ----------

def p_basis(shape, p):
    return [1 << j for j in range(p)] if shape == "A" else [1 << j for j in range(1, p + 1)]


def gl_order(n):
    out = 1
    for i in range(n):
        out *= (1 << n) - (1 << i)
    return out


def group_order(t, shape, p):
    """|G|: block triangular with diagonal blocks (1, GL_(p-1), GL_(t-p)) for A and
    (GL_p, 1, GL_(t-p-1)) for B."""
    if shape == "A":
        return 2 ** ((t - 1) + (p - 1) * (t - p)) * gl_order(p - 1) * gl_order(t - p)
    return 2 ** ((p + 1) * (t - p - 1)) * gl_order(p) * gl_order(t - p - 1)


def generators(t, shape, p):
    """The elementary transvections g e_j = e_j + e_i (other e_c fixed) that lie in G."""
    inP = {b.bit_length() - 1 for b in p_basis(shape, p)}
    gens = []
    for j in range(1, t):
        for i in range(t):
            if i == j or (j in inP and i not in inP):
                continue
            cols = [1 << c for c in range(t)]
            cols[j] |= 1 << i
            gens.append(sa.from_cols(cols, t))
    return gens


def in_group(g, t, shape, p):
    pb = p_basis(shape, p)
    return (sa.mat_apply(g, 1, t) == 1 and sa.rank_f2(sa.rows_of(g, t)) == t
            and all(in_span(rref(pb), sa.mat_apply(g, v, t)) for v in pb))


def orbits(t, shape, p, rho):
    """[(X_1, R, orbit size)] for the G-orbits of the pairs (X_1 containing e_0, R), ordered by
    decreasing d = dim(X_1 n R) and then by first appearance."""
    xs = subspaces(t, t - rho, 1)
    rs = subspaces(t, rho)
    xi = {x: i for i, x in enumerate(xs)}
    ri = {r: i for i, r in enumerate(rs)}
    gens = generators(t, shape, p)
    gx = [[xi[image(g, x, t)] for x in xs] for g in gens]
    gr = [[ri[image(g, r, t)] for r in rs] for g in gens]
    nr = len(rs)
    seen = bytearray(len(xs) * nr)
    found = []
    for a0 in range(len(xs)):
        for b0 in range(nr):
            if seen[a0 * nr + b0]:
                continue
            seen[a0 * nr + b0] = 1
            stack, size = [(a0, b0)], 0
            while stack:
                a, b = stack.pop()
                size += 1
                for g in range(len(gens)):
                    a2, b2 = gx[g][a], gr[g][b]
                    if not seen[a2 * nr + b2]:
                        seen[a2 * nr + b2] = 1
                        stack.append((a2, b2))
            found.append((xs[a0], rs[b0], size))
    order = sorted(range(len(found)), key=lambda i: (-dim_meet(found[i][0], found[i][1]), i))
    return [found[i] for i in order]


def invariants(t, shape, p, x1, r):
    pb = rref(p_basis(shape, p))
    return {"d": dim_meet(x1, r), "x0_in_R": in_span(r, 1), "dim_X1_P": dim_meet(x1, pb),
            "dim_R_P": dim_meet(r, pb)}


# ---------- the encoding ----------

def wanted_phi(i, d, shape, p):
    kd = d - p
    return 0 if i < kd else p_basis(shape, p)[i - kd]


def encode_r3(t, d, shape, p, x1, r):
    """sat_aniso.encode (no echelon form) with sigma(u) = e_0, phi fixed, A_u X_1 = 0, Im A_u in R."""
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]
    for row in range(t):
        cnf.clauses.append([S[0][row]] if row == 0 else [-S[0][row]])
    for i in range(1, d):
        want = wanted_phi(i, d, shape, p)
        for row in range(t):
            v = B[(0, i)][row]
            cnf.clauses.append([v] if (want >> row) & 1 else [-v])
    for x in x1:
        for row in range(t):
            cnf.xor_eq([A[0][row][c] for c in range(t) if (x >> c) & 1], 0)
    for f in sa.nullspace(list(r), t):
        for c in range(t):
            cnf.xor_eq([A[0][row][c] for row in range(t) if (f >> row) & 1], 0)
    return cnf, names


def in_normal_form(As, ss, B, t, d, shape, p, x1, r):
    if len(As) != d or ss[0] != 1:
        return False
    if any(B[(0, i)] != wanted_phi(i, d, shape, p) for i in range(1, d)):
        return False
    Au = As[0]
    return (all(sa.mat_apply(Au, x, t) == 0 for x in x1)
            and all(in_span(r, sa.mat_apply(Au, 1 << c, t)) for c in range(t)))


def model_facts(As, ss, B, t, d):
    at, sv = sa.tables(As, ss, B, d)
    ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
    return {"rank_u": ranks[0], "max_rank": max(ranks)}


# ---------- selfcheck ----------

# Hand values (m27/predictions.md).
HAND_SUBSPACES = {(2, 1, 1): 1, (2, 1, 0): 3, (4, 2, 1): 7, (4, 2, 0): 35, (6, 3, 1): 155,
                  (6, 3, 0): 1395}
HAND_GROUP = {(6, "A", 5): 10321920, (6, "B", 4): 645120, (6, "B", 5): 9999360,
              (4, "B", 3): 168, (2, "A", 1): 2, (2, "B", 1): 1}
HAND_ORBITS = {(2, "A", 1): [1, 2], (2, "B", 1): [1, 1, 1], (4, "B", 3): [7, 21, 21, 28, 42, 42, 84]}


def selfcheck():
    st = {"subspaces": {}, "group_order": {}, "gens_in_group": {}, "orbit_counts": {},
          "orbit_sizes": {}, "totals": {}, "divides": {}, "invariants": {}}
    for (t, k, c), n in HAND_SUBSPACES.items():
        st["subspaces"][f"{t},{k},{c}"] = len(subspaces(t, k, c))
    cases = [(t, rho, s, p) for t, d, rho, s, p in CONTROLS] + [(T, RHO, s, p)
                                                               for s, p in SHAPES.values()]
    for t, rho, s, p in cases:
        key = f"t{t}_{s}{p}"
        orb = orbits(t, s, p, rho)
        go = group_order(t, s, p)
        st["group_order"][key] = go
        st["gens_in_group"][key] = all(in_group(g, t, s, p) for g in generators(t, s, p))
        st["orbit_counts"][key] = len(orb)
        st["orbit_sizes"][key] = sorted(o[2] for o in orb)
        st["totals"][key] = sum(o[2] for o in orb)
        st["divides"][key] = all(go % o[2] == 0 for o in orb)
        if t == T:
            st["invariants"][key] = [invariants(t, s, p, x1, r) for x1, r, _ in orb]
    tot = {2: 3, 4: 245, 6: 155 * 1395}
    st["graded"] = {
        "subspaces": all(st["subspaces"][f"{t},{k},{c}"] == n
                         for (t, k, c), n in HAND_SUBSPACES.items()),
        "group_order": all(st["group_order"][f"t{t}_{s}{p}"] == n
                           for (t, s, p), n in HAND_GROUP.items()),
        "gens_in_group": all(st["gens_in_group"].values()),
        "totals": all(v == tot[int(k[1:k.index("_")])] for k, v in st["totals"].items()),
        "divides": all(st["divides"].values()),
        "hand_orbits": all(st["orbit_sizes"][f"t{t}_{s}{p}"] == v
                           for (t, s, p), v in HAND_ORBITS.items())}
    return st


# ---------- solving ----------

def instance_name(t, shape, p, idx):
    return f"r3_t{t}_{shape}{p}_o{idx:03d}"


def child(spec_path, solver, path):
    from pysat.solvers import Solver
    with open(spec_path) as f:
        sp = json.load(f)
    t, d = sp["t"], sp["d"]
    cnf, names = encode_r3(t, d, sp["shape"], sp["p"], sp["x1"], sp["r"])
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
        As, ss, B = sa.decode(s.get_model(), names, t, d)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_one(spec, solver, budget_seconds, out_dir):
    t, d, shape, p = spec["t"], spec["d"], spec["shape"], spec["p"]
    name = spec["name"]
    spec_path = os.path.join(out_dir, name + ".spec.json")
    with open(spec_path, "w") as f:
        json.dump(spec, f)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", spec_path,
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
    res["invariants"] = invariants(t, shape, p, spec["x1"], spec["r"])
    res["wall_seconds"] = round(time.time() - start, 2)
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and in_normal_form(As, ss, B, t, d, shape, p, spec["x1"], spec["r"]))
        res["facts"] = model_facts(As, ss, B, t, d)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def specs(t, d, rho, shape, p):
    return [{"t": t, "d": d, "rho": rho, "shape": shape, "p": p, "x1": list(x1), "r": list(r),
             "size": size, "name": instance_name(t, shape, p, idx)}
            for idx, (x1, r, size) in enumerate(orbits(t, shape, p, rho))]


def run_group(sps, solver, budget_seconds, group_seconds, out_dir):
    """The instances in order; once the group budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for sp in sps:
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = dict(sp, status="SKIPPED")
            with open(os.path.join(out_dir, sp["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(sp, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


# ---------- grading ----------

def expected_control(t, shape, r):
    """Lemma 63 at t = 2 (dim V = 2): shape A is SAT for every R (u = a + b, A_u = 0); shape B is
    SAT only for R = span(e_1) (u = a, A_u the projection onto span(f) along span(e)). At t = 4,
    dim V = 5 nothing exists (A(4) = 4)."""
    if t == 2:
        return "SAT" if shape == "A" or list(r) == [2] else "UNSAT"
    return "UNSAT"


def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if (fn.startswith("r3_") and fn.endswith(".json") and not fn.endswith(".child.json")
                and not fn.endswith(".spec.json")):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    for name, r in results.items():
        if r.get("t") == T:
            continue
        s = r.get("status", "missing")
        if s in ("SAT", "UNSAT"):
            graded[name] = s == expected_control(r["t"], r["shape"], r["r"])
            if s == "SAT":
                graded[name + "_verified"] = bool(r.get("verified"))
        else:
            ungraded[name] = s
    per_shape = {}
    for key, (s, p) in SHAPES.items():
        st = [r for n, r in sorted(results.items()) if r.get("t") == T and r["shape"] == s
              and r["p"] == p]
        status = [r.get("status") for r in st]
        per_shape[key] = {"instances": len(st),
                          "counts": {x: status.count(x) for x in sorted(set(status))},
                          "all_unsat": bool(st) and all(x == "UNSAT" for x in status),
                          "undecided": [r["name"] for r in st if r.get("status") != "UNSAT"]}
        for r in st:
            if r.get("status") == "SAT":
                graded[r["name"] + "_verified"] = bool(r.get("verified"))
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "per_shape": per_shape, "times": times,
            "any_sat_6": any(r.get("status") == "SAT" for r in results.values()
                             if r.get("t") == T)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--shape", choices=sorted(SHAPES), default="A5")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=3.0)
    ap.add_argument("--group-minutes", type=float, default=55.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="spec.json")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.spec, args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        sps = [sp for t, d, rho, s, p in CONTROLS for sp in specs(t, d, rho, s, p)]
        out = run_group(sps, args.solver, 120, 3600, args.out_dir)
        print(f"SUMMARY controls {json.dumps(out, sort_keys=True)}", flush=True)
    elif args.part == "solve":
        s, p = SHAPES[args.shape]
        sps = specs(T, T + 1, RHO, s, p)
        out = run_group(sps, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY solve {args.shape} instances {len(sps)} {json.dumps(out, sort_keys=True)}",
              flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_6 {out['any_sat_6']} "
              + " ".join(f"{k} {v['counts']}" for k, v in out["per_shape"].items()), flush=True)
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
