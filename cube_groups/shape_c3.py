# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Shape c of Case B in the case R = X_1 (d = k), as a split search (notes/a6-d3.md).

Setting and encoding as in shape_c.py, with t = 2k, so that rank A_u = k = dim X_1 and R = Im A_u
can equal X_1 = ker A_u (at t = 6 this is d = dim(X_1 n R) = 3, the case A_u^2 = 0). In the normal
form of Lemmas 35, 37 and 39 (X_1 = span(e_0, ..., e_(k-1)); v_1, ..., v_(k-1) in N with
sigma(v_j) = e_j; v_(k-1+j) in W with phi(v_(k-1+j)) = e_j), R = X_1 gives, by hand results:

    (D) A_u e_c lies in X_1 for c >= k                                   (R = X_1)
    (W) A_(v_(k-1+j)) maps X_1 into X_1 (Proposition 27(c2)) and induces M_j on X/X_1
        (Lemma 46(a), where L = [R] = 0)
    (K) M_(n_y) q(y) = 0 for every y in Y (Lemma 46(c), where L = 0), with q(y) the class of
        sigma(h_y) modulo X_1 and h_y = sum of the v_(k-1+j) over the e_j in y

By (K) and q(y) != 0 for y != 0 (Lemma 38(e)), every non-zero element of span(M_1, ..., M_(k-1))
is singular. So shape c with R = X_1 at (t, k) exists only if, for one orbit of shape_c.orbits whose
span has no invertible element, the CNF of shape_c.encode_split with (D), (W) and (K) is
satisfiable. (D) and (W) are unit clauses, (K) parity equations.

Parts: selfcheck (pure Python: the orbit filter against hand counts), solve (every kept orbit at
(t, k), each in a child process with a time budget, under a total budget; needs python-sat), grade
(the pre-registered predictions of m18/predictions.md).

Usage: python shape_c3.py --part selfcheck|solve|grade [--t T --k K] [--budget-minutes 7]
                          [--group-minutes 150] [--out-dir DIR]
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


# ---------- the orbit filter ----------

def m_of_y(Ms, yb):
    """M_(n_y) for y = sum of the e_j over the bits j - 1 of yb."""
    M = 0
    for j, Mj in enumerate(Ms, start=1):
        if (yb >> (j - 1)) & 1:
            M ^= Mj
    return M


def all_singular(Ms, m):
    return all(sa.rank_f2(sa.rows_of(m_of_y(Ms, yb), m)) < m for yb in range(1, 1 << len(Ms)))


def kept_orbits(m, r):
    """[(index in shape_c.orbits(m, r), least tuple)] for the orbits whose span has no invertible
    element. The property is the same for every tuple of an orbit."""
    return [(i, o[0]) for i, o in enumerate(sc.orbits(m, r)) if all_singular(o[0], m)]


# ---------- the encoding ----------

def w_index(k, j):
    """Index of v_(k-1+j), the element of W with phi = e_j."""
    return k - 1 + j


def q_vars(S, B, k, m, yb):
    """For each coordinate c < m of X/X_1, the variables whose sum is coordinate c of q(y)."""
    hs = [w_index(k, j) for j in range(1, k) if (yb >> (j - 1)) & 1]
    out = []
    for c in range(m):
        vs = [S[i][k + c] for i in hs]
        vs += [B[(hs[a], hs[b])][k + c] for a in range(len(hs)) for b in range(a + 1, len(hs))]
        out.append(vs)
    return out


def add_d3(cnf, names, t, k, Ms):
    """Append (D), (W) and (K) to cnf."""
    A, S, B = names[0], names[1], names[2]
    m = t - k
    for r in range(k, t):
        for c in range(k, t):
            cnf.clauses.append([-A[0][r][c]])
    for j, M in enumerate(Ms, start=1):
        i = w_index(k, j)
        for l in range(m):
            for c in range(t):
                want = c >= k and (M >> (m * l + c - k)) & 1
                v = A[i][k + l][c]
                cnf.clauses.append([v] if want else [-v])
    for yb in range(1, 1 << (k - 1)):
        M = m_of_y(Ms, yb)
        qv = q_vars(S, B, k, m, yb)
        for l in range(m):
            cnf.xor_eq([x for c in range(m) if (M >> (m * l + c)) & 1 for x in qv[c]], 0)


def encode_d3(t, k, Ms):
    if t != 2 * k:
        raise ValueError("R = X_1 needs t = 2k")
    cnf, names = sc.encode_split(t, k, Ms)
    add_d3(cnf, names, t, k, Ms)
    return cnf, names


def q_of(ss, B, k, yb):
    hs = [w_index(k, j) for j in range(1, k) if (yb >> (j - 1)) & 1]
    x = 0
    for i in hs:
        x ^= ss[i]
    for a in range(len(hs)):
        for b in range(a + 1, len(hs)):
            x ^= B[(hs[a], hs[b])]
    return x >> k


def satisfies_d3(As, ss, B, t, k, Ms):
    """(D), (W) and (K) checked directly on coordinates, without the CNF."""
    m = t - k
    if any(cs.col(As[0], c, t) >> k for c in range(k, t)):
        return False
    for j, M in enumerate(Ms, start=1):
        i = w_index(k, j)
        for c in range(t):
            want = 0 if c < k else sa.mat_apply(M, 1 << (c - k), m)
            if cs.col(As[i], c, t) >> k != want:
                return False
    return all(sa.mat_apply(m_of_y(Ms, yb), q_of(ss, B, k, yb), m) == 0
               for yb in range(1, 1 << (k - 1)))


def model_facts(As, ss, B, t, k):
    """What the hand results predict for a model: every rank <= t - k (Proposition 26(a)), R = X_1,
    and the facts of Lemma 38 that shape_c.model_facts checks."""
    facts = sc.model_facts(As, ss, B, t, k)
    R = sa.independent([cs.col(As[0], c, t) for c in range(t)])
    facts["R_is_X1"] = len(R) == k and all(v >> k == 0 for v in R)
    return facts


# ---------- selfcheck ----------

def selfcheck():
    kept = {f"{m},{r}": len(kept_orbits(m, r)) for m, r in ((2, 1), (3, 1), (3, 2))}
    big = kept_orbits(3, 2)
    lines = sum(1 for _, Ms in big if sc.span_dim(Ms, 3) <= 1)
    all_orbits = sc.orbits(3, 2)
    st = {"kept": kept, "kept_3_2_span_le_1": lines,
          "kept_3_2_indices": [i for i, _ in big],
          "orbits_3_2": len(all_orbits)}
    # Hand counts: the singular classes of M_2(F_2) are 0, the nilpotent one and diag(0, 1); those
    # of M_3(F_2) are 0 and seven non-zero classes (rank-1 and regular nilpotent, the four split
    # classes with eigenvalue 0, and x (x^2 + x + 1)). A pair spanning at most a line is kept iff
    # its one class is singular.
    st["graded"] = {"kept_single": kept["2,1"] == 3 and kept["3,1"] == 8,
                    "kept_lines": lines == 8,
                    "kept_proper": 8 <= kept["3,2"] < len(all_orbits),
                    "filter_ok": all(all_singular(Ms, 3) for _, Ms in big)}
    return st


# ---------- solving ----------

def instance_name(t, k, idx):
    return f"d3_t{t}_k{k}_o{idx:02d}"


def child(t, k, Ms, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_d3(t, k, Ms)
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
                           and satisfies_d3(As, ss, B, t, k, Ms))
        res["facts"] = model_facts(As, ss, B, t, k)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, k, solver, budget_seconds, group_seconds, out_dir):
    """Every kept orbit at (t, k), in order; once the total budget is used up the rest are
    SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    reps = kept_orbits(t - k, k - 1)
    start = time.time()
    counts = {}
    for idx, Ms in reps:
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = {"status": "SKIPPED", "t": t, "k": k, "orbit": idx, "Ms": list(Ms),
                   "name": instance_name(t, k, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(t, k, idx, Ms, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return {"t": t, "k": k, "orbits": len(reps), "counts": counts}


# Pre-registered (m18/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
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
        if fn.startswith("d3_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {}
    for t, k in CONTROLS + EXPLORATORY:
        status[f"{t},{k}"] = [results.get(instance_name(t, k, i), {}).get("status", "missing")
                              for i, _ in kept_orbits(t - k, k - 1)]
    # Controls: every kept orbit UNSAT (A(4) = 4).
    for t, k in CONTROLS:
        for (i, _), s in zip(kept_orbits(t - k, k - 1), status[f"{t},{k}"]):
            name = instance_name(t, k, i)
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    # A verified model anywhere must satisfy Proposition 26(a), R = X_1 and Lemma 38.
    for name, r in results.items():
        if r["status"] != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - r["k"]
        graded[name + "_facts"] = all(fa.get(key) for key in
                                      ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e",
                                       "R_is_X1"))
    counts = {key: {s: v.count(s) for s in sorted(set(v))} for key, v in status.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
            "all_unsat_6_3": all(s == "UNSAT" for s in status["6,3"])}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=4)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--ms", default="")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=7.0)
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
        print(f"SUMMARY solve t{args.t} k{args.k} orbits {out['orbits']} "
              f"{json.dumps(out['counts'], sort_keys=True)}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"all_unsat_6_3 {out['all_unsat_6_3']}", flush=True)
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
