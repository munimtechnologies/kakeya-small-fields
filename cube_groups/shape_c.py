# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Shape c of Case B split by the commuting matrices of Lemma 38 (notes/shape-c.md).

Setting and encoding as in case_b_shapes.py; m = t - k. In shape c (beta = 0 on U+ = N, so every
A_n with n in N kills X_1 = ker A_u), A_u induces an isomorphism T from X/X_1 onto R = Im A_u, and
n in N gives M_n = T^-1 (A_n on X/X_1). In the bases of Lemmas 35 and 37, e_k, ..., e_(t-1) give a
basis of X/X_1. With M_i the matrix of M_(v_i) in it (column j = image of e_(k+j)),

    A_(v_i) e_(k+j) = A_u (sum_l M_i[l][j] e_(k+l))      for 1 <= i <= k - 1, 0 <= j < m.    (S)

Lemma 38: the M_n commute. Lemma 39: a new basis of P modulo Y (conjugating every M_i by the same g
in GL_m) and an invertible recombination of v_1, ..., v_(k-1) keep the normal form of shape c. So
shape c at (t, k) exists iff, for one orbit of commuting tuples (M_1, ..., M_(k-1)) under
GL_m x GL_(k-1), the CNF of case_b_shapes.encode_shape(t, k, 'c') with the parity equations (S) for
the orbit's least tuple is satisfiable. For m <= 3 the equations add clauses only, no variables.

m x m matrices are m^2-bit masks with entry (r, c) at bit m r + c, as in sat_aniso.py.

Parts: selfcheck (pure Python: commuting tuples and orbits against hand counts, orbit-stabiliser),
solve (every orbit at (t, k), each in a child process with a time budget, under a total budget;
needs python-sat), grade (the pre-registered predictions of m13/predictions.md).

Usage: python shape_c.py --part selfcheck|solve|grade [--t T --k K] [--budget-minutes 4]
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


# ---------- commuting tuples and their orbits ----------

def gl(m):
    return [g for g in range(1 << (m * m)) if sa.rank_f2(sa.rows_of(g, m)) == m]


def identity(m):
    return sum(1 << (m * r + r) for r in range(m))


@functools.lru_cache(maxsize=None)
def commuting_tuples(m, r):
    """Every r-tuple of m x m matrices that commute pairwise, in increasing order."""
    mats = range(1 << (m * m))
    out = [()]
    if r >= 2:
        cent = {A: {B for B in mats if sa.mat_mul(A, B, m) == sa.mat_mul(B, A, m)} for A in mats}
    for _ in range(r):
        out = [tup + (B,) for tup in out for B in mats if all(B in cent[A] for A in tup)]
    return out


def act(g, gi, R, tup, m):
    """Recombine the tuple by R (r x r, new M_a = sum of M_b over R[a][b] = 1), then conjugate
    every entry: M -> g^-1 M g."""
    r = len(tup)
    out = []
    for a in range(r):
        M = 0
        for b in range(r):
            if (R >> (r * a + b)) & 1:
                M ^= tup[b]
        out.append(sa.mat_mul(sa.mat_mul(gi, M, m), g, m))
    return tuple(out)


@functools.lru_cache(maxsize=None)
def orbits(m, r):
    """[(least tuple, orbit size, stabiliser size)] of the commuting r-tuples of m x m matrices
    under GL_m (simultaneous conjugation) x GL_r (recombination), sorted."""
    group = [(g, sa.mat_inv(g, m), R) for g in gl(m) for R in gl(r)]
    left = set(commuting_tuples(m, r))
    out = []
    while left:
        tup = min(left)
        images = [act(g, gi, R, tup, m) for g, gi, R in group]
        orb = set(images)
        out.append((tup, len(orb), images.count(tup)))
        left -= orb
    return sorted(out)


def span_dim(tup, m):
    return sa.rank_f2(list(tup))


# ---------- the encoding ----------

def encode_split(t, k, Ms):
    """case_b_shapes.encode_shape(t, k, 'c') with the parity equations (S) for Ms = (M_1, ...)."""
    cnf, names = cs.encode_shape(t, k, "c")
    A = names[0]
    m = t - k
    for i, M in enumerate(Ms, start=1):
        for j in range(m):
            col = sa.mat_apply(M, 1 << j, m)
            for r in range(t):
                cnf.xor_eq([A[i][r][k + j]] + [A[0][r][k + l] for l in range(m) if (col >> l) & 1],
                           0)
    return cnf, names


def split_clause_count(t, k, Ms):
    """Clauses that (S) adds: an equation on 1 + p variables (p <= 3) gives 2^p clauses."""
    m = t - k
    return t * sum(1 << bin(sa.mat_apply(M, 1 << j, m)).count("1") for M in Ms for j in range(m))


def satisfies_split(As, t, k, Ms):
    m = t - k
    for i, M in enumerate(Ms, start=1):
        for j in range(m):
            col = sa.mat_apply(M, 1 << j, m)
            want = 0
            for l in range(m):
                if (col >> l) & 1:
                    want ^= cs.col(As[0], k + l, t)
            if cs.col(As[i], k + j, t) != want:
                return False
    return True


def m_of(As, n, t, k):
    """M_n for n in N = span(v_0, ..., v_(k-1)) (bit mask over v_0, ..., v_(k-1)), or None if A_u
    is not one-to-one on span(e_k, ..., e_(t-1)) or Im A_n is not in Im A_u."""
    m = t - k
    An = 0
    for i in range(k):
        if (n >> i) & 1:
            An ^= As[i]
    inv = {}
    for z in range(1 << m):
        inv.setdefault(sa.mat_apply(As[0], z << k, t), z)
    if len(inv) != 1 << m:
        return None
    cols = []
    for j in range(m):
        z = inv.get(sa.mat_apply(An, 1 << (k + j), t))
        if z is None:
            return None
        cols.append(z)
    return sa.from_cols(cols, m)


def model_facts(As, ss, B, t, k):
    """What Lemma 38 predicts for a model: M_u = I, the M_n commute, D = T^-1(X_1 n R) contains
    M_n q(y) for all n and y (38(e)), and (G_y + G_y^2) sigma(n) = T M_n q(y) (38(d))."""
    d = t + k - 1
    m = t - k
    at, sv = sa.tables(As, ss, B, d)
    facts = {"max_rank": max(sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d))}
    Ms = {n: m_of(As, n, t, k) for n in range(1, 1 << k)}
    if any(M is None for M in Ms.values()):
        facts["T_ok"] = False
        return facts
    facts["T_ok"] = True
    facts["M_u_is_I"] = Ms[1] == identity(m)
    facts["commute"] = all(sa.mat_mul(P, Q, m) == sa.mat_mul(Q, P, m)
                           for P in Ms.values() for Q in Ms.values())
    D = {z for z in range(1 << m) if sa.mat_apply(As[0], z << k, t) >> k == 0}
    facts["dim_D"] = len(D).bit_length() - 1
    ok_d = ok_e = True
    for yb in range(1, 1 << (k - 1)):
        h = sum(1 << (k - 1 + j) for j in range(1, k) if (yb >> (j - 1)) & 1)
        q = sv[h] >> k
        for n, Mn in Ms.items():
            g1 = sa.mat_apply(at[h], sv[n], t)
            lhs = g1 ^ sa.mat_apply(at[h], g1, t)
            mq = sa.mat_apply(Mn, q, m)
            ok_d = ok_d and lhs == sa.mat_apply(As[0], mq << k, t)
            ok_e = ok_e and mq in D
    facts["lemma38d"] = ok_d
    facts["lemma38e"] = ok_e
    return facts


# ---------- selfcheck ----------

def selfcheck():
    commuting = {f"{m},{r}": len(commuting_tuples(m, r))
                 for m, r in ((1, 1), (2, 1), (2, 2), (3, 1), (3, 2))}
    small = {f"{m},{r}": len(orbits(m, r)) for m, r in ((1, 1), (2, 1), (2, 2), (3, 1))}
    big = orbits(3, 2)
    group = len(gl(3)) * len(gl(2))
    st = {"commuting": commuting, "orbits": dict(small, **{"3,2": len(big)}),
          "group_3_2": group,
          "orbits_3_2_by_span_dim": {str(s): sum(1 for o in big if span_dim(o[0], 3) == s)
                                     for s in range(3)},
          "split_clauses_6_3": [split_clause_count(6, 3, o[0]) for o in big]}
    st["graded"] = {
        "commuting": commuting == {"1,1": 2, "2,1": 16, "2,2": 88, "3,1": 512, "3,2": 7456},
        "orbits_small": small == {"1,1": 2, "2,1": 6, "2,2": 9, "3,1": 14},
        "orbit_stabiliser": group == 1008 and sum(o[1] for o in big) == 7456
        and all(o[1] * o[2] == group for o in big),
        "span_le_1": st["orbits_3_2_by_span_dim"]["0"] == 1
        and st["orbits_3_2_by_span_dim"]["1"] == 13}
    return st


# ---------- solving ----------

def instance_name(t, k, idx):
    return f"sc_t{t}_k{k}_o{idx:02d}"


def child(t, k, Ms, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_split(t, k, Ms)
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
                           and cs.in_shape(As, ss, B, t, k, "c") and satisfies_split(As, t, k, Ms))
        res["facts"] = model_facts(As, ss, B, t, k)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def solve_all(t, k, solver, budget_seconds, group_seconds, out_dir):
    """Every orbit at (t, k), in order; once the total budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    reps = [o[0] for o in orbits(t - k, k - 1)]
    start = time.time()
    counts = {}
    for idx, Ms in enumerate(reps):
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


# Pre-registered (m13/predictions.md). SAT counts only with a verified model; UNKNOWN, SKIPPED and
# ERROR are reported and not graded.
CONTROLS = ((3, 2), (4, 2))
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
        if fn.startswith("sc_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    status = {}
    for t, k in CONTROLS + EXPLORATORY:
        n = len(orbits(t - k, k - 1))
        status[f"{t},{k}"] = [results.get(instance_name(t, k, i), {}).get("status", "missing")
                              for i in range(n)]
    # Controls: every orbit UNSAT (A(3) = 3, A(4) = 4).
    for t, k in CONTROLS:
        for i, s in enumerate(status[f"{t},{k}"]):
            name = instance_name(t, k, i)
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
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - r["k"]
        graded[name + "_lemma38"] = all(fa.get(key) for key in
                                        ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e"))
    counts = {key: {s: v.count(s) for s in sorted(set(v))} for key, v in status.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
            "all_unsat_6_3": all(s == "UNSAT" for s in status["6,3"])}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=3)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--ms", default="")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=4.0)
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
