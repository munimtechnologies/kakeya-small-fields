# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m94: the pilot of the shape (c) search at rank 4 for t = 8 and dim V = 11 (notes/a84.md,
a85.md, a86.md; cube_groups/m94-predictions.md), with A_u of type (N4) and the matrices M_n of
Lemma 38 (notes/shape-c.md) fixed to a basis of one orbit of job m93.

Setting and encoding as in case_b.py and case_b_shapes.py. The form c of Lemma 37 at (t, k) = (8, 4)
fixes

    x0 = sigma(u) = e_0,  P = phi(V) = span(e_1, ..., e_7),  A_u kills X_1 = span(e_0, ..., e_3),
    sigma(v_i) = e_i,  beta(v_i, v_j) = 0,  A_(v_i) kills X_1  (i, j = 1, 2, 3),
    phi(v_(3+j)) = e_j.

By Corollary 121 and Lemma 94 an element u of rank 4 is in this form, with A_u of type (N4), (N3)
or (F3). By Lemma 95(b) (Lemma 39 with k = 4: conjugation in GL_4(F_2) on X / X_1, recombination
in GL_3(F_2) on Y), the space W = span(M_1, M_2, M_3) may be any representative of its orbit and the
tuple any basis of it. This file fixes the tuple and the type (N4) and leaves T = A_u on
[e_4], ..., [e_7] free:

    (N4) rows k to t - 1 of A_u e_c are 0 for c >= k (Im A_u = ker A_u), and no non-empty set of
         the columns A_u e_k, ..., A_u e_(t-1) adds up to 0 (T is one-to-one)
    (S)  A_(v_i) e_(k+j) = A_u (sum over l of M_i[l][j] e_(k+l))               (Lemma 38)
    (a)  rows k to t - 1 of beta(v_i, v_(k-1+j)) are 0 for j < k and column j - k of M_i for j >= k

With M_i constant, (S) is linear in the entries of A_u. The pilot's tuple is E_00, E_12, E_11 + E_22
(masks 1, 64, 1056 of m93.py, entry (r, c) at bit 4 r + c), the basis m93 recorded for its orbit of
size 10080, the largest orbit that meets (N4).

Controls: case_b's (t, k) = (2, 1) example must be SAT; the same encoder at (6, 3) with
M = N, N^2 (N the 3 x 3 shift) must be UNSAT, as A(6) = 6. The unit tests check the clauses on
hand-made data.

Matrices M are lists of rows, M[l][j] = entry (l, j), column j = image of [e_(k+j)]. A_u is a
tuple of columns (bit masks) where noted; sat_aniso.py uses t^2-bit masks with entry (r, c) at bit
t r + c.

Parts: selfcheck (pure Python), controls, pilot, grade.

Usage: python m94.py --part selfcheck|controls|pilot|grade [--cap-minutes 75] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import subprocess
import sys
import time

import case_b as cb
import case_b_shapes as csh
import sat_aniso as sa

T = 8
K = 4
PILOT_W = (1, 64, 1056)
PILOT_ORBIT = 10080
PILOT_NAME = "n4_t8_k4_w10080"
CONTROL_NAME = "n4_t6_k3"
SHIFT = [[0, 0, 0], [1, 0, 0], [0, 1, 0]]
SHIFT2 = [[0, 0, 0], [0, 0, 0], [1, 0, 0]]
# (S) conditions, (a) units, (N4) units, one-to-one clauses: (k - 1) n t, (k - 1)(t - 1) n, n^2,
# 2^n - 1 with n = t - k.
HAND = {(8, 4): {"lin": 96, "a_units": 84, "n4_units": 16, "inv": 15},
        (6, 3): {"lin": 36, "a_units": 30, "n4_units": 9, "inv": 7}}


# ---------- matrices as lists of rows ----------

def m_of(mask, n):
    """The n x n matrix of a bit mask with entry (l, j) at bit n l + j (m93.py's masks for n = 4)."""
    return [[(mask >> (n * l + j)) & 1 for j in range(n)] for l in range(n)]


def mul(x, y):
    n = len(x)
    return [[sum(x[a][l] & y[l][b] for l in range(n)) & 1 for b in range(n)] for a in range(n)]


def add(x, y):
    return [[a ^ b for a, b in zip(rx, ry)] for rx, ry in zip(x, y)]


def flat(x):
    return sum(v << (len(x) * l + j) for l, row in enumerate(x) for j, v in enumerate(row))


def check_tuple(Ms):
    """Pairwise commuting, independent, and I not in their span (Lemma 95(a))."""
    n = len(Ms[0])
    ident = flat([[int(l == j) for j in range(n)] for l in range(n)])
    span = {0}
    for x in Ms:
        if any(len(row) != n for row in x) or len(x) != n:
            return False
        span |= {s ^ flat(x) for s in span}
    return (len(span) == 1 << len(Ms) and ident not in span
            and all(mul(x, y) == mul(y, x) for x in Ms for y in Ms))


def pilot_ms():
    return [m_of(x, T - K) for x in PILOT_W]


# ---------- the encoding ----------

def encode_n4(t, k, Ms):
    """(cnf, names, info): encode_shape(t, k, 'c') with A_u of type (N4) and M_(v_i) = Ms[i - 1]
    (the conditions (N4), (S), (a) of the docstring). info: the counts, the first new clause and
    variable."""
    n = t - k
    if n != k or len(Ms) != k - 1 or not check_tuple(Ms):
        raise ValueError("type (N4) needs t = 2 k and k - 1 commuting matrices spanning a space "
                         "of dimension k - 1 without I")
    cnf, names = csh.encode_shape(t, k, "c")
    A, B = names[0], names[2]
    info = {"start": len(cnf.clauses), "first_var": cnf.nv + 1}
    n4 = 0
    for r in range(k, t):
        for c in range(k, t):
            cnf.clauses.append([-A[0][r][c]])
            n4 += 1
    inv = 0
    for sel in range(1, 1 << n):
        cs = [k + c for c in range(n) if (sel >> c) & 1]
        if len(cs) == 1:
            cnf.clauses.append([A[0][r][cs[0]] for r in range(k)])
        else:
            cnf.clauses.append([cnf.xor_def([A[0][r][c] for c in cs]) for r in range(k)])
        inv += 1
    lin = 0
    for i in range(1, k):
        M = Ms[i - 1]
        for j in range(n):
            for r in range(t):
                cnf.xor_eq([A[i][r][k + j]] + [A[0][r][k + l] for l in range(n) if M[l][j]], 0)
                lin += 1
    a_units = 0
    for i in range(1, k):
        M = Ms[i - 1]
        for j in range(1, t):
            for l in range(n):
                v = B[(i, k - 1 + j)][k + l]
                cnf.clauses.append([v] if j >= k and M[l][j - k] else [-v])
                a_units += 1
    info.update({"lin": lin, "a_units": a_units, "n4_units": n4, "inv": inv,
                 "vars": cnf.nv, "clauses": len(cnf.clauses)})
    return cnf, names, info


def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


def hint_info(t, k, Ms):
    cnf, _, info = encode_n4(t, k, Ms)
    info["consistent"] = units_consistent(cnf)
    return info


def col(A, c, t):
    return sa.mat_apply(A, 1 << c, t)


def fixed_ok(As, B, t, k, Ms):
    """(N4), (S) and (a) read back from a decoded model."""
    n = t - k
    low = (1 << k) - 1
    tcols = [col(As[0], k + c, t) for c in range(n)]
    if any(x & ~low for x in tcols) or sa.rank_f2(tcols) != n:
        return False
    for i in range(1, k):
        M = Ms[i - 1]
        for j in range(n):
            want = 0
            for l in range(n):
                if M[l][j]:
                    want ^= tcols[l]
            if col(As[i], k + j, t) != want:
                return False
        for j in range(1, t):
            want = sum(M[l][j - k] << (k + l) for l in range(n)) if j >= k else 0
            if (B[(i, k - 1 + j)] >> k) != want >> k:
                return False
    return True


# ---------- selfcheck ----------

def w_check():
    """The pilot's space against job m93's record (m93.py, downloaded unchanged)."""
    import m93
    tb = m93.Tables()
    basis = list(PILOT_W)
    el = m93.span_of(basis)
    orbit = {m93.key_of(m93.span_of([m93.mul(m93.mul(g, b), gi) for b in basis]))
             for g, gi in tb.pairs}
    return {"elements": len(set(el)), "identity": m93.IDENT in el,
            "commuting": all(m93.mul(x, y) == m93.mul(y, x) for x in basis for y in basis),
            "orbit_size": len(orbit), "flags": m93.flags(tb, basis)}


def selfcheck():
    st = {"case_b": cb.selfcheck(random.Random(61))["graded"],
          "case_b_shapes": csh.selfcheck()["graded"], "w": w_check(),
          "hints": {"8,4": hint_info(8, 4, pilot_ms()), "6,3": hint_info(6, 3, [SHIFT, SHIFT2])}}
    w, hi = st["w"], st["hints"]
    fl = w["flags"]

    def counts_ok(key, tk):
        return (all(hi[key][f] == v for f, v in HAND[tk].items()) and hi[key]["consistent"])

    st["graded"] = {
        "case_b": all(st["case_b"].values()),
        "case_b_shapes": all(st["case_b_shapes"].values()),
        "w_space": w["elements"] == 8 and not w["identity"] and w["commuting"]
        and check_tuple(pilot_ms()),
        "w_orbit": w["orbit_size"] == PILOT_ORBIT,
        "w_flags": fl["singular"] and fl["n4"] and fl["f3"] and fl["common_kernel_dim"] == 1
        and fl["image_dim"] == 3,
        "hints_t8": counts_ok("8,4", (8, 4)),
        "hints_t6": counts_ok("6,3", (6, 3))}
    return st


# ---------- solving ----------

def specs():
    return {CONTROL_NAME: {"name": CONTROL_NAME, "kind": "control", "t": 6, "k": 3,
                           "ms": [SHIFT, SHIFT2]},
            PILOT_NAME: {"name": PILOT_NAME, "kind": "pilot", "t": T, "k": K, "ms": pilot_ms(),
                         "w_masks": list(PILOT_W), "w_orbit": PILOT_ORBIT}}


def child(spec, solver, path):
    from pysat.solvers import Solver
    cnf, names, info = encode_n4(spec["t"], spec["k"], spec["ms"])
    with open(path + ".size", "w") as f:
        json.dump(info, f)
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
        As, ss, B = sa.decode(s.get_model(), names, spec["t"], spec["t"] + spec["k"] - 1)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_one(spec, solver, budget_seconds, out_dir):
    path = os.path.join(out_dir, spec["name"] + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
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
    try:
        with open(path + ".size") as f:
            res["cnf"] = json.load(f)
    except (OSError, ValueError):
        res["cnf"] = None
    res.update(spec)
    res.update({"wall_seconds": round(time.time() - start, 2),
                "budget_seconds": round(budget_seconds, 1)})
    if res["status"] == "SAT":
        t, k = spec["t"], spec["k"]
        d = t + k - 1
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and csh.in_shape(As, ss, B, t, k, "c")
                           and fixed_ok(As, B, t, k, spec["ms"]))
        res["facts"] = csh.model_facts(As, ss, B, t, k, "c")
    with open(os.path.join(out_dir, spec["name"] + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {spec['name']}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def run_controls(solver, out_dir):
    counts = {}
    res = cb.solve(2, 1, solver, 120, out_dir)
    counts["cb_t2_k1_" + res["status"]] = 1
    res = solve_one(specs()[CONTROL_NAME], solver, 600, out_dir)
    counts[CONTROL_NAME + "_" + res["status"]] = 1
    print(f"SUMMARY controls {json.dumps(counts, sort_keys=True)}", flush=True)


def run_pilot(solver, cap_seconds, out_dir):
    res = solve_one(specs()[PILOT_NAME], solver, cap_seconds, out_dir)
    cnf = res.get("cnf") or {}
    print(f"SUMMARY pilot {PILOT_NAME} {res['status']} wall_seconds {res['wall_seconds']} "
          f"vars {cnf.get('vars')} clauses {cnf.get('clauses')} verified {res.get('verified')}",
          flush=True)


# ---------- grading (pre-registered in m94-predictions.md) ----------

def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["selfcheck_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for name in ("cb_t2_k1", CONTROL_NAME, PILOT_NAME):
        try:
            with open(os.path.join(out_dir, name + ".json")) as f:
                results[name] = json.load(f)
        except (OSError, ValueError):
            ungraded[name] = "missing"
    r = results.get("cb_t2_k1")
    if r is not None:
        if r["status"] in ("SAT", "UNSAT"):
            graded["cb_t2_k1"] = r["status"] == "SAT" and bool(r.get("verified"))
        else:
            ungraded["cb_t2_k1"] = r["status"]
    r = results.get(CONTROL_NAME)
    if r is not None:
        if r["status"] in ("SAT", "UNSAT"):
            graded[CONTROL_NAME] = r["status"] == "UNSAT"
        else:
            ungraded[CONTROL_NAME] = r["status"]
    pilot = results.get(PILOT_NAME) or {}
    if pilot.get("status") == "SAT":
        graded[PILOT_NAME + "_verified"] = bool(pilot.get("verified"))
    return {"graded": graded, "ungraded": ungraded,
            "pilot": {key: pilot.get(key) for key in ("status", "seconds", "wall_seconds", "cnf",
                                                      "solver", "verified", "facts")},
            "control_seconds": (results.get(CONTROL_NAME) or {}).get("wall_seconds")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "pilot", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--cap-minutes", type=float, default=75.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="{}")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.solver, args.out_dir)
    elif args.part == "pilot":
        run_pilot(args.solver, args.cap_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {sorted(out['ungraded'])} "
              f"pilot {out['pilot']['status']}", flush=True)
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
