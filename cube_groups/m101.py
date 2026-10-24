# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m101: the rank-0 case of (B7)_8 (t = 8, dim V = 11, dim P = 7) with a zero map in ker phi
(Corollary 123 of notes/a93.md), for every class of A_u (cube_groups/m101-predictions.md).

What came back on 2026-10-24 (job m100, notes/a93.md): every graded check held (14 of 14 in each
half) and all four positive controls were SAT, but all 68 rank-0 sweeps were UNKNOWN at 180 s.

Corollary 123 (by hand, notes/a93.md): in the rank-0 case (every A_n with n in N = ker phi vanishes
on X_1 = ker A_u), the maps A_n are A_u T_n on X / X_1 with T_n commuting (Lemma 104), so some
w != 0 in N has A_w = 0, and the basis of N can be chosen with v_1 = w. For such w, C =
beta(w, V) + span(sigma(w)) lies in X_1 (Lemma 105 (a)), and unless A_u is idempotent, x0 is not in C
(Lemma 105 (d), (e)). So for one class, the rank-0 case is one instance: m100's sweep instance plus

    A_(v_1) = 0                                    64 unit clauses
    beta(v_1, e_j) in X_1 for j != 1               30 unit clauses (implied; added for the solver)
    x0 not in C (A_u not idempotent)               a functional f on X_1 with f(x0) = 1 that
                                                   kills sigma(v_1) and every beta(v_1, e_j)

In m42's normal form x0 = sigma(u) = e_0 and X_1 = span(e_0, ..., e_4) in every pair orbit, so f
needs only the coordinates 0 to 4. The instance is a case split on the system with the basis of N
chosen as Corollary 123 allows; it needs no symmetry argument. UNSAT for a class means: every system
of that class has an element of N whose map is not zero on X_1.

Parts (one shard of the 13 pairs per job, as m100):

    check    the instance counts, that m100's sweep instance is an unchanged prefix of this one,
             2047 anisotropy clauses in the sweep CNF, none in "relax" and 15 in "relax_n", and
             the idempotent classes found by machine against the two found by hand
    control  two classes of the shard without the anisotropy clauses ("relax") and with anisotropy
             kept only on N ("relax_n"); a model must pass every added condition, checked outside
             the encoder
    sweep    every class of the shard, capped
    grade    the graded checks of m101-predictions.md

Usage: python m101.py --part check|control|sweep|grade --shard a|b [--cap-seconds S] [--out-dir D]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import m42
import m100
import sat_aniso as sa

T, D, P, KD = m100.T, m100.D, m100.P, m100.KD
X0 = 1                                   # sigma(u) = e_0 in m42's normal form
NX1 = T - 3                              # X_1 = span(e_0, ..., e_4), dimension 5
X1_MASK = (1 << NX1) - 1
# by hand (notes/a93.md): A_u is idempotent only in these two classes, both with d = 0
IDEMPOTENT = ((11, 5), (12, 10))
MODES = ("sweep", "relax", "relax_n")
ZERO_UNITS = T * T
IN_X1_UNITS = (D - 1) * (T - NX1)
CASE_TWO_VECTORS = D                     # sigma(v_1) and beta(v_1, e_j) for the 10 j != 1


def bkey(i, j):
    return (min(i, j), max(i, j))


def is_idempotent(au, t=T):
    return sa.mat_mul(au, au, t) == au


def case_two_required(spec):
    return not is_idempotent(spec["au"], spec["t"])


# ---------- the added conditions ----------

def add_zero_map(cnf, names, t):
    """A_(v_1) = 0 (Corollary 123 (ii)). Returns the number of unit clauses."""
    A = names[0]
    for r in range(t):
        for c in range(t):
            cnf.clauses.append([-A[1][r][c]])
    return t * t


def add_in_x1(cnf, names, t, d, nx1=NX1):
    """beta(v_1, e_j) in X_1 = span(e_0, ..., e_(nx1 - 1)) for j != 1 (Lemma 105 (a))."""
    B = names[2]
    n = 0
    for j in range(d):
        if j == 1:
            continue
        for r in range(nx1, t):
            cnf.clauses.append([-B[bkey(1, j)][r]])
            n += 1
    return n


def add_case_two(cnf, names, t, d, nx1=NX1):
    """x0 = e_0 not in C = span(sigma(v_1), beta(v_1, e_j)), for vectors in X_1: a functional f on
    the first nx1 coordinates with f(e_0) = 1 that kills every generator of C. Returns
    (f variables, number of generators)."""
    S, B = names[1], names[2]
    f = [cnf.new() for _ in range(nx1)]
    cnf.clauses.append([f[0]])
    vecs = [S[1]] + [B[bkey(1, j)] for j in range(d) if j != 1]
    for vec in vecs:
        cnf.xor_eq([cnf.AND(f[r], vec[r]) for r in range(nx1)], 0)
    return f, len(vecs)


def add_aniso_on(cnf, names, t, idx):
    """sigma(h) != 0 for every non-zero h in span(e_i : i in idx), as sat_aniso.encode does on all
    of V. Returns the number of clauses."""
    S, B = names[1], names[2]
    n = 0
    idx = list(idx)
    for k in range(1, len(idx) + 1):
        for sub in itertools.combinations(idx, k):
            ys = []
            for r in range(t):
                vs = [S[i][r] for i in sub] + [B[(i, j)][r] for i, j in itertools.combinations(sub, 2)]
                ys.append(cnf.xor_def(vs))
            cnf.clauses.append(ys)
            n += 1
    return n


def build(spec, mode="sweep"):
    """(cnf, names, counts) of the instance; "relax" drops the anisotropy clauses and "relax_n"
    keeps them only on N = span(u, v_1, v_2, v_3)."""
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    cnf, names = m100.encode_fixed(t, d, au, s0, phis, aniso=mode == "sweep")
    counts = {"hints": m42.add_hints(cnf, names, t, kd, au, s0, pvecs),
              "sweep": m100.add_sweep(cnf, names, t, kd, au)}
    counts["base_clauses"] = len(cnf.clauses)
    counts["zero"] = add_zero_map(cnf, names, t)
    counts["in_x1"] = add_in_x1(cnf, names, t, d)
    counts["case_two"] = add_case_two(cnf, names, t, d)[1] if case_two_required(spec) else 0
    counts["aniso_n"] = add_aniso_on(cnf, names, t, range(kd)) if mode == "relax_n" else 0
    return cnf, names, counts


# ---------- solving ----------

def child(spec, mode, path):
    from pysat.solvers import Solver
    cnf, names, _ = build(spec, mode)
    start = time.time()
    used = None
    for name in sa.SOLVERS:
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
        As, ss, B = sa.decode(s.get_model(), names, T, D)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def check_model(spec, res):
    """A SAT answer read back outside the encoder: m100's checks ((*) on all 2^11 x 2^11 pairs, the
    normal form, the sweep conditions, anisotropy), and each added condition separately."""
    out = m100.check_model(spec, res)
    As, ss = res["A"], res["s"]
    B = {(i, k): v for i, k, v in res["B"]}
    gens = [ss[1]] + [B[bkey(1, j)] for j in range(D) if j != 1]
    _, sv = sa.tables(As, ss, B, D)
    out["zero_map"] = As[1] == 0
    out["in_x1"] = all(v & ~X1_MASK == 0 for v in gens)
    out["case_two"] = X0 not in m100.span(gens)
    out["aniso_n"] = all(sv[h] for h in range(1, 1 << KD))
    return out


def needed(spec, mode):
    need = ["system", "normal_form", "sweep", "zero_map", "in_x1"]
    if case_two_required(spec):
        need.append("case_two")
    if mode == "sweep":
        need.append("anisotropic")
    if mode == "relax_n":
        need.append("aniso_n")
    return need


def solve_one(spec, mode, budget, out_dir):
    tag = spec["name"] + "_" + mode
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--mode", mode, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({k: spec[k] for k in ("name", "pair", "cls", "dmeet", "class_size")})
    row.update({"mode": mode, "case_two": case_two_required(spec),
                "wall_seconds": round(time.time() - start, 2), "budget_seconds": budget})
    if res["status"] == "SAT":
        row["check"] = check_model(spec, res)
        row["verified"] = all(row["check"][k] for k in needed(spec, mode))
    print(f"solve {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


# ---------- the parts ----------

def run_check(shard, out_dir):
    g = {}
    reps = [(pi, ci) for pi in range(len(m100.PAIRS)) for ci in range(len(m100.PAIRS[pi][2]))]
    g["classes_68"] = len(reps) == 68
    g["x1_is_e0_e4"] = all(m100.span(x1) == m100.span([1 << i for i in range(NX1)])
                           for x1, _, _ in m100.PAIRS)
    found = tuple(sorted((pi, ci) for pi, ci in reps
                         if is_idempotent(m100.PAIRS[pi][2][ci][0])))
    g["idempotent_as_hand"] = found == IDEMPOTENT
    g["idempotent_d0_size1"] = all(m100.M99_D[pi] == 0 and m100.PAIRS[pi][2][ci][1] == 1
                                   for pi, ci in found)
    spec = m100.spec_of(*m100.CONTROLS[shard][0])
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    g["x0_e0"] = s0 == X0
    g["n_in_ker_phi"] = kd == 4 and all(phis[i] == 0 for i in range(1, kd))
    theirs, _, _, _ = m100.build(spec, relax=False)
    h_theirs, n_theirs = m100.clause_hash(theirs), len(theirs.clauses)
    del theirs
    info = {"spec": spec["name"]}
    for mode in MODES:
        cnf, _, counts = build(spec, mode)
        info[mode] = dict(counts, clauses=len(cnf.clauses), aniso=m100.aniso_clauses(cnf, t))
        if mode == "sweep":
            prefix = sa.CNF()
            prefix.clauses = cnf.clauses[:n_theirs]
            g["m100_prefix"] = (counts["base_clauses"] == n_theirs
                                and m100.clause_hash(prefix) == h_theirs)
            del prefix
        del cnf
    g["counts"] = all(info[m]["zero"] == ZERO_UNITS == 64 and info[m]["in_x1"] == IN_X1_UNITS == 30
                      and info[m]["case_two"] == CASE_TWO_VECTORS == 11
                      and info[m]["sweep"] == m100.SWEEP_CONDITIONS for m in MODES)
    g["aniso_by_mode"] = (info["sweep"]["aniso"], info["relax"]["aniso"],
                          info["relax_n"]["aniso"]) == ((1 << d) - 1, 0, (1 << kd) - 1)
    g["shards_cover"] = sorted(m100.SHARDS["a"] + m100.SHARDS["b"]) == list(range(13))
    info["graded"] = g
    info["idempotent"] = [list(x) for x in found]
    with open(os.path.join(out_dir, f"m101{shard}_check.json"), "w") as f:
        json.dump(info, f, indent=1)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} idempotent "
          f"{info['idempotent']} counts {json.dumps(info['sweep'], sort_keys=True)}", flush=True)


def append_row(out_dir, shard, row):
    rows = m100.load(out_dir, f"m101{shard}_rows.json") or []
    rows.append(row)
    with open(os.path.join(out_dir, f"m101{shard}_rows.json"), "w") as f:
        json.dump(rows, f, indent=1)


def run_control(shard, cap, out_dir):
    counts = {}
    for pi, ci in m100.CONTROLS[shard]:
        for mode in ("relax", "relax_n"):
            row = solve_one(m100.spec_of(pi, ci), mode, cap, out_dir)
            append_row(out_dir, shard, row)
            key = f"{mode} {row['status']}"
            counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY control {shard} {json.dumps(counts, sort_keys=True)} cap {cap}", flush=True)


def run_sweep(shard, cap, out_dir):
    counts, by_d = {}, {}
    for spec in m100.shard_specs(shard):
        row = solve_one(spec, "sweep", cap, out_dir)
        append_row(out_dir, shard, row)
        counts[row["status"]] = counts.get(row["status"], 0) + 1
        key = f"d{spec['dmeet']}"
        by_d.setdefault(key, {})
        by_d[key][row["status"]] = by_d[key].get(row["status"], 0) + 1
    print(f"SUMMARY sweep {shard} {json.dumps(counts, sort_keys=True)} by_d "
          f"{json.dumps(by_d, sort_keys=True)} cap {cap}", flush=True)


def grade(shard, out_dir):
    g = {}
    chk = m100.load(out_dir, f"m101{shard}_check.json")
    if chk is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    rows = m100.load(out_dir, f"m101{shard}_rows.json") or []
    sweep = [r for r in rows if r["mode"] == "sweep"]
    control = [r for r in rows if r["mode"] != "sweep"]
    g["sweep_complete"] = sorted(r["name"] for r in sweep) == sorted(
        s["name"] for s in m100.shard_specs(shard))
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g["verified_" + r["name"] + "_" + r["mode"]] = bool(r.get("verified"))
    return {"graded": g,
            "sweep": {r["name"]: [r["status"], r["wall_seconds"], r["dmeet"]] for r in sweep},
            "control": {r["name"] + "_" + r["mode"]: [r["status"], r["wall_seconds"]]
                        for r in control},
            "unsat": sorted(r["name"] for r in sweep if r["status"] == "UNSAT")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "control", "sweep", "grade", "child"],
                    default="check")
    ap.add_argument("--shard", choices=sorted(m100.SHARDS), default="a")
    ap.add_argument("--cap-seconds", type=float, default=180.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--mode", choices=MODES, default="sweep")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.mode, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "control":
        run_control(args.shard, args.cap_seconds, args.out_dir)
    elif args.part == "sweep":
        run_sweep(args.shard, args.cap_seconds, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        with open(os.path.join(args.out_dir, f"m101{args.shard}_grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        st = {}
        for s, _, _ in out["sweep"].values():
            st[s] = st.get(s, 0) + 1
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} "
              f"failed {bad[:12]} sweep {json.dumps(st, sort_keys=True)} control "
              f"{json.dumps(out['control'], sort_keys=True)} unsat {out['unsat']}", flush=True)


if __name__ == "__main__":
    main()
