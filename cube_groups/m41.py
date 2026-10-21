# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m41: the rank-3 configuration (A5) for t = 7 and dim V = 9 (notes/a26.md, Lemma 82), one
exact SAT instance with A_u fixed.

Setting and encoding as in sat_aniso.py. By Proposition 29(c) (notes/a24.md), if an anisotropic
system with t = 7 and dim V = 9 has no element of rank 4, each element u of rank 3 is in (A5), (B6)
or (B5). In (A5), x0 = sigma(u) lies in P = beta(u, V), dim P = 6 and ker phi has dimension 3, and
Lemma 79 gives R = Im A_u inside X_1 = ker A_u, x0 outside R and X_1 = R + span(x0) inside P.
Lemma 82 of notes/a26.md takes bases with

    x0 = e_0,  R = span(e_1, e_2, e_3),  P = span(e_0, ..., e_5),
    v_0 = u,  phi(v_1) = phi(v_2) = 0,  phi(v_(3+j)) = e_j for 0 <= j <= 5,

and shows that all 168 candidates for A_u (A_u kills e_0, ..., e_3, image R) form one orbit under
G = {g in GL(X) : g e_0 = e_0, g R = R, g P = P}; so A_u e_4 = e_1, A_u e_5 = e_2, A_u e_6 = e_3.
(A5) exists iff the CNF of sat_aniso.encode (without its echelon form) with these values fixed by
unit clauses is satisfiable. The variant "hint" adds 110 unit clauses for facts already proved
(Lemma 79 (a), (c), (d) and (3) of a10.md): for v_1, v_2 in ker phi, A_(v_i) kills X_1, maps P into
R, and sigma(v_i) lies in X_1; for v_3 over x0, A_(v_3) x0 = x0, A_(v_3) kills R and sigma(v_3) lies
in R.

Controls, as in a7_casea.py (job m39): the same encoder at t = 5 with the parameters of case_a.py
gives exactly case_a's CNF (9 orbits, UNSAT by Lemma 52 and jobs m15, m39), and a planted system at
t = 6 (three copies of Lemma 63 (ii), u = a_1 + a_2 + a_3) must be SAT.

Matrices are t^2-bit masks with entry (r, c) at bit t r + c, as in sat_aniso.py.

Parts: selfcheck (pure Python), controls (needs python-sat), solve --kind main|hint (needs
python-sat), grade (the pre-registered predictions of m41/predictions.md).

Usage: python m41.py --part selfcheck|controls|solve|grade [--kind main|hint] [--minutes 140]
                     [--out-dir DIR]
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

T = 7
D = 9
E = [1 << i for i in range(T)]
R_MASK = E[1] | E[2] | E[3]
X1_MASK = E[0] | R_MASK
P_MASK = X1_MASK | E[4] | E[5]
PHI = (None, 0, 0, E[0], E[1], E[2], E[3], E[4], E[5])     # phi(v_i); v_0 = u
T5_PHI = (None, 1, 2, 4, 8, 16)                            # case_a.wanted_phi at t = 5
CANDIDATES = 168
MAIN_UNITS = T + T * T + (D - 1) * T                       # 112
HINT_UNITS = 2 * 4 * T + 2 * 2 * 4 + 2 * 3 + T + 3 * T + 4  # 110


# ---------- the matrix A_u and its orbit ----------

def rep():
    return sa.from_cols([0, 0, 0, 0, E[1], E[2], E[3]], T)


def is_candidate(A):
    """A kills e_0, ..., e_3, its image lies in R, and it has rank 3 (so the image is R)."""
    cols = [sa.mat_apply(A, E[j], T) for j in range(T)]
    return (all(c == 0 for c in cols[:4]) and all((c & ~R_MASK) == 0 for c in cols)
            and sa.rank_f2(cols) == 3)


def candidates():
    out = []
    for cols in itertools.product([x << 1 for x in range(8)], repeat=3):
        if sa.rank_f2(list(cols)) == 3:
            out.append(sa.from_cols([0, 0, 0, 0] + list(cols), T))
    return sorted(out)


# Transvections I + E_ij (g e_j = e_j + e_i) that fix e_0 and keep R and P; they generate G.
ALLOWED = ([(i, j) for j in (1, 2, 3) for i in (1, 2, 3) if i != j]
           + [(i, j) for j in (4, 5) for i in range(6) if i != j]
           + [(i, 6) for i in range(6)])


def generators():
    return [ca.identity(T) ^ (1 << (T * i + j)) for i, j in ALLOWED]


def orbit(start):
    gens = generators()
    orb = {start}
    frontier = [start]
    while frontier:
        nxt = []
        for A in frontier:
            for g in gens:
                B = ca.conj(g, A, T)
                if B not in orb:
                    orb.add(B)
                    nxt.append(B)
        frontier = nxt
    return orb


# ---------- the encoding (as encode_fixed in a7_casea.py) ----------

def encode_fixed(t, d, au, s0, phis, fixed_s=None):
    """sat_aniso.encode (no echelon form) with A_0 = au, s_0 = s0, B_0i = phis[i] (unless None)
    and s_i = fixed_s[i] fixed by unit clauses."""
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]

    def unit(var, bit):
        cnf.clauses.append([var] if bit else [-var])

    for r in range(t):
        unit(S[0][r], (s0 >> r) & 1)
        for c in range(t):
            unit(A[0][r][c], (au >> (t * r + c)) & 1)
    for i, s in sorted((fixed_s or {}).items()):
        for r in range(t):
            unit(S[i][r], (s >> r) & 1)
    for i in range(1, d):
        if phis[i] is None:
            continue
        for r in range(t):
            unit(B[(0, i)][r], (phis[i] >> r) & 1)
    return cnf, names


def add_hints(cnf, names):
    """Lemma 79 (d): A_(v_1), A_(v_2) kill X_1 and map P into R; (3): sigma(v_1), sigma(v_2) in
    X_1 and A_(v_3) x0 = x0; Lemma 79 (a): A_(v_3) kills R; Lemma 79 (c): sigma(v_3) in R."""
    A, S = names[0], names[1]

    def unit(var, bit):
        cnf.clauses.append([var] if bit else [-var])

    for i in (1, 2):
        for c in range(4):
            for r in range(T):
                unit(A[i][r][c], 0)
        for c in (4, 5):
            for r in (0, 4, 5, 6):
                unit(A[i][r][c], 0)
        for r in (4, 5, 6):
            unit(S[i][r], 0)
    for r in range(T):
        unit(A[3][r][0], r == 0)
        for c in (1, 2, 3):
            unit(A[3][r][c], 0)
    for r in (0, 4, 5, 6):
        unit(S[3][r], 0)


# ---------- the planted control (three copies of Lemma 63 (ii), as in m32.py, a7_casea.py) ----------

def sigma_old(v):
    """X: E_i = bit 2i, F_i = bit 2i + 1; V: a_i = bit 2i, b_i = bit 2i + 1;
    sigma(a_i) = sigma(b_i) = E_i, sigma(a_i + b_i) = F_i, no cross terms."""
    out = 0
    for i in range(3):
        a, b = (v >> (2 * i)) & 1, (v >> (2 * i + 1)) & 1
        if a ^ b:
            out ^= 1 << (2 * i)
        elif a:
            out ^= 1 << (2 * i + 1)
    return out


def alpha_old(v):
    """A_(a_i) = A_(b_i) = the projection onto span(F_i) along the rest, A_(a_i + b_i) = 0."""
    out = 0
    for i in range(3):
        if ((v >> (2 * i)) ^ (v >> (2 * i + 1))) & 1:
            out ^= sa.entries(6, [(2 * i + 1, 2 * i + 1)])
    return out


def planted():
    """(As, ss, B) at t = 6, d = 6 in the basis h_0 = a_1 + a_2 + a_3 = u, h_1 = a_1, h_2 = a_2
    (phi = 0), h_3, h_4, h_5 = b_1, b_2, b_3, after the change of X-basis of m32.py (skew)."""
    t = 6
    nb = sa.from_cols([21, 2, 8, 32, 6, 16], t)
    c = sa.mat_inv(nb, t)
    hs = [21, 1, 4, 2, 8, 32]
    As = [sa.mat_mul(sa.mat_mul(c, alpha_old(v), t), nb, t) for v in hs]
    ss = [sa.mat_apply(c, sigma_old(v), t) for v in hs]
    B = {(i, k): sa.mat_apply(c, sigma_old(hs[i] ^ hs[k]) ^ sigma_old(hs[i]) ^ sigma_old(hs[k]), t)
         for i in range(t) for k in range(i + 1, t)}
    return As, ss, B


# ---------- instances ----------

def main_spec(kind):
    return {"name": f"a5x_{kind}", "kind": kind, "au": rep(), "t": T, "d": D}


def planted_spec():
    return {"name": "a5x_planted", "kind": "planted", "au": planted()[0][0], "t": 6, "d": 6}


def t5_specs():
    return [{"name": f"a5x_t5_{i}", "kind": "t5", "idx": i, "au": Au, "t": 5, "d": 6}
            for i, (Au, _) in enumerate(ca.orbits(5))]


def params(spec):
    """(t, d, au, s0, phis, fixed_s) of an instance."""
    kind = spec["kind"]
    if kind in ("main", "hint"):
        return T, D, spec["au"], E[0], PHI, {}
    if kind == "t5":
        return 5, 6, spec["au"], 1, T5_PHI, {1: 2}
    As, ss, B = planted()
    return 6, 6, As[0], ss[0], (None,) + tuple(B[(0, i)] for i in range(1, 6)), {}


def build(spec):
    t, d, au, s0, phis, fixed_s = params(spec)
    cnf, names = encode_fixed(t, d, au, s0, phis, fixed_s)
    if spec["kind"] == "hint":
        add_hints(cnf, names)
    return cnf, names


# ---------- selfcheck ----------

def clause_set(cnf):
    return {tuple(sorted(c)) for c in cnf.clauses}


def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


def selfcheck():
    cand = candidates()
    orb = orbit(rep())
    gens = generators()
    gens_ok = all(sa.rank_f2(sa.rows_of(g, T)) == T and sa.mat_apply(g, E[0], T) == E[0]
                  and all((sa.mat_apply(g, E[j], T) & ~R_MASK) == 0 for j in (1, 2, 3))
                  and all((sa.mat_apply(g, E[j], T) & ~P_MASK) == 0 for j in (4, 5))
                  for g in gens)
    n_base = len(sa.encode(T, D, echelon=False)[0].clauses)
    cnf, names = build(main_spec("main"))
    main_units = len(cnf.clauses) - n_base
    main_ok = units_consistent(cnf)
    n_before = len(cnf.clauses)
    add_hints(cnf, names)
    hint_units = len(cnf.clauses) - n_before
    hint_ok = units_consistent(cnf)
    t5_same = []
    for sp in t5_specs():
        mine = build(sp)[0]
        theirs = ca.encode_case_a(5, sp["au"])[0]
        t5_same.append(mine.nv == theirs.nv and len(mine.clauses) == len(theirs.clauses)
                       and clause_set(mine) == clause_set(theirs))
    As, ss, B = planted()
    at, sv = sa.tables(As, ss, B, 6)
    pc, pn = build(planted_spec())
    st = {"candidates": len(cand), "orbit": len(orb), "orbit_in_candidates": orb <= set(cand),
          "rep_candidate": is_candidate(rep()), "generators": len(gens), "generators_ok": gens_ok,
          "main_units": main_units, "hint_units": hint_units,
          "consistent": main_ok and hint_ok, "cnf_vars": cnf.nv, "cnf_clauses": len(cnf.clauses),
          "t5_same_as_case_a": t5_same,
          "planted": {"system": sa.is_system(at, sv, 6, 6), "anisotropic": sa.anisotropic(sv),
                      "ker_phi_3": [B[(0, i)] for i in (1, 2)] == [0, 0],
                      "cnf_accepts": sa.satisfies(pc, sa.assignment(pc, pn, As, ss, B, 6, 6))}}
    st["graded"] = {
        "candidates": len(cand) == CANDIDATES and all(is_candidate(A) for A in cand),
        "one_orbit": len(orb) == CANDIDATES and st["orbit_in_candidates"],
        "rep": st["rep_candidate"],
        "generators": len(gens) == len(ALLOWED) == 22 and gens_ok,
        "units": main_units == MAIN_UNITS and hint_units == HINT_UNITS,
        "consistent": st["consistent"],
        "t5_same_as_case_a": len(t5_same) == 9 and all(t5_same),
        "planted": all(st["planted"].values())}
    return st


# ---------- solving ----------

def child(spec, solver, path):
    from pysat.solvers import Solver
    cnf, names = build(spec)
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
        As, ss, B = sa.decode(s.get_model(), names, spec["t"], spec["d"])
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def write(res, out_dir):
    with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
        json.dump(res, f, indent=1)


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
    res.update(spec)
    res.update({"wall_seconds": round(time.time() - start, 2),
                "budget_seconds": round(budget_seconds, 1)})
    if res["status"] == "SAT":
        t, d, au, s0, phis, fixed_s = params(spec)
        As, ss = res["A"], res["s"]
        B = {(i, k): v for i, k, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        nf = (As[0] == au and ss[0] == s0
              and all(phis[i] is None or B[(0, i)] == phis[i] for i in range(1, d))
              and all(ss[i] == v for i, v in fixed_s.items()))
        res["verified"] = sa.is_system(at, sv, d, t) and sa.anisotropic(sv) and nf
        ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
        res["max_rank"] = max(ranks)
        res["rank_u"] = ranks[0]
    write(res, out_dir)
    print(f"solve {spec['name']}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def run_controls(solver, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    counts = {}
    res = solve_one(planted_spec(), solver, 300, out_dir)
    counts["planted_" + res["status"]] = 1
    start = time.time()
    for sp in t5_specs():
        left = 12 * 60 - (time.time() - start)
        if left < 1:
            res = dict(sp, status="SKIPPED")
            write(res, out_dir)
        else:
            res = solve_one(sp, solver, min(180, left), out_dir)
        key = "t5_" + res["status"]
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY controls {json.dumps(counts, sort_keys=True)}", flush=True)
    return counts


# ---------- grading (pre-registered in m41/predictions.md) ----------

def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["selfcheck_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("a5x_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    for name, r in results.items():
        st = r.get("status")
        if r["kind"] == "planted":
            if st in ("SAT", "UNSAT"):
                graded[name] = st == "SAT" and bool(r.get("verified"))
            else:
                ungraded[name] = st
        elif r["kind"] == "t5":
            if st in ("SAT", "UNSAT"):
                graded[name] = st == "UNSAT"
            else:
                ungraded[name] = st
        elif st == "SAT":
            graded[name + "_verified"] = bool(r.get("verified"))
            graded[name + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    status = {n: r.get("status") for n, r in results.items() if r["kind"] in ("main", "hint")}
    return {"graded": graded, "ungraded": ungraded, "status": status,
            "times": {n: r.get("wall_seconds") for n, r in results.items()},
            "any_sat": any(s == "SAT" for s in status.values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--kind", choices=["main", "hint"], default="main")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--minutes", type=float, default=140.0)
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
    elif args.part == "solve":
        res = solve_one(main_spec(args.kind), args.solver, args.minutes * 60, args.out_dir)
        print(f"SUMMARY solve {res['name']} {res['status']}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat {out['any_sat']} {json.dumps(out['status'], sort_keys=True)}", flush=True)
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
