# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m39: Case A at rank 4 for t = 7 and dim V = 9 (notes/a25.md, Lemma 80), an exact SAT search
split by the orbits of A_u.

Setting and encoding as in sat_aniso.py. By Proposition 29 (notes/a24.md) an element u of rank 4 in
an anisotropic system with t = 7 and dim V = 9 has k = 3, and in Case A phi = beta(u, .) maps V onto
X, so ker phi = span(u, n). Lemma 77 gives x0 = sigma(u) outside R = Im A_u and D = ker A_u n R a
plane, so ker A_u = span(x0) + D. Lemma 80 of notes/a25.md takes bases with

    x0 = e_0,  D = span(e_1, e_2),  R = span(e_1, ..., e_4),
    v_0 = u,  v_1 = n,  phi(v_2) = e_0,  phi(v_i) = e_(i-2) for 3 <= i <= 8,

and A_u any candidate (A_u e_0 = A_u e_1 = A_u e_2 = 0, image R) of its orbit under conjugation by
G = {g in GL(X) : g e_0 = e_0, g D = D, g R = R}. There are 20160 candidates, |G| = 6^3 2^14, and
six orbits, told apart by the similarity class of the 2 x 2 map that A_u induces on R / D (zero,
identity, order 3, unipotent, idempotent, nilpotent). So Case A at rank 4 for t = 7 and dim V = 9
exists iff, for one of the six, the CNF of sat_aniso.encode (without its echelon form) with these
values fixed by unit clauses is satisfiable. The variant "hint" adds the facts of (2), (3) and
Lemma 77 (a), (d), (f) as unit clauses: sigma(v_1) in ker A_u, A_(v_1) kills ker A_u and maps into
R, sigma(v_2) in D, A_(v_2) kills D.

Controls: the same encoder at t = 5 with the parameters of case_a.py gives exactly case_a's CNF
(the 9 orbits, UNSAT by Lemma 52 and job m15), and a planted system at t = 6 (three copies of
Lemma 63 (ii), as in m32.py, with u = a_1 + a_2 + a_3, so ker phi has dimension 3) must be SAT.

Matrices are t^2-bit masks with entry (r, c) at bit t r + c, as in sat_aniso.py.

Parts: selfcheck (pure Python: candidates, orbits against the hand counts, the unit clauses, the
t = 5 CNFs, the planted system), controls (needs python-sat), solve --kind main|hint --idx 0,1,2
(needs python-sat), grade (the pre-registered predictions of m39/predictions.md).

Usage: python a7_casea.py --part selfcheck|controls|solve|grade [--which planted|all]
                          [--kind main|hint] [--idx 0,1,2] [--group-minutes 120] [--out-dir DIR]
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
D_MASK = E[1] | E[2]
R_MASK = E[1] | E[2] | E[3] | E[4]
PHI = (None, 0, E[0], E[1], E[2], E[3], E[4], E[5], E[6])     # phi(v_i); v_0 = u, v_1 = n
T5_PHI = (None, 1, 2, 4, 8, 16)                               # case_a.wanted_phi at t = 5

# The six classes, by the map Pbar that A_u induces on R / D (basis [e_3], [e_4]). Each
# representative is given by its columns A_u e_3, ..., A_u e_6 (A_u e_0 = A_u e_1 = A_u e_2 = 0).
CLASSES = ("zero", "id", "f4", "unip", "idem", "nil")
REP_COLS = {"zero": (2, 4, 8, 16), "id": (8, 16, 2, 4), "f4": (16, 24, 2, 4),
            "unip": (8, 24, 2, 4), "idem": (8, 2, 16, 4), "nil": (2, 8, 16, 4)}
# Hand values (notes/a25.md, Lemma 80): orbit size = 96 x (number of bottom rows [Pbar | S]).
HAND_SIZES = {"zero": 576, "id": 1536, "f4": 3072, "unip": 4608, "idem": 6912, "nil": 3456}
CANDIDATES = 20160
GROUP_ORDER = 6 ** 3 * 2 ** 14        # 3538944
HINT_UNITS = 4 + 5 + 21 + 21 + 14
MAIN_UNITS = T + T * T + (D - 1) * T


# ---------- the matrices A_u and their orbits ----------

def rep(cls):
    return sa.from_cols([0, 0, 0] + list(REP_COLS[cls]), T)


def is_candidate(A):
    """A e_0 = A e_1 = A e_2 = 0, image inside R and rank 4 (so the image is R)."""
    cols = [sa.mat_apply(A, E[j], T) for j in range(T)]
    return (cols[0] == cols[1] == cols[2] == 0 and all((c & ~R_MASK) == 0 for c in cols)
            and sa.rank_f2(cols) == 4)


def candidates():
    out = []
    for cols in itertools.product([x << 1 for x in range(16)], repeat=4):
        if sa.rank_f2(list(cols)) == 4:
            out.append(sa.from_cols([0, 0, 0] + list(cols), T))
    return sorted(out)


def pbar(A):
    """Columns (2-bit vectors) of the map that A induces on R / D in the basis [e_3], [e_4]."""
    return (sa.mat_apply(A, E[3], T) >> 3) & 3, (sa.mat_apply(A, E[4], T) >> 3) & 3


def pclass(A):
    c3, c4 = pbar(A)
    if c3 == 0 and c4 == 0:
        return "zero"
    if (c3, c4) == (1, 2):
        return "id"
    tr = (c3 & 1) ^ ((c4 >> 1) & 1)
    det = ((c3 & 1) & ((c4 >> 1) & 1)) ^ (((c3 >> 1) & 1) & (c4 & 1))
    return {(1, 1): "f4", (0, 1): "unip", (1, 0): "idem", (0, 0): "nil"}[(tr, det)]


# Transvections I + E_ij (g e_j = e_j + e_i) that keep e_0, D and R; with GL(2) on each diagonal
# block they generate G.
ALLOWED = ([(1, 2), (2, 1), (3, 4), (4, 3), (5, 6), (6, 5)]
           + [(i, j) for j in (3, 4) for i in (1, 2)]
           + [(i, j) for j in (5, 6) for i in range(5)])


def generators():
    return [ca.identity(T) ^ (1 << (T * i + j)) for i, j in ALLOWED]


def group_order():
    return GROUP_ORDER


def orbits(cand):
    """[(least matrix, orbit as a set)] under conjugation by the generators, and whether every
    orbit stays inside the candidates."""
    gens = generators()
    cset = set(cand)
    left = set(cand)
    out = []
    closed = True
    while left:
        a = min(left)
        orb = {a}
        frontier = [a]
        while frontier:
            nxt = []
            for A in frontier:
                for g in gens:
                    B = ca.conj(g, A, T)
                    if B not in orb:
                        orb.add(B)
                        nxt.append(B)
            frontier = nxt
        closed = closed and orb <= cset
        out.append((a, orb))
        left -= orb
    return out, closed


# ---------- the encoding ----------

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
    """(3): sigma(v_1) in ker A_u, A_(v_1) x0 = 0; (2): Im A_(v_1) in R; Lemma 77 (f): A_(v_1)
    kills D; Lemma 77 (a): sigma(v_2) in D; Lemma 77 (d): A_(v_2) kills D."""
    A, S = names[0], names[1]
    for r in range(3, T):
        cnf.clauses.append([-S[1][r]])
    for r in (0,) + tuple(range(3, T)):
        cnf.clauses.append([-S[2][r]])
    for r in range(T):
        for c in (0, 1, 2):
            cnf.clauses.append([-A[1][r][c]])
    for r in (0, 5, 6):
        for c in range(T):
            cnf.clauses.append([-A[1][r][c]])
    for r in range(T):
        for c in (1, 2):
            cnf.clauses.append([-A[2][r][c]])


# ---------- the planted control (three copies of Lemma 63 (ii), as in m32.py) ----------

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

def main_spec(kind, idx):
    cls = CLASSES[idx]
    return {"name": f"a7ca_{kind}_{idx}_{cls}", "kind": kind, "idx": idx, "cls": cls,
            "au": rep(cls), "t": T, "d": D}


def planted_spec():
    return {"name": "a7ca_planted", "kind": "planted", "idx": -1, "au": planted()[0][0],
            "t": 6, "d": 6}


def t5_specs():
    return [{"name": f"a7ca_t5_{i}", "kind": "t5", "idx": i, "au": Au, "t": 5, "d": 6}
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


def selfcheck():
    cand = candidates()
    orbs, closed = orbits(cand)
    sizes, classes = {}, []
    for _, orb in orbs:
        cl = sorted({pclass(A) for A in orb})
        classes.append(cl)
        if len(cl) == 1:
            sizes[cl[0]] = len(orb)
    own = {cls: any(rep(cls) in orb and {pclass(A) for A in orb} == {cls} for _, orb in orbs)
           for cls in CLASSES}
    gens = generators()
    gens_ok = all(sa.rank_f2(sa.rows_of(g, T)) == T and sa.mat_apply(g, E[0], T) == E[0]
                  and all((sa.mat_apply(g, E[j], T) & ~D_MASK) == 0 for j in (1, 2))
                  and all((sa.mat_apply(g, E[j], T) & ~R_MASK) == 0 for j in (3, 4))
                  for g in gens)
    n_base = len(sa.encode(T, D, echelon=False)[0].clauses)
    cnf, names = encode_fixed(T, D, rep("zero"), E[0], PHI)
    main_units = len(cnf.clauses) - n_base
    n_before = len(cnf.clauses)
    add_hints(cnf, names)
    hint_units = len(cnf.clauses) - n_before
    t5_same = []
    for sp in t5_specs():
        mine = build(sp)[0]
        theirs = ca.encode_case_a(5, sp["au"])[0]
        t5_same.append(mine.nv == theirs.nv and len(mine.clauses) == len(theirs.clauses)
                       and clause_set(mine) == clause_set(theirs))
    As, ss, B = planted()
    at, sv = sa.tables(As, ss, B, 6)
    pc, pn = build(planted_spec())
    st = {"candidates": len(cand), "orbits": len(orbs), "orbit_sizes": sizes,
          "orbit_classes": classes, "closed": closed, "rep_in_own_orbit": own,
          "generators": len(gens), "generators_ok": gens_ok, "main_units": main_units,
          "hint_units": hint_units, "cnf_vars": cnf.nv, "cnf_clauses": len(cnf.clauses),
          "t5_same_as_case_a": t5_same,
          "planted": {"system": sa.is_system(at, sv, 6, 6), "anisotropic": sa.anisotropic(sv),
                      "ker_phi_3": [B[(0, i)] for i in (1, 2)] == [0, 0],
                      "cnf_accepts": sa.satisfies(pc, sa.assignment(pc, pn, As, ss, B, 6, 6))}}
    st["graded"] = {
        "candidates": len(cand) == CANDIDATES == sum(HAND_SIZES.values()),
        "orbits": len(orbs) == 6 and all(len(c) == 1 for c in classes)
                  and sorted(c[0] for c in classes) == sorted(CLASSES),
        "orbit_sizes": sizes == HAND_SIZES,
        "orbit_stabiliser": all(GROUP_ORDER % n == 0 for n in sizes.values()),
        "closed": closed,
        "reps": all(own.values()) and all(is_candidate(rep(c)) for c in CLASSES),
        "generators": len(gens) == 20 and gens_ok,
        "units": main_units == MAIN_UNITS and hint_units == HINT_UNITS,
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


def run_controls(which, solver, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    counts = {}
    res = solve_one(planted_spec(), solver, 300, out_dir)
    counts["planted_" + res["status"]] = 1
    if which == "all":
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


def run_group(kind, idxs, group_seconds, solver, out_dir):
    """The classes idxs in order, each with an equal share of the group time still left; a
    representative that is not a candidate of its class is not run (status MISMATCH)."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for k, idx in enumerate(idxs):
        sp = main_spec(kind, idx)
        budget = (group_seconds - (time.time() - start)) / (len(idxs) - k)
        if not is_candidate(sp["au"]) or pclass(sp["au"]) != sp["cls"]:
            res = dict(sp, status="MISMATCH")
            write(res, out_dir)
        elif budget < 1:
            res = dict(sp, status="SKIPPED")
            write(res, out_dir)
        else:
            print(f"m39 {kind}: {sp['name']} with {budget / 60:.1f} minutes", flush=True)
            res = solve_one(sp, solver, budget, out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    print(f"SUMMARY solve {kind} classes {len(idxs)} {json.dumps(counts, sort_keys=True)}",
          flush=True)
    return counts


# ---------- grading (pre-registered in m39/predictions.md) ----------

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
        if fn.startswith("a7ca_") and fn.endswith(".json") and not fn.endswith(".child.json"):
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
        else:
            graded[name + "_rep"] = st != "MISMATCH"
            if st == "SAT":
                graded[name + "_verified"] = bool(r.get("verified"))
                graded[name + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 4
    status = {n: r.get("status") for n, r in results.items() if r["kind"] in ("main", "hint")}
    counts = {}
    for n, s in status.items():
        kind = results[n]["kind"]
        counts.setdefault(kind, {})
        counts[kind][s] = counts[kind].get(s, 0) + 1
    return {"graded": graded, "ungraded": ungraded, "status": status, "counts": counts,
            "times": {n: r.get("wall_seconds") for n, r in results.items()},
            "any_sat": any(s == "SAT" for s in status.values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--which", choices=["planted", "all"], default="all")
    ap.add_argument("--kind", choices=["main", "hint"], default="main")
    ap.add_argument("--idx", default="0,1,2,3,4,5")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--group-minutes", type=float, default=120.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="{}")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.which, args.solver, args.out_dir)
    elif args.part == "solve":
        idxs = [int(x) for x in args.idx.split(",") if x != ""]
        run_group(args.kind, idxs, args.group_minutes * 60, args.solver, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat {out['any_sat']} {json.dumps(out['counts'], sort_keys=True)}", flush=True)
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
