# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m53: the kind-P class of (B6) with d = 3 (pair orbit 1 of job m42) at t = 7 and dim V = 9,
split by the second matrix A_(h_1) into the 40 classes of Proposition 30 (notes/a42.md).

Proposition 30 (a): for every n in N = ker phi outside span(u), A_n lies in Adm = {A : A x0 = 0,
A(X) inside R, rank of A on X_1 at most 2, A != 0, A != A_u}. (b), (c): up to the stabiliser G of
(x0, P, A_u) and n -> n + u, Adm has 40 classes in kind P. m42.py's normal form (sigma(u) = e_0,
P = span(e_1, ..., e_6), v_0 = u, phi(v_1) = phi(v_2) = 0, phi(v_(2 + j)) = e_j) fixes nothing
beyond x0, P, A_u and the basis of V that phi forces, so a base change by G followed by a new
basis of V (v_1 = n or n + u, v_2 completing N) brings A_(v_1) to a chosen representative. The
kind-P class is therefore empty if and only if all 40 instances below are unsatisfiable.

Each instance is m42.py's CNF (sat_aniso.encode without echelon form; sigma(u), A_u and phi fixed
by unit clauses; the hints of Proposition 29 (c) and (2), (3) of a10.md on ker phi), copied below
unchanged, with A_u the kind-P matrix e_4 -> e_1, e_5 -> e_2, e_6 -> e_3 (kernel span(e_0, ..., e_3),
image span(e_1, e_2, e_3), the pair of orbit 1, which is a single class of A_u), plus 49 unit
clauses fixing A_(v_1). The representatives are m52.py's (union-find roots for kind P, in m52's
adapted coordinates x0 = e_6, P = span(e_0, ..., e_5)), moved to m42's coordinates by
e_k -> e_(k + 1) (k < 6), e_6 -> e_0, which sends m52's A_u to the A_u above.

Parts:
    check   gate: m52's kind-P computation must give |G| = 86016, 176126 maps and 40 classes
            (6 / 20 / 14 by rank on X_1); the change of coordinates is a ring map and sends m52's
            A_u to A_u; every representative is in Adm in m42's coordinates; the instance has
            m42's 79 hints; the planted system at t = 6 with A_(v_1) fixed to its own map is
            accepted (and rejected when one entry is flipped) and solved SAT and verified.
    solve   the 40 instances, each an equal share of the time left (at most --cap-seconds).
    grade   graded checks, and the statuses by rank on X_1.

Usage: python m53.py --part check|solve|grade [--group-minutes 140] [--cap-seconds 210]
                     [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

import m52
import sat_aniso as sa

T = 7
D = 9
P = 6
X1 = (8, 4, 2, 1)
R = (8, 4, 2)
AU = (1 << 11) | (1 << 19) | (1 << 27)      # entries (1, 4), (2, 5), (3, 6)
HAND_HINTS_B6 = 79
HAND_P = {"0": 6, "1": 20, "2": 14}
PLANTED_BUDGET = 240.0
MIN_BUDGET = 20.0


# ---------- from m42.py, unchanged ----------

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


def dim_meet(a, b):
    return len(a) + len(b) - len(rref(list(a) + list(b)))


def cols_of(g, t):
    return [sa.mat_apply(g, 1 << c, t) for c in range(t)]


def kernel(A, t):
    return rref(sa.nullspace(sa.rows_of(A, t), t))


def column_space(A, t):
    return rref(cols_of(A, t))


def ann(rows, t):
    """Basis of {f : f . s = 0 for every s in rows}."""
    return sa.nullspace(list(rows), t)


def p_basis(p):
    return rref([1 << j for j in range(1, p + 1)])


def phis_for(d, p):
    kd = d - p
    return (None,) + (0,) * (kd - 1) + tuple(1 << j for j in range(1, p + 1))


def encode_fixed(t, d, au, s0, phis):
    """sat_aniso.encode (no echelon form) with A_0 = au, s_0 = s0 and B_0i = phis[i] fixed by unit
    clauses (as encode_fixed in m41.py, without fixed s_i)."""
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]

    def unit(var, bit):
        cnf.clauses.append([var] if bit else [-var])

    for r in range(t):
        unit(S[0][r], (s0 >> r) & 1)
        for c in range(t):
            unit(A[0][r][c], (au >> (t * r + c)) & 1)
    for i in range(1, d):
        if phis[i] is None:
            continue
        for r in range(t):
            unit(B[(0, i)][r], (phis[i] >> r) & 1)
    return cnf, names


def add_hints(cnf, names, t, kd, au, s0, pvecs):
    """For n = v_i, 0 < i < kd (in ker phi): A_n x0 = 0 and sigma(n) in X_1 by (3) of a10.md; A_n
    maps P + span(x0) into R and beta(n, n') lies in X_1 by (2). Returns the number of linear
    conditions added."""
    A, S, B = names[0], names[1], names[2]
    ann_x1 = ann(kernel(au, t), t)
    ann_r = ann(column_space(au, t), t)
    ext = rref(list(pvecs) + [s0])
    n = 0
    for i in range(1, kd):
        for row in range(t):
            cnf.xor_eq([A[i][row][c] for c in range(t) if (s0 >> c) & 1], 0)
            n += 1
        for y in ext:
            for f in ann_r:
                cnf.xor_eq([A[i][row][c] for row in range(t) if (f >> row) & 1
                            for c in range(t) if (y >> c) & 1], 0)
                n += 1
        for f in ann_x1:
            cnf.xor_eq([S[i][row] for row in range(t) if (f >> row) & 1], 0)
            n += 1
    for i, j in itertools.combinations(range(1, kd), 2):
        for f in ann_x1:
            cnf.xor_eq([B[(i, j)][row] for row in range(t) if (f >> row) & 1], 0)
            n += 1
    return n


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


def planted_spec():
    return {"name": "r3b_planted", "kind": "planted", "t": 6, "d": 6, "p": 3,
            "au": planted()[0][0]}


def params(spec):
    """(t, d, au, s0, phis, kd, pvecs) of an instance."""
    if spec["kind"] == "planted":
        As, ss, B = planted()
        phis = (None,) + tuple(B[(0, i)] for i in range(1, 6))
        return 6, 6, As[0], ss[0], phis, 3, [phis[i] for i in (3, 4, 5)]
    t, d, p = spec["t"], spec["d"], spec["p"]
    return t, d, spec["au"], 1, phis_for(d, p), d - p, list(p_basis(p))


def m42_build(spec):
    t, d, au, s0, phis, kd, pvecs = params(spec)
    cnf, names = encode_fixed(t, d, au, s0, phis)
    n = add_hints(cnf, names, t, kd, au, s0, pvecs)
    return cnf, names, n


def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


# ---------- the split ----------

def shift(v):
    """m52's adapted coordinates to m42's: e_k -> e_(k + 1) for k < 6, e_6 -> e_0."""
    return ((v << 1) & 127) | (v >> 6 & 1)


def to_m42(cols):
    """The t^2-bit mask (entry (r, c) at bit t r + c) of the map with m52 columns cols, in m42's
    coordinates."""
    m = 0
    for j in range(T):
        col, c = shift(cols[j]), shift(1 << j).bit_length() - 1
        for r in range(T):
            if col >> r & 1:
                m |= 1 << (T * r + c)
    return m


def column(m, c, t=T):
    return sum(((m >> (t * r + c)) & 1) << r for r in range(t))


def rank_on_x1(m):
    return len(rref([column(m, c) for c in range(4)]))


def admissible(m):
    """m (m42's coordinates) is in Adm: kills x0 = e_0, image inside R, rank on X_1 at most 2,
    not 0, not A_u."""
    cols = [column(m, c) for c in range(T)]
    return (cols[0] == 0 and all(in_span(R, v) for v in cols) and rank_on_x1(m) <= 2
            and m != 0 and m != AU)


def fix_a1(cnf, names, t, a1):
    """49 unit clauses A_(v_1) = a1. Returns the number added."""
    A = names[0]
    for r in range(t):
        for c in range(t):
            cnf.clauses.append([A[1][r][c]] if (a1 >> (t * r + c)) & 1 else [-A[1][r][c]])
    return t * t


def build(spec):
    cnf, names, hints = m42_build(spec)
    units = fix_a1(cnf, names, spec["t"], spec["a1"])
    return cnf, names, hints, units


def spec_of(k, rep):
    return {"name": f"r3p_t7_B6_o001_a{k:02d}", "kind": "main", "t": T, "d": D, "p": P, "pair": 1,
            "x1": list(X1), "r": list(R), "au": AU, "a1": rep["m42"], "rank_x1": rep["rank_x1"],
            "m52_index": rep["index"], "m52_size": rep["size"]}


def planted_with_a1(a1=None):
    spec = planted_spec()
    spec["a1"] = planted()[0][1] if a1 is None else a1
    return spec


# ---------- solving (as m42.py and m49.py, with build() above) ----------

def child(spec, solver, path):
    from pysat.solvers import Solver
    cnf, names, _, _ = build(spec)
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
        t, d, au, s0, phis, kd, pvecs = params(spec)
        As, ss = res["A"], res["s"]
        B = {(i, k): v for i, k, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        nf = (As[0] == au and ss[0] == s0 and As[1] == spec["a1"]
              and all(phis[i] is None or B[(0, i)] == phis[i] for i in range(1, d)))
        res["verified"] = sa.is_system(at, sv, d, t) and sa.anisotropic(sv) and nf
        ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
        res["max_rank"] = max(ranks)
        res["rank_u"] = ranks[0]
    write(res, out_dir)
    print(f"solve {spec['name']}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


# ---------- parts ----------

def ring_map_check(trials, seed):
    """to_m42 respects products, the identity and A_u (catches a wrong index convention)."""
    rng = random.Random(seed)
    ok = to_m42(m52.IDENT) == sum(1 << (T * r + r) for r in range(T))
    for _ in range(trials):
        a = tuple(rng.getrandbits(T) for _ in range(T))
        b = tuple(rng.getrandbits(T) for _ in range(T))
        ok = ok and to_m42(m52.compose(a, b)) == sa.mat_mul(to_m42(a), to_m42(b), T)
    return ok


def check(solver, out_dir):
    start = time.time()
    graded, st = {}, {}
    # The gate: m52's kind-P count (Proposition 30 (c)).
    kp = m52.run_kind("P", random.Random(52))
    st["m52_P"] = {k: v for k, v in kp.items() if k != "reps"}
    s = kp["structure"]
    graded["m52_structure"] = s["rank_au"] == 3 and s["ker_is_x1"] and s["r_in_x1"] and s["kind_ok"]
    graded["m52_group"] = kp["group_checked"] and kp["order"] == 86016
    graded["m52_valid"] = kp["valid"] == m52.HAND_VALID and kp["action_closed"]
    graded["m52_sizes"] = kp["sizes_ok"]
    graded["m52_orbits"] = kp["orbits"] == 40 and kp["orbits_by_rank_x1"] == HAND_P
    # The change of coordinates.
    graded["ring_map"] = ring_map_check(200, 53)
    graded["au_moves"] = to_m42(m52.au_of("P")) == AU
    graded["au_pair_1"] = (kernel(AU, T) == X1 and column_space(AU, T) == R
                           and dim_meet(X1, R) == 3 and dim_meet(R, p_basis(P)) == 3
                           and not in_span(R, 1))
    reps = []
    for rep in kp["reps"]:
        m = to_m42(tuple(rep["cols"]))
        reps.append(dict(rep, m42=m))
    graded["reps_admissible"] = len(reps) == 40 and all(admissible(r["m42"]) for r in reps)
    graded["reps_distinct"] = len({r["m42"] for r in reps} | {r["m42"] ^ AU for r in reps}) == 80
    graded["reps_rank"] = all(rank_on_x1(r["m42"]) == r["rank_x1"] for r in reps)
    with open(os.path.join(out_dir, "m53_reps.json"), "w") as f:
        json.dump(reps, f, indent=1)
    # The instance: m42's hints, and the 49 units.
    cnf, names, hints, units = build(spec_of(0, reps[0]))
    st["probe"] = {"hints": hints, "units_added": units, "vars": cnf.nv, "clauses": len(cnf.clauses)}
    graded["probe"] = hints == HAND_HINTS_B6 and units == T * T and units_consistent(cnf)
    # The positive control.
    As, ss, B = planted()
    pc, pn, _, _ = build(planted_with_a1())
    graded["planted_accepted"] = sa.satisfies(pc, sa.assignment(pc, pn, As, ss, B, 6, 6))
    qc, qn, _, _ = build(planted_with_a1(As[1] ^ 1))
    graded["planted_flip_rejected"] = not sa.satisfies(qc, sa.assignment(qc, qn, As, ss, B, 6, 6))
    res = solve_one(planted_with_a1(), solver, PLANTED_BUDGET, out_dir)
    if res["status"] in ("SAT", "UNSAT"):
        graded["planted_sat"] = res["status"] == "SAT" and bool(res.get("verified"))
    else:
        st["planted_ungraded"] = res["status"]
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


def run_solve(solver, group_seconds, cap_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    with open(os.path.join(out_dir, "m53_reps.json")) as f:
        reps = json.load(f)
    sps = [spec_of(k, rep) for k, rep in enumerate(reps)]
    counts = {}
    for k, sp in enumerate(sps):
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(sp, status="SKIPPED")
            write(res, out_dir)
        else:
            budget = min(cap_seconds, max(min(MIN_BUDGET, left), left / (len(sps) - k)))
            res = solve_one(sp, solver, budget, out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    print(f"SUMMARY solve instances {len(sps)} {json.dumps(counts, sort_keys=True)}", flush=True)


def grade(out_dir):
    """Graded: the check, and every SAT verified (a system, anisotropic, normal form with A_u and
    A_(v_1) as fixed, rank A_u = 3, every rank <= 4). Reported: statuses by rank on X_1."""
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    counts, by_rank, rows = {}, {}, {}
    for fn in sorted(os.listdir(out_dir)):
        if not (fn.startswith("r3p_") and fn.endswith(".json")) or fn.endswith(".child.json"):
            continue
        with open(os.path.join(out_dir, fn)) as f:
            r = json.load(f)
        s = r.get("status")
        counts[s] = counts.get(s, 0) + 1
        br = by_rank.setdefault(str(r["rank_x1"]), {})
        br[s] = br.get(s, 0) + 1
        rows[r["name"]] = {"status": s, "rank_x1": r["rank_x1"], "wall_seconds": r.get("wall_seconds")}
        if s == "SAT":
            graded[r["name"] + "_verified"] = bool(r.get("verified"))
            graded[r["name"] + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    times = sorted(v["wall_seconds"] for v in rows.values()
                   if v["status"] == "UNSAT" and v["wall_seconds"] is not None)
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "by_rank_x1": by_rank,
            "rows": rows, "instances": len(rows), "closed": counts.get("UNSAT", 0),
            "median_unsat_seconds": times[len(times) // 2] if times else None,
            "class_empty": counts.get("UNSAT", 0) == 40, "any_sat_7": counts.get("SAT", 0) > 0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "child", "grade"], default="check")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--group-minutes", type=float, default=140.0)
    ap.add_argument("--cap-seconds", type=float, default=210.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.solver, args.group_minutes * 60, args.cap_seconds, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"closed {out['closed']} of {out['instances']} class_empty {out['class_empty']} "
              f"any_sat_7 {out['any_sat_7']}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.solver, args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
