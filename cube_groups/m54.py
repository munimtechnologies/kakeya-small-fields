# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m54: the kind-graph class of (B6) with d = 3 (pair orbit 2 of job m42) at t = 7 and
dim V = 9, split by the second matrix A_(h_1) into the 178 classes of Proposition 30 (notes/a42.md),
run as two batches of 89 (jobs m54a and m54b).

The argument is m53's (notes/a43.md) with kind graph in place of kind P: by Proposition 30 (a)
every n in N = ker phi outside span(u) has A_n in Adm = {A : A x0 = 0, A(X) inside R, rank of A
on X_1 at most 2, A != 0, A != A_u}; by (b), (c) Adm has 178 classes in kind graph up to the
stabiliser G of (x0, P, A_u) and n -> n + u (18 / 94 / 66 by rank on X_1); m42.py's normal form
fixes nothing on N, so the class is empty if and only if all 178 instances are unsatisfiable.

The instances are m53.py's (m42.py's CNF and 79 hints, copied unchanged there, plus 49 unit
clauses A_(v_1) = the representative), with A_u = m42b's own representative of pair orbit 2,
e_4 -> e_3, e_5 -> e_2, e_6 -> e_0 + e_1 (kernel span(e_0, ..., e_3), image R = span(e_3, e_2,
e_0 + e_1): x0 = e_0 not in R, R not inside P = span(e_1, ..., e_6)). The representatives are
m52.py's union-find roots for kind graph, in m52's adapted coordinates (x0 = e_6,
P = span(e_0, ..., e_5), R = span(e_0, e_1, e_2 + e_6)), moved to m42's coordinates by the
permutation Bm: e_0 -> e_3, e_1 -> e_2, e_2 -> e_1, e_3 -> e_4, e_4 -> e_5, e_5 -> e_6, e_6 -> e_0,
which sends x0, P, X_1, R and m52's A_u to those of m42 (checked below, not assumed).

Parts:
    check   gate: m52's kind-graph computation must give |G| = 12288, 176126 maps and 178
            classes (18 / 94 / 66 by rank on X_1); Bm is a ring map and sends m52's A_u to
            m42b's representative; every representative is in Adm in m42's coordinates; the
            instance has m42's 79 hints; the planted control at t = 6 as in m53.
    solve   the batch's 89 instances, each an equal share of the time left (at most
            --cap-seconds).
    grade   graded checks, and the statuses by rank on X_1.

Usage: python m54.py --part check|solve|grade --batch a|b [--group-minutes 140]
                     [--cap-seconds 95] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import time

import m52
import m53
import sat_aniso as sa

T = 7
D = 9
P = 6
X1 = (8, 4, 2, 1)
R = (8, 4, 3)
AU = (1 << 25) | (1 << 19) | (1 << 13) | (1 << 6)   # entries (3, 4), (2, 5), (1, 6), (0, 6)
M42B_REP_O002 = 34086976                             # m45.OPEN["r3b_t7_B6_o002_c000"]
PERM = (3, 2, 1, 4, 5, 6, 0)                         # Bm e_k = e_(PERM[k])
HAND_G = {"0": 18, "1": 94, "2": 66}
HAND_ORDER_G = 12288
CLASSES = 178
BATCHES = {"a": (0, 89), "b": (89, 178)}


def bm(v):
    """m52's adapted coordinates (kind graph) to m42's."""
    out = 0
    for k in range(T):
        if v >> k & 1:
            out |= 1 << PERM[k]
    return out


def to_m42(cols):
    """The t^2-bit mask (entry (r, c) at bit t r + c) of Bm A Bm^(-1), A with m52 columns cols."""
    m = 0
    for j in range(T):
        col, c = bm(cols[j]), PERM[j]
        for r in range(T):
            if col >> r & 1:
                m |= 1 << (T * r + c)
    return m


def admissible(m):
    """m (m42's coordinates) is in Adm for pair orbit 2: kills x0 = e_0, image inside R, rank on
    X_1 at most 2, not 0, not A_u."""
    cols = [m53.column(m, c) for c in range(T)]
    return (cols[0] == 0 and all(m53.in_span(R, v) for v in cols) and m53.rank_on_x1(m) <= 2
            and m != 0 and m != AU)


def spec_of(k, rep):
    return {"name": f"r3g_t7_B6_o002_a{k:03d}", "kind": "main", "t": T, "d": D, "p": P, "pair": 2,
            "x1": list(X1), "r": list(R), "au": AU, "a1": rep["m42"], "rank_x1": rep["rank_x1"],
            "m52_index": rep["index"], "m52_size": rep["size"]}


def ring_map_check(trials, seed):
    """to_m42 respects products and the identity (catches a wrong index convention)."""
    rng = random.Random(seed)
    ok = to_m42(m52.IDENT) == sum(1 << (T * r + r) for r in range(T))
    for _ in range(trials):
        a = tuple(rng.getrandbits(T) for _ in range(T))
        b = tuple(rng.getrandbits(T) for _ in range(T))
        ok = ok and to_m42(m52.compose(a, b)) == sa.mat_mul(to_m42(a), to_m42(b), T)
    return ok


def frame_moves():
    """Bm sends m52's x0, P, X_1 and R (kind graph) to m42's."""
    p_ad = [1 << k for k in range(6)]
    return (bm(m52.X0) == 1
            and m53.rref([bm(v) for v in p_ad]) == m53.p_basis(P)
            and m53.rref([bm(v) for v in m52.X1B]) == X1
            and m53.rref([bm(v) for v in m52.KINDS["graph"]]) == R)


def check(solver, out_dir):
    start = time.time()
    graded, st = {}, {}
    # The gate: m52's kind-graph count (Proposition 30 (c)).
    kg = m52.run_kind("graph", random.Random(54))
    st["m52_graph"] = {k: v for k, v in kg.items() if k != "reps"}
    s = kg["structure"]
    graded["m52_structure"] = s["rank_au"] == 3 and s["ker_is_x1"] and s["r_in_x1"] and s["kind_ok"]
    graded["m52_group"] = kg["group_checked"] and kg["order"] == HAND_ORDER_G
    graded["m52_valid"] = kg["valid"] == m52.HAND_VALID and kg["action_closed"]
    graded["m52_sizes"] = kg["sizes_ok"]
    graded["m52_orbits"] = kg["orbits"] == CLASSES and kg["orbits_by_rank_x1"] == HAND_G
    # The change of coordinates.
    graded["ring_map"] = ring_map_check(200, 54)
    graded["frame_moves"] = frame_moves()
    graded["au_moves"] = to_m42(m52.au_of("graph")) == AU == M42B_REP_O002
    graded["au_pair_2"] = (m53.kernel(AU, T) == X1 and m53.column_space(AU, T) == R
                           and m53.dim_meet(X1, R) == 3 and m53.dim_meet(R, m53.p_basis(P)) == 2
                           and not m53.in_span(R, 1))
    reps = []
    for rep in kg["reps"]:
        reps.append(dict(rep, m42=to_m42(tuple(rep["cols"]))))
    graded["reps_admissible"] = len(reps) == CLASSES and all(admissible(r["m42"]) for r in reps)
    graded["reps_distinct"] = (len({r["m42"] for r in reps} | {r["m42"] ^ AU for r in reps})
                               == 2 * CLASSES)
    graded["reps_rank"] = all(m53.rank_on_x1(r["m42"]) == r["rank_x1"] for r in reps)
    st["batch_by_rank_x1"] = {}
    for b, (lo, hi) in BATCHES.items():
        br = {}
        for r in reps[lo:hi]:
            br[str(r["rank_x1"])] = br.get(str(r["rank_x1"]), 0) + 1
        st["batch_by_rank_x1"][b] = br
    with open(os.path.join(out_dir, "m54_reps.json"), "w") as f:
        json.dump(reps, f, indent=1)
    # The instance: m42's hints, and the 49 units.
    cnf, names, hints, units = m53.build(spec_of(0, reps[0]))
    st["probe"] = {"hints": hints, "units_added": units, "vars": cnf.nv, "clauses": len(cnf.clauses)}
    graded["probe"] = hints == m53.HAND_HINTS_B6 and units == T * T and m53.units_consistent(cnf)
    # The positive control (as in m53).
    As, ss, B = m53.planted()
    pc, pn, _, _ = m53.build(m53.planted_with_a1())
    graded["planted_accepted"] = sa.satisfies(pc, sa.assignment(pc, pn, As, ss, B, 6, 6))
    qc, qn, _, _ = m53.build(m53.planted_with_a1(As[1] ^ 1))
    graded["planted_flip_rejected"] = not sa.satisfies(qc, sa.assignment(qc, qn, As, ss, B, 6, 6))
    res = m53.solve_one(m53.planted_with_a1(), solver, m53.PLANTED_BUDGET, out_dir)
    if res["status"] in ("SAT", "UNSAT"):
        graded["planted_sat"] = res["status"] == "SAT" and bool(res.get("verified"))
    else:
        st["planted_ungraded"] = res["status"]
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


def run_solve(batch, solver, group_seconds, cap_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    with open(os.path.join(out_dir, "m54_reps.json")) as f:
        reps = json.load(f)
    lo, hi = BATCHES[batch]
    sps = [spec_of(k, reps[k]) for k in range(lo, hi)]
    counts = {}
    for i, sp in enumerate(sps):
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(sp, status="SKIPPED")
            m53.write(res, out_dir)
        else:
            budget = min(cap_seconds, max(min(m53.MIN_BUDGET, left), left / (len(sps) - i)))
            res = m53.solve_one(sp, solver, budget, out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    print(f"SUMMARY solve batch {batch} instances {len(sps)} {json.dumps(counts, sort_keys=True)}",
          flush=True)


def grade(batch, out_dir):
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
        if not (fn.startswith("r3g_") and fn.endswith(".json")) or fn.endswith(".child.json"):
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
    lo, hi = BATCHES[batch]
    times = sorted(v["wall_seconds"] for v in rows.values()
                   if v["status"] == "UNSAT" and v["wall_seconds"] is not None)
    return {"batch": batch, "graded": graded, "ungraded": ungraded, "counts": counts,
            "by_rank_x1": by_rank, "rows": rows, "instances": len(rows), "expected": hi - lo,
            "closed": counts.get("UNSAT", 0),
            "median_unsat_seconds": times[len(times) // 2] if times else None,
            "batch_all_unsat": counts.get("UNSAT", 0) == hi - lo,
            "any_sat_7": counts.get("SAT", 0) > 0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--batch", choices=sorted(BATCHES), default="a")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--group-minutes", type=float, default=140.0)
    ap.add_argument("--cap-seconds", type=float, default=95.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.batch, args.solver, args.group_minutes * 60, args.cap_seconds, args.out_dir)
    elif args.part == "grade":
        out = grade(args.batch, args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade batch {args.batch} all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"closed {out['closed']} of {out['instances']} "
              f"batch_all_unsat {out['batch_all_unsat']} any_sat_7 {out['any_sat_7']}", flush=True)
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
