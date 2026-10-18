# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m24: Case A at rank 4 and t = 6 (notes/a9.md, Lemma 61), the search of case_a.py at t = 6.

An anisotropic system with t = 6 and dim V = 7 and an element u of rank 4 has k = 2 and
dim V = t + k - 1, so u is in Case A or Case B (Proposition 26). Case B is job m23 (a6_r4.py). In
Case A, Lemma 48 of notes/case-a.md fixes sigma(u) = e_0, sigma(v_1) = e_1, beta(u, .) and A_u = C,
with C any matrix of its orbit under G = {g in GL(X) : g e_0 = e_0, g e_1 = e_1}. At t = 6 there are
3,124,800 candidate matrices C, too many for the orbit closure of case_a.py, so Lemma 61 lists the
21 orbits by hand: C is (Cbar, c) with Cbar the 4 x 4 map induced on X / X_1 and c : X / X_1 -> X_1;
the orbit depends only on the similarity class of Cbar (rank 3: 11 classes, rank 2: 6 classes) and,
for rank 2, on c restricted to ker Cbar up to the centraliser (1 or 3 orbits per class). The
selfcheck proves the list complete: each representative is a candidate, no two are conjugate under
G (exact linear algebra), and the orbit sizes |G| / |stabiliser| are the hand values and add up to
3,124,800. UNSAT for all 21 would show that no system with t = 6 and dim V = 7 has an element of
rank 4 in Case A; with job m23 (Case B) that would leave only rank 3 for A(6) = 6.

Parts: selfcheck (pure Python), controls (case_a.py's orbits at t = 3, 4 and 5, UNSAT by
Proposition 25 and job m15; needs python-sat), solve (the 21 orbits at t = 6; needs python-sat),
grade (the pre-registered predictions of m24/predictions.md). Each instance is solved by
case_a.solve_one, unchanged, in a child process with a time budget.

Usage: python a6_casea.py --part selfcheck|controls|solve|grade [--budget-minutes 6]
                          [--group-minutes 140] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import time

import case_a as ca
import sat_aniso as sa

T = 6
CONTROLS = (3, 4, 5)

# Cbar on X / X_1 with basis f_j = [e_(j+2)], given by the columns Cbar f_j as 4-bit vectors. Each
# kernel is span(f_0) (rank 3) or span(f_0, f_1) (rank 2). F4 is the companion matrix of
# x^2 + x + 1, F8a of x^3 + x + 1 and F8b of x^3 + x^2 + 1.
RANK3 = (("J4", (0, 1, 2, 4)), ("J3+1", (0, 1, 2, 8)), ("J2+I", (0, 1, 4, 8)),
         ("J2+J2(1)", (0, 1, 4, 12)), ("J2+F4", (0, 1, 8, 12)), ("0+I", (0, 2, 4, 8)),
         ("0+J2(1)+1", (0, 2, 6, 8)), ("0+J3(1)", (0, 2, 6, 12)), ("0+F4+1", (0, 4, 6, 8)),
         ("0+F8a", (0, 4, 8, 6)), ("0+F8b", (0, 4, 8, 10)))
# Rank 2: (name, columns, the values (c(f_0), c(f_1)) in X_1 = span(e_0, e_1), one per orbit).
RANK2 = (("0+0+I", (0, 0, 4, 8), ((1, 2),)), ("0+0+J2(1)", (0, 0, 4, 12), ((1, 2),)),
         ("0+0+F4", (0, 0, 8, 12), ((1, 2),)),
         ("J2+0+1", (0, 0, 1, 8), ((1, 2), (2, 1), (3, 1))),
         ("J3+0", (0, 0, 1, 4), ((1, 2), (2, 1), (3, 1))),
         ("J2+J2", (0, 0, 1, 2), ((1, 2),)))

# Hand values (notes/a9.md, Lemma 61): orbit size = (size of the similarity class of Cbar in
# M_4(F_2)) x 64 for rank 3, and x 96 / (number of orbits of the class) for rank 2.
HAND_SIZES = (161280, 322560, 107520, 322560, 215040, 7680, 161280, 322560, 430080, 184320,
              184320, 53760, 161280, 107520, 80640, 80640, 80640, 40320, 40320, 40320, 20160)
CANDIDATES = 155 * 20160        # 4-dim R through e_1, times the bases of R
HAND_STAB = {0: 32, 5: 672, 20: 256}


def matrix(cbar, c):
    """C with C e_0 = C e_1 = 0 and C e_(j+2) = c[j] + (Cbar f_j shifted to e_2, ..., e_5)."""
    cols = [0, 0] + [(c[j] if j < len(c) else 0) | (cbar[j] << 2) for j in range(4)]
    return sa.from_cols(cols, T)


def reps():
    """[(name, C)] for the 21 orbits, in the order of HAND_SIZES."""
    out = [(name, matrix(cbar, (2,))) for name, cbar in RANK3]
    for name, cbar, cs in RANK2:
        for c in cs:
            out.append((name if len(cs) == 1 else f"{name} y={c[0]}", matrix(cbar, c)))
    return out


def is_candidate(C):
    """C e_0 = C e_1 = 0, rank 4 and e_1 in Im C."""
    cols = [sa.mat_apply(C, 1 << j, T) for j in range(2, T)]
    return (sa.mat_apply(C, 1, T) == 0 and sa.mat_apply(C, 2, T) == 0
            and sa.rank_f2(cols) == 4 and sa.rank_f2(cols + [2]) == 4)


# ---------- G-conjugacy by linear algebra ----------

E01 = 1 | (1 << (T + 1))                                            # entries (0, 0) and (1, 1)
GBASIS = [1 << (T * r + c) for c in range(2, T) for r in range(T)]  # free entries of g


def transporters(C1, C2, first=False):
    """Every g in G with g C1 = C2 g (that is, g C1 g^-1 = C2); with first, at most one."""
    nb = len(GBASIS)
    imgs = [sa.mat_mul(G, C1, T) ^ sa.mat_mul(C2, G, T) for G in GBASIS]
    rhs = sa.mat_mul(E01, C1, T) ^ sa.mat_mul(C2, E01, T)
    rows = [sum(((m >> p) & 1) << k for k, m in enumerate(imgs)) | (((rhs >> p) & 1) << nb)
            for p in range(T * T)]
    ns = sa.nullspace(rows, nb + 1)
    out = []
    for m in range(1 << len(ns)):
        x = sa.combine(ns, m)
        if not (x >> nb) & 1:
            continue
        g = E01 ^ sa.combine(GBASIS, x & ((1 << nb) - 1))
        if sa.rank_f2(sa.rows_of(g, T)) == T:
            out.append(g)
            if first:
                break
    return out


def orbit_size(C):
    return ca.group_order(T) // len(transporters(C, C))


# ---------- selfcheck ----------

def selfcheck():
    rs = reps()
    mats = [C for _, C in rs]
    sizes = [orbit_size(C) for C in mats]
    gens = ca.generators(T)[:2]
    st = {"reps": len(rs), "names": [n for n, _ in rs],
          "candidate": [is_candidate(C) for C in mats],
          "d": [ca.invariants(C, T)[0] for C in mats],
          "group_order": ca.group_order(T), "orbit_sizes": sizes, "total": sum(sizes),
          "stabilisers": {str(i): len(transporters(mats[i], mats[i])) for i in HAND_STAB},
          "conjugate_pairs": [[i, j] for i, j in itertools.combinations(range(len(mats)), 2)
                              if transporters(mats[i], mats[j], first=True)],
          "transporter_finds_g": all(g in transporters(C, ca.conj(g, C, T))
                                     for C in mats for g in gens)}
    st["graded"] = {
        "reps": st["reps"] == 21 and len(set(mats)) == 21,
        "candidates": all(st["candidate"]),
        "d_split": st["d"] == [1] * 11 + [2] * 10,
        "group_order": st["group_order"] == 60 * 56 * 48 * 32 == 5160960,
        "orbit_sizes": tuple(sizes) == HAND_SIZES,
        "total": st["total"] == CANDIDATES == 3124800,
        "stabilisers": all(st["stabilisers"][str(i)] == s for i, s in HAND_STAB.items()),
        "no_two_conjugate": st["conjugate_pairs"] == [],
        "transporter_finds_g": st["transporter_finds_g"]}
    return st


# ---------- solving and grading ----------

def run_controls(solver, budget_seconds, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    counts = {}
    for t in CONTROLS:
        for idx, (Au, _) in enumerate(ca.orbits(t)):
            res = ca.solve_one(t, idx, Au, solver, budget_seconds, out_dir)
            counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


def run_solve(solver, budget_seconds, group_seconds, out_dir):
    """The 21 orbits at t = 6, in order; once the total budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for idx, (name, Au) in enumerate(reps()):
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = {"status": "SKIPPED", "t": T, "orbit": idx, "Au": Au,
                   "name": ca.instance_name(T, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = ca.solve_one(T, idx, Au, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("ca_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


# Controls: orbits of case_a.py at t = 3, 4, 5 (1, 3 and 9). Pre-registered (m24/predictions.md).
CONTROL_COUNTS = {3: 1, 4: 3, 5: 9}


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    for t, n in CONTROL_COUNTS.items():
        for i in range(n):
            name = ca.instance_name(t, i)
            s = results.get(name, {}).get("status", "missing")
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    # A verified model anywhere must have every rank <= t - 2 and the facts of Lemma 48.
    for name, r in results.items():
        if r.get("status") != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - 2
        graded[name + "_lemma48"] = all(fa.get(key) for key in ("phi_onto", "ker_A_u", "A_v"))
    status = [results.get(ca.instance_name(T, i), {}).get("status", "missing") for i in range(21)]
    counts = {s: status.count(s) for s in sorted(set(status))}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "counts_6": counts, "status_6": status,
            "times": times, "all_unsat_6": all(s == "UNSAT" for s in status),
            "any_sat_6": "SAT" in status}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "grade"],
                    default="selfcheck")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=6.0)
    ap.add_argument("--group-minutes", type=float, default=140.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        out = run_controls(args.solver, 120, args.out_dir)
        print(f"SUMMARY controls {json.dumps(out, sort_keys=True)}", flush=True)
    elif args.part == "solve":
        out = run_solve(args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY solve t6 orbits 21 {json.dumps(out, sort_keys=True)}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"all_unsat_6 {out['all_unsat_6']} any_sat_6 {out['any_sat_6']}", flush=True)
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
