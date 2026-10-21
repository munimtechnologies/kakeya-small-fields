# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m46: the 42 classes of the rank-3 configuration (B5) for t = 7 and dim V = 9 that job m42c
left UNKNOWN at about 40 to 63 seconds each (two of them at 107 and 475 s; notes/a33.md), again with
at least three times that budget, as the decision rule in cube_groups/m42-predictions.md asks.

Each instance is m42.py's, unchanged: its CNF depends only on the representative A_u (sigma(u) = e_0
and phi in the normal form of shape ("B", 5)), so the representatives that job m42c recorded are
written below and solved directly. The part check recomputes m42.py's classification of (B5) (same
code and seeds), confirms the 420 classes and the per-pair counts that m42c found, and confirms that
each name below has the same representative there, with kernel X_1 and image R of its pair.

Batch a is the 20 open classes whose kernel X_1 lies in H0 = span(e_0) + P (pair orbits 0 to 19,
Lemma 83 (alpha)); batch b the 22 whose kernel does not (pair orbits 20 to 48, (beta)).

Usage: python m46.py --part check|solve|grade [--batch a|b] [--group-minutes 156]
                     [--cap-minutes 10] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m42

P = 5
# The two orbits of X_1 = ker A_u (Lemma 83, Step 4): (alpha) X_1 = span(e_0, e_1, e_2, e_3) inside
# H0, pair orbits 0 to 19; (beta) X_1 = span(e_0, e_1, e_2, e_6), pair orbits 20 to 48.
X1_OF_ORBIT = {0: (8, 4, 2, 1), 1: (64, 4, 2, 1)}
FIRST_BETA_PAIR = 20
# The 49 pair orbits of Lemma 83 as m42c numbered them: the image R of each (reduced echelon basis).
PAIR_R = {
    0: (4, 2, 1), 1: (8, 4, 2), 2: (8, 4, 3), 3: (16, 2, 1), 4: (16, 4, 2), 5: (16, 4, 3),
    6: (17, 4, 2), 7: (32, 16, 1), 8: (32, 16, 2), 9: (32, 16, 3), 10: (32, 17, 2),
    11: (64, 2, 1), 12: (64, 4, 2), 13: (64, 4, 3), 14: (64, 16, 1), 15: (64, 16, 2),
    16: (64, 16, 3), 17: (64, 17, 2), 18: (64, 32, 16), 19: (64, 32, 17),
    20: (4, 2, 1), 21: (8, 2, 1), 22: (8, 4, 2), 23: (8, 4, 3), 24: (9, 4, 2), 25: (16, 8, 1),
    26: (16, 8, 2), 27: (16, 8, 3), 28: (16, 9, 2), 29: (32, 16, 8), 30: (32, 16, 9),
    31: (64, 2, 1), 32: (64, 4, 2), 33: (64, 4, 3), 34: (64, 8, 1), 35: (64, 8, 2),
    36: (64, 8, 3), 37: (64, 9, 2), 38: (64, 16, 8), 39: (64, 16, 9), 40: (72, 2, 1),
    41: (72, 4, 2), 42: (72, 4, 3), 43: (72, 16, 1), 44: (72, 16, 2), 45: (72, 16, 3),
    46: (72, 17, 2), 47: (72, 32, 16), 48: (72, 32, 17)}
# Classes of A_u per pair orbit in job m42c (out/classes_t7_B5.json), 420 in all.
M42C_PER_PAIR = (3, 1, 2, 13, 3, 9, 3, 10, 5, 10, 9, 10, 3, 6, 26, 14, 26, 14, 12, 27,
                 1, 5, 2, 4, 2, 10, 5, 10, 9, 6, 12, 1, 1, 1, 5, 4, 5, 4, 10, 23, 4, 2, 3, 14, 9,
                 14, 9, 12, 27)
# The 42 classes m42c left UNKNOWN, with their representatives A_u (t^2-bit masks).
OPEN = {
    "r3b_t7_B5_o000_c000": 266304,
    "r3b_t7_B5_o002_c000": 34086976,
    "r3b_t7_B5_o002_c001": 34089040,
    "r3b_t7_B5_o004_c000": 4295499776,
    "r3b_t7_B5_o004_c001": 8590204928,
    "r3b_t7_B5_o005_c002": 4295503968,
    "r3b_t7_B5_o005_c003": 4295506032,
    "r3b_t7_B5_o005_c005": 8590207056,
    "r3b_t7_B5_o005_c006": 8590209120,
    "r3b_t7_B5_o006_c000": 4295499792,
    "r3b_t7_B5_o006_c001": 8590204960,
    "r3b_t7_B5_o008_c001": 562640723968,
    "r3b_t7_B5_o009_c004": 562640726096,
    "r3b_t7_B5_o010_c003": 571230654544,
    "r3b_t7_B5_o012_c000": 70368744710144,
    "r3b_t7_B5_o013_c002": 70368745230368,
    "r3b_t7_B5_o016_c001": 70377334124640,
    "r3b_t7_B5_o017_c006": 140741783330832,
    "r3b_t7_B5_o019_c006": 72048076390512,
    "r3b_t7_B5_o019_c007": 141304424038464,
    "r3b_t7_B5_o020_c000": 133152,
    "r3b_t7_B5_o022_c000": 17043456,
    "r3b_t7_B5_o023_c001": 17044520,
    "r3b_t7_B5_o023_c002": 33689632,
    "r3b_t7_B5_o023_c003": 33690664,
    "r3b_t7_B5_o024_c000": 17043464,
    "r3b_t7_B5_o026_c002": 2214594560,
    "r3b_t7_B5_o027_c001": 2181043240,
    "r3b_t7_B5_o030_c000": 279239983136,
    "r3b_t7_B5_o030_c011": 1105970855944,
    "r3b_t7_B5_o032_c000": 35184372355072,
    "r3b_t7_B5_o035_c002": 70368760958976,
    "r3b_t7_B5_o035_c003": 70368811287552,
    "r3b_t7_B5_o036_c000": 35184405647392,
    "r3b_t7_B5_o036_c004": 70368811287560,
    "r3b_t7_B5_o037_c003": 70368811287584,
    "r3b_t7_B5_o039_c003": 35188784496696,
    "r3b_t7_B5_o039_c022": 140743947583496,
    "r3b_t7_B5_o042_c000": 35184389132320,
    "r3b_t7_B5_o042_c001": 70368777867296,
    "r3b_t7_B5_o042_c002": 70368777868328,
    "r3b_t7_B5_o047_c003": 36288195461120,
}
BATCHES = {"a": sorted(n for n in OPEN if int(n[11:14]) < FIRST_BETA_PAIR),
           "b": sorted(n for n in OPEN if int(n[11:14]) >= FIRST_BETA_PAIR)}


def pair_cls(name):
    """(pair, class) of a name r3b_t7_B5_oPPP_cCCC."""
    return int(name[11:14]), int(name[16:19])


def x_orbit(pair):
    return 0 if pair < FIRST_BETA_PAIR else 1


def x1_of(pair):
    return X1_OF_ORBIT[x_orbit(pair)]


def spec_of(name):
    pi, ci = pair_cls(name)
    return {"name": name, "kind": "main", "t": m42.T, "d": m42.D, "p": P, "pair": pi, "cls": ci,
            "x1": list(x1_of(pi)), "r": list(PAIR_R[pi]), "au": OPEN[name]}


def check():
    """m42.py's classification of (B5) again, compared with what m42c recorded."""
    start = time.time()
    sps, summary = m42.instances(m42.T, m42.D, P, m42.RHO)
    by_name = {s["name"]: s for s in sps}
    pairs = summary["pairs"]
    st = {"classes": len(sps), "per_pair": [len(pr["classes"]) for pr in pairs],
          "seconds": None}
    probe = spec_of(BATCHES["a"][0])
    cnf, names, hints = m42.build(probe)
    st["graded"] = {
        "per_pair": tuple(st["per_pair"]) == M42C_PER_PAIR and len(sps) == sum(M42C_PER_PAIR),
        "pairs": len(pairs) == len(PAIR_R) and all(
            tuple(pairs[pi]["x1"]) == x1_of(pi) and tuple(pairs[pi]["r"]) == r
            and pairs[pi]["x_orbit"] == x_orbit(pi) for pi, r in PAIR_R.items()),
        "reps": all(n in by_name and by_name[n]["au"] == au for n, au in OPEN.items()),
        "members": all(m42.kernel(au, m42.T) == x1_of(pair_cls(n)[0])
                       and m42.column_space(au, m42.T) == PAIR_R[pair_cls(n)[0]]
                       for n, au in OPEN.items()),
        "hints": hints == m42.HAND_HINTS["B5"] and m42.units_consistent(cnf),
        "batches": sorted(BATCHES["a"] + BATCHES["b"]) == sorted(OPEN)
                   and len(BATCHES["a"]) == 20 and len(BATCHES["b"]) == 22}
    st["seconds"] = round(time.time() - start, 1)
    return st


def run_solve(batch, solver, group_seconds, cap_seconds, out_dir):
    start = time.time()
    sps = [spec_of(n) for n in BATCHES[batch]]
    out = m42.run_group(sps, solver, group_seconds, cap_seconds, out_dir, start)
    print(f"SUMMARY solve batch {batch} instances {len(sps)} {json.dumps(out, sort_keys=True)}",
          flush=True)


def grade(out_dir):
    """Graded: the check, and every SAT verified with rank A_u = 3 and every rank <= 4. Reported:
    the status and time of each open class."""
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    counts, undecided, times = {}, [], {}
    for name in sorted(OPEN):
        path = os.path.join(out_dir, name + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        st = r.get("status")
        counts[st] = counts.get(st, 0) + 1
        times[name] = r.get("wall_seconds")
        if st != "UNSAT":
            undecided.append(name)
        if st == "SAT":
            graded[name + "_verified"] = bool(r.get("verified"))
            graded[name + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "undecided": undecided,
            "times": times, "any_sat_7": counts.get("SAT", 0) > 0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--batch", choices=sorted(BATCHES), default="a")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--group-minutes", type=float, default=156.0)
    ap.add_argument("--cap-minutes", type=float, default=10.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.batch, args.solver, args.group_minutes * 60, args.cap_minutes * 60,
                  args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} {json.dumps(out['counts'], sort_keys=True)}",
              flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check()
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
