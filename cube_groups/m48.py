# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m48: the 51 classes of the rank-3 configuration (B5) for t = 7 and dim V = 9 that job m42d
(the second half of (B5)) left UNKNOWN at about 40 to 70 seconds each (four of them at 107, 142, 165
and 480 s; notes/a35.md), again with at least three times that budget where the cap allows, as the
decision rule in cube_groups/m42-predictions.md asks. It is job m46's code for the other half.

Each instance is m42.py's, unchanged: the representatives that job m42d recorded are written below
and solved directly. The part check recomputes m42.py's classification of (B5) (same code and
seeds), confirms the 420 classes and the per-pair counts (as in m46.py), confirms that each name
below has the same representative there, with kernel X_1 and image R of its pair, and that every
name lies in m42d's half (index 1 of 2 in m42.py's round-robin order).

The 51 names, sorted, are dealt round-robin into batches a, b, c of 17, so each batch mixes pair
orbits and the four slow classes are spread out.

Usage: python m48.py --part check|solve|grade [--batch a|b|c] [--group-minutes 156]
                     [--cap-minutes 10] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m42
import m46

P = m46.P
# The 51 classes m42d left UNKNOWN, with their representatives A_u (t^2-bit masks), from
# m42d's out/r3b_t7_B5_*.json.
OPEN = {
    "r3b_t7_B5_o000_c001": 266320,
    "r3b_t7_B5_o000_c002": 270368,
    "r3b_t7_B5_o001_c000": 34086912,
    "r3b_t7_B5_o003_c003": 4294971504,
    "r3b_t7_B5_o003_c005": 4294975536,
    "r3b_t7_B5_o004_c002": 17180135424,
    "r3b_t7_B5_o005_c000": 4295499840,
    "r3b_t7_B5_o005_c001": 4295501904,
    "r3b_t7_B5_o005_c004": 8590204992,
    "r3b_t7_B5_o006_c002": 17180135488,
    "r3b_t7_B5_o007_c005": 566935683104,
    "r3b_t7_B5_o007_c006": 571230650400,
    "r3b_t7_B5_o007_c008": 1103806595136,
    "r3b_t7_B5_o008_c004": 1103806603264,
    "r3b_t7_B5_o009_c009": 1103806605392,
    "r3b_t7_B5_o010_c002": 566935687232,
    "r3b_t7_B5_o010_c007": 1653562417168,
    "r3b_t7_B5_o012_c002": 351843721154560,
    "r3b_t7_B5_o013_c000": 70368744710208,
    "r3b_t7_B5_o013_c001": 70368744714336,
    "r3b_t7_B5_o013_c004": 351843721154592,
    "r3b_t7_B5_o013_c005": 351843721414672,
    "r3b_t7_B5_o015_c001": 70381629087744,
    "r3b_t7_B5_o015_c004": 70394513985536,
    "r3b_t7_B5_o015_c005": 70398808952832,
    "r3b_t7_B5_o015_c011": 422216760037376,
    "r3b_t7_B5_o016_c024": 422233939904528,
    "r3b_t7_B5_o017_c000": 70377334120480,
    "r3b_t7_B5_o017_c001": 70381629087792,
    "r3b_t7_B5_o019_c016": 142949396512816,
    "r3b_t7_B5_o022_c001": 33689600,
    "r3b_t7_B5_o023_c000": 17043488,
    "r3b_t7_B5_o024_c001": 33689616,
    "r3b_t7_B5_o027_c005": 2214594576,
    "r3b_t7_B5_o028_c006": 4395631664,
    "r3b_t7_B5_o028_c008": 6559892536,
    "r3b_t7_B5_o031_c000": 35184372090912,
    "r3b_t7_B5_o033_c000": 35184372355104,
    "r3b_t7_B5_o035_c000": 35184405647360,
    "r3b_t7_B5_o035_c001": 35184422424576,
    "r3b_t7_B5_o036_c003": 70368760960040,
    "r3b_t7_B5_o037_c000": 35184405647376,
    "r3b_t7_B5_o037_c001": 35184422424600,
    "r3b_t7_B5_o041_c000": 35184389132288,
    "r3b_t7_B5_o041_c001": 70368777867264,
    "r3b_t7_B5_o043_c006": 70370925215784,
    "r3b_t7_B5_o045_c004": 35192978802704,
    "r3b_t7_B5_o047_c002": 35747029581824,
    "r3b_t7_B5_o047_c008": 70658688024576,
    "r3b_t7_B5_o047_c010": 71474731810816,
    "r3b_t7_B5_o048_c003": 36288195461136,
}
_SORTED = sorted(OPEN)
BATCHES = {"a": _SORTED[0::3], "b": _SORTED[1::3], "c": _SORTED[2::3]}
# m42d's half of (B5): index 1 of 2 in m42.instances' round-robin order.
HALF, HALVES = 1, 2


def spec_of(name):
    pi, ci = m46.pair_cls(name)
    return {"name": name, "kind": "main", "t": m42.T, "d": m42.D, "p": P, "pair": pi, "cls": ci,
            "x1": list(m46.x1_of(pi)), "r": list(m46.PAIR_R[pi]), "au": OPEN[name]}


def check():
    """m42.py's classification of (B5) again, compared with what m42c and m42d recorded."""
    start = time.time()
    sps, summary = m42.instances(m42.T, m42.D, P, m42.RHO)
    by_name = {s["name"]: s for s in sps}
    half = {s["name"] for s in sps[HALF::HALVES]}
    pairs = summary["pairs"]
    st = {"classes": len(sps), "per_pair": [len(pr["classes"]) for pr in pairs],
          "half": len(half), "seconds": None}
    probe = spec_of(BATCHES["a"][0])
    cnf, names, hints = m42.build(probe)
    st["graded"] = {
        "per_pair": tuple(st["per_pair"]) == m46.M42C_PER_PAIR
                    and len(sps) == sum(m46.M42C_PER_PAIR),
        "pairs": len(pairs) == len(m46.PAIR_R) and all(
            tuple(pairs[pi]["x1"]) == m46.x1_of(pi) and tuple(pairs[pi]["r"]) == r
            and pairs[pi]["x_orbit"] == m46.x_orbit(pi) for pi, r in m46.PAIR_R.items()),
        "reps": all(n in by_name and by_name[n]["au"] == au for n, au in OPEN.items()),
        "members": all(m42.kernel(au, m42.T) == m46.x1_of(m46.pair_cls(n)[0])
                       and m42.column_space(au, m42.T) == m46.PAIR_R[m46.pair_cls(n)[0]]
                       for n, au in OPEN.items()),
        "in_m42d_half": len(half) == 210 and all(n in half for n in OPEN),
        "disjoint_from_m46": not set(OPEN) & set(m46.OPEN),
        "hints": hints == m42.HAND_HINTS["B5"] and m42.units_consistent(cnf),
        "batches": sorted(sum(BATCHES.values(), [])) == _SORTED
                   and all(len(b) == 17 for b in BATCHES.values())}
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
    for name in _SORTED:
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
