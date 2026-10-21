# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m45: the 30 classes of the rank-3 configuration (B6) for t = 7 and dim V = 9 that job m42a
left UNKNOWN at about 194 to 202 seconds each (notes/a32.md), again with at least three times that
budget, as the decision rule in cube_groups/m42-predictions.md asks.

Each instance is m42.py's, unchanged: its CNF depends only on the representative A_u (sigma(u) = e_0
and phi in the normal form of shape ("B", 6)), so the representatives that job m42a recorded are
written below and solved directly. The part check recomputes m42.py's classification of (B6) (same
code and seeds), confirms the 68 classes and the per-pair counts that m42a found, and confirms that
each name below has the same representative there, with kernel X_1 and image R of its pair.

Usage: python m45.py --part check|solve|grade [--batch a|b] [--group-minutes 156]
                     [--cap-minutes 11] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m42

P = 6
X1 = (8, 4, 2, 1)
# The 13 pair orbits of Lemma 83 (notes/a27.md) as m42a numbered them: the image R of each.
PAIR_R = {0: (4, 2, 1), 1: (8, 4, 2), 2: (8, 4, 3), 3: (16, 2, 1), 4: (16, 4, 2), 5: (16, 4, 3),
          6: (17, 4, 2), 7: (32, 16, 1), 8: (32, 16, 2), 9: (32, 16, 3), 10: (32, 17, 2),
          11: (64, 32, 16), 12: (64, 32, 17)}
# Classes of A_u per pair orbit in job m42a (out/classes_t7_B6.json), 68 in all.
M42A_PER_PAIR = (1, 1, 1, 5, 2, 4, 2, 10, 5, 10, 9, 6, 12)
# The 30 classes m42a left UNKNOWN, with their representatives A_u (t^2-bit masks).
OPEN = {
    "r3b_t7_B6_o000_c000": 266304,
    "r3b_t7_B6_o002_c000": 34086976,
    "r3b_t7_B6_o004_c000": 4295499776,
    "r3b_t7_B6_o004_c001": 8590204928,
    "r3b_t7_B6_o005_c002": 8590204992,
    "r3b_t7_B6_o005_c003": 8590207056,
    "r3b_t7_B6_o006_c000": 4295499792,
    "r3b_t7_B6_o006_c001": 8590204960,
    "r3b_t7_B6_o007_c004": 562640715856,
    "r3b_t7_B6_o007_c005": 566935683104,
    "r3b_t7_B6_o008_c000": 558345756672,
    "r3b_t7_B6_o008_c001": 562640723968,
    "r3b_t7_B6_o008_c002": 566935687168,
    "r3b_t7_B6_o008_c003": 571230654464,
    "r3b_t7_B6_o009_c004": 562640726096,
    "r3b_t7_B6_o009_c006": 571230654496,
    "r3b_t7_B6_o009_c007": 571230656560,
    "r3b_t7_B6_o009_c008": 1103806603328,
    "r3b_t7_B6_o009_c009": 1103806605392,
    "r3b_t7_B6_o010_c000": 558345756704,
    "r3b_t7_B6_o010_c001": 562640724016,
    "r3b_t7_B6_o010_c002": 566935687232,
    "r3b_t7_B6_o010_c003": 571230654544,
    "r3b_t7_B6_o010_c005": 1116691499072,
    "r3b_t7_B6_o011_c004": 72048076390400,
    "r3b_t7_B6_o012_c001": 71489730642000,
    "r3b_t7_B6_o012_c003": 71498320576624,
    "r3b_t7_B6_o012_c005": 72043781423200,
    "r3b_t7_B6_o012_c006": 72048076390512,
    "r3b_t7_B6_o012_c008": 143490562392080,
}
# Batch a: pair orbits 9, 10 and 12 (where every UNSAT of m42a was, or next to it); b: the rest.
BATCHES = {"a": sorted(n for n in OPEN if int(n[11:14]) in (9, 10, 12)),
           "b": sorted(n for n in OPEN if int(n[11:14]) not in (9, 10, 12))}


def pair_cls(name):
    """(pair, class) of a name r3b_t7_B6_oPPP_cCCC."""
    return int(name[11:14]), int(name[16:19])


def spec_of(name):
    pi, ci = pair_cls(name)
    return {"name": name, "kind": "main", "t": m42.T, "d": m42.D, "p": P, "pair": pi, "cls": ci,
            "x1": list(X1), "r": list(PAIR_R[pi]), "au": OPEN[name]}


def check():
    """m42.py's classification of (B6) again, compared with what m42a recorded."""
    start = time.time()
    sps, summary = m42.instances(m42.T, m42.D, P, m42.RHO)
    by_name = {s["name"]: s for s in sps}
    pairs = summary["pairs"]
    st = {"classes": len(sps), "per_pair": [len(pr["classes"]) for pr in pairs],
          "seconds": None}
    probe = spec_of(BATCHES["a"][0])
    cnf, names, hints = m42.build(probe)
    st["graded"] = {
        "per_pair": tuple(st["per_pair"]) == M42A_PER_PAIR and len(sps) == sum(M42A_PER_PAIR),
        "pairs": len(pairs) == len(PAIR_R) and all(
            tuple(pairs[pi]["x1"]) == X1 and tuple(pairs[pi]["r"]) == r for pi, r in PAIR_R.items()),
        "reps": all(n in by_name and by_name[n]["au"] == au for n, au in OPEN.items()),
        "members": all(m42.kernel(au, m42.T) == X1
                       and m42.column_space(au, m42.T) == PAIR_R[pair_cls(n)[0]]
                       for n, au in OPEN.items()),
        "hints": hints == m42.HAND_HINTS["B6"] and m42.units_consistent(cnf),
        "batches": sorted(BATCHES["a"] + BATCHES["b"]) == sorted(OPEN)
                   and len(BATCHES["a"]) == len(BATCHES["b"]) == 15}
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
    ap.add_argument("--cap-minutes", type=float, default=11.0)
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
