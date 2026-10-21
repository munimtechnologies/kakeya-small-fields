# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m47: the 29 classes of the rank-3 configuration (B6) for t = 7 and dim V = 9 that job m42b
left UNKNOWN at about 247 to 277 seconds each (notes/a34.md), again with at least three times that
budget, as the decision rule in cube_groups/m42-predictions.md asks. It is job m45's code (the same
rule applied to job m42a's 30 open classes) for m42b's half of (B6).

Each instance is m42.py's, unchanged: its CNF depends only on the representative A_u (sigma(u) = e_0
and phi in the normal form of shape ("B", 6)), so the representatives that job m42b recorded are
written below and solved directly. The part check recomputes m42.py's classification of (B6) (same
code and seeds), confirms the 68 classes and the per-pair counts that m42a and m42b found, confirms
that each name below has the same representative there, with kernel X_1 and image R of its pair, and
confirms that these 29 names and m42b's 5 UNSAT names are exactly m42b's 34 classes.

Usage: python m47.py --part check|solve|grade [--batch a|b|c] [--group-minutes 156]
                     [--cap-minutes 15] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m42

P = 6
X1 = (8, 4, 2, 1)
# The 13 pair orbits of Lemma 83 (notes/a27.md) as m42a and m42b numbered them: the image R of each.
PAIR_R = {0: (4, 2, 1), 1: (8, 4, 2), 2: (8, 4, 3), 3: (16, 2, 1), 4: (16, 4, 2), 5: (16, 4, 3),
          6: (17, 4, 2), 7: (32, 16, 1), 8: (32, 16, 2), 9: (32, 16, 3), 10: (32, 17, 2),
          11: (64, 32, 16), 12: (64, 32, 17)}
# Classes of A_u per pair orbit (out/classes_t7_B6.json of m42a and m42b), 68 in all.
M42_PER_PAIR = (1, 1, 1, 5, 2, 4, 2, 10, 5, 10, 9, 6, 12)
# How the two halves split them: m42a took every second class, m42b the others.
M42A_TRIED_PER_PAIR = (1, 0, 1, 0, 2, 2, 2, 2, 4, 5, 5, 1, 9)
M42B_TRIED_PER_PAIR = (0, 1, 0, 5, 0, 2, 0, 8, 1, 5, 4, 5, 3)
# The 5 classes m42b found UNSAT (161 to 243 s), with their representatives.
M42B_UNSAT = {
    "r3b_t7_B6_o007_c000": 558345748544,
    "r3b_t7_B6_o007_c008": 1103806595136,
    "r3b_t7_B6_o011_c000": 71485435674624,
    "r3b_t7_B6_o011_c001": 71489730641920,
    "r3b_t7_B6_o011_c005": 282578783305728,
}
# The 29 classes m42b left UNKNOWN, with their representatives A_u (t^2-bit masks).
OPEN = {
    "r3b_t7_B6_o001_c000": 34086912,
    "r3b_t7_B6_o003_c000": 4294971456,
    "r3b_t7_B6_o003_c001": 4294971472,
    "r3b_t7_B6_o003_c002": 8589936704,
    "r3b_t7_B6_o003_c003": 8589936720,
    "r3b_t7_B6_o003_c004": 8589942800,
    "r3b_t7_B6_o005_c000": 4295499840,
    "r3b_t7_B6_o005_c001": 4295501904,
    "r3b_t7_B6_o007_c001": 558345748560,
    "r3b_t7_B6_o007_c002": 558345748592,
    "r3b_t7_B6_o007_c003": 562640715840,
    "r3b_t7_B6_o007_c006": 571230650400,
    "r3b_t7_B6_o007_c007": 571230650416,
    "r3b_t7_B6_o007_c009": 1103806595152,
    "r3b_t7_B6_o008_c004": 1103806603264,
    "r3b_t7_B6_o009_c000": 558345756736,
    "r3b_t7_B6_o009_c001": 558345758800,
    "r3b_t7_B6_o009_c002": 558345762928,
    "r3b_t7_B6_o009_c003": 562640724032,
    "r3b_t7_B6_o009_c005": 566935687200,
    "r3b_t7_B6_o010_c004": 1103806603280,
    "r3b_t7_B6_o010_c006": 1125281433696,
    "r3b_t7_B6_o010_c007": 1653562417168,
    "r3b_t7_B6_o010_c008": 1679332214896,
    "r3b_t7_B6_o011_c002": 71494025609216,
    "r3b_t7_B6_o011_c003": 72043781423104,
    "r3b_t7_B6_o012_c004": 72035191488576,
    "r3b_t7_B6_o012_c009": 144040318205968,
    "r3b_t7_B6_o012_c011": 283128539119632,
}
# Batch a: pair orbits 1, 3, 5, 8 (d >= 2 except pair 8); b: pair orbits 7, 11, 12 (where m42b's UNSAT
# answers were); c: pair orbits 9 and 10.
BATCH_PAIRS = {"a": (1, 3, 5, 8), "b": (7, 11, 12), "c": (9, 10)}
BATCH_SIZES = {"a": 9, "b": 11, "c": 9}


def pair_cls(name):
    """(pair, class) of a name r3b_t7_B6_oPPP_cCCC."""
    return int(name[11:14]), int(name[16:19])


BATCHES = {b: sorted(n for n in OPEN if pair_cls(n)[0] in pairs) for b, pairs in BATCH_PAIRS.items()}


def per_pair(names):
    counts = [0] * len(PAIR_R)
    for n in names:
        counts[pair_cls(n)[0]] += 1
    return tuple(counts)


def spec_of(name):
    pi, ci = pair_cls(name)
    return {"name": name, "kind": "main", "t": m42.T, "d": m42.D, "p": P, "pair": pi, "cls": ci,
            "x1": list(X1), "r": list(PAIR_R[pi]), "au": OPEN[name]}


def check():
    """m42.py's classification of (B6) again, compared with what m42a and m42b recorded."""
    start = time.time()
    sps, summary = m42.instances(m42.T, m42.D, P, m42.RHO)
    by_name = {s["name"]: s for s in sps}
    pairs = summary["pairs"]
    st = {"classes": len(sps), "per_pair": [len(pr["classes"]) for pr in pairs],
          "seconds": None}
    probe = spec_of(BATCHES["a"][0])
    cnf, names, hints = m42.build(probe)
    both = dict(OPEN)
    both.update(M42B_UNSAT)
    st["graded"] = {
        "per_pair": tuple(st["per_pair"]) == M42_PER_PAIR and len(sps) == sum(M42_PER_PAIR),
        "halves": tuple(a + b for a, b in zip(M42A_TRIED_PER_PAIR, M42B_TRIED_PER_PAIR))
                  == M42_PER_PAIR,
        "pairs": len(pairs) == len(PAIR_R) and all(
            tuple(pairs[pi]["x1"]) == X1 and tuple(pairs[pi]["r"]) == r for pi, r in PAIR_R.items()),
        "reps": all(n in by_name and by_name[n]["au"] == au for n, au in both.items()),
        "members": all(m42.kernel(au, m42.T) == X1
                       and m42.column_space(au, m42.T) == PAIR_R[pair_cls(n)[0]]
                       for n, au in both.items()),
        "m42b_half": len(both) == 34 and not (set(OPEN) & set(M42B_UNSAT))
                     and per_pair(both) == M42B_TRIED_PER_PAIR,
        "hints": hints == m42.HAND_HINTS["B6"] and m42.units_consistent(cnf),
        "batches": sorted(sum(BATCHES.values(), [])) == sorted(OPEN)
                   and all(len(BATCHES[b]) == BATCH_SIZES[b] for b in BATCHES)}
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
    ap.add_argument("--cap-minutes", type=float, default=15.0)
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
