# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m79: the second-matrix splits of three classes of (B6) with d = 1 whose rank-0 sweep was
open (Proposition 33, notes/a52.md), at t = 7 and dim V = 9 (cube_groups/m79-predictions.md;
notes/a66.md).

What came back on 2026-10-21: m76a-v2, m77a and m77b held every graded check and found o009_c002,
o009_c009, o009_c001 and o009_c004 empty (Corollaries 92 to 95), so every class of (B6) whose sweep
was UNSAT is closed. The 20 left all had an open sweep (job m64a: UNKNOWN at 150 s), so by Lemma 93
(b) their split instances of rank 0 on X_1 are needed too, each with its 21 negative unit clauses,
as m71a ran them for o008_c002 and o010_c002.

Group a (job m79a): o008_c000 (|G| = 384; 2023 orbits: 135 of rank 0, 944 of rank 1, 944 of rank
  2) and o008_c001 (|G| = 576; 1287: 87, 600, 600): 3310 instances, 222 of them with Lemma 93 (b).
Group b (job m79b): o008_c003 (|G| = 384; 1975: 135, 920, 920): 1975 instances, 135 with it.
Instances not reached are SKIPPED and stay open.

Everything else is m69.py's, imported unchanged: the instances (m57.py's encoding and hints, the
unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of m66.py, the plan
of the tails, the shared budget (10 to 20 s per split instance), the check, the child process and
the grading. This file sets m69's lists and adds one graded check: no class split here was split
before.

Parts:
    check   m69.py's check of the group's classes, and the check above. Writes m79_reps.json.
    solve   m69.py's solve.
    grade   m69.py's grade, without its (B5) entries.

Usage: python m79.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os

import m69 as b

TAILS = {"a": ("r3b_t7_B6_o008_c000", "r3b_t7_B6_o008_c001"),
         "b": ("r3b_t7_B6_o008_c003",)}
# Job m64a's sweep instance of each class (out/grade.json "status", 2026-10-21): UNKNOWN at 150 s.
SWEEP = {"r3b_t7_B6_o008_c000": "open", "r3b_t7_B6_o008_c001": "open",
         "r3b_t7_B6_o008_c003": "open"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o008_c000": {"d": 1, "order": 384, "valid": 176126, "orbits": 2023,
                            "by_rank": {"0": 135, "1": 944, "2": 944}},
    "r3b_t7_B6_o008_c001": {"d": 1, "order": 576, "valid": 176126, "orbits": 1287,
                            "by_rank": {"0": 87, "1": 600, "2": 600}},
    "r3b_t7_B6_o008_c003": {"d": 1, "order": 384, "valid": 176126, "orbits": 1975,
                            "by_rank": {"0": 135, "1": 920, "2": 920}},
}
# Classes of (B6) closed by the second-matrix split (jobs m69a to m77b): none may be split here.
CLOSED_SPLIT = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011",
                "r3b_t7_B6_o009_c008", "r3b_t7_B6_o011_c002", "r3b_t7_B6_o004_c001",
                "r3b_t7_B6_o006_c001", "r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000",
                "r3b_t7_B6_o008_c004", "r3b_t7_B6_o003_c004", "r3b_t7_B6_o012_c009",
                "r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003", "r3b_t7_B6_o012_c004",
                "r3b_t7_B6_o008_c002", "r3b_t7_B6_o009_c003", "r3b_t7_B6_o007_c001",
                "r3b_t7_B6_o010_c002", "r3b_t7_B6_o007_c004", "r3b_t7_B6_o007_c007",
                "r3b_t7_B6_o009_c000", "r3b_t7_B6_o009_c002", "r3b_t7_B6_o009_c009",
                "r3b_t7_B6_o012_c001", "r3b_t7_B6_o009_c001", "r3b_t7_B6_o009_c004")
REPS_FILE = "m79_reps.json"


def install():
    """m69's lists become this job's; m57.build keeps Lemma 93 (b) for the rank-0 instances."""
    b.install()
    b.NAMED = {"a": (), "b": ()}
    b.TAILS, b.SWEEP, b.GATE, b.REPS_FILE = TAILS, SWEEP, GATE, REPS_FILE


install()


def check(group, out_dir):
    install()
    st = b.check(group, out_dir)
    st["graded"]["not_split_before"] = not set(TAILS[group]) & set(CLOSED_SPLIT)
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m79-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    for key in ("o020", "b5_closed", "named", "named_unsat"):
        out.pop(key, None)
    return out


def summary_line(out):
    cls = {n[10:]: {k: v for k, v in c.items() if k != "open"} for n, c in out.get("classes", {}).items()}
    opened = {n[10:]: c["open"][:30] for n, c in out.get("classes", {}).items()}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} b6_closed {out.get('b6_closed')} "
            f"classes {json.dumps(cls, sort_keys=True)} open {json.dumps(opened, sort_keys=True)}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    install()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        b.run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(summary_line(out), flush=True)
    else:
        st = check(args.group, args.out_dir)
        print(f"check: {json.dumps({k: v for k, v in st.items() if k != 'm57'}, sort_keys=True)}",
              flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
