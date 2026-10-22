# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m88: the second-matrix split of o005_c003, the last class of (B6) not yet split (d = 2,
rank-0 sweep open; Proposition 33, notes/a52.md), at t = 7 and dim V = 9, alone in one group
(cube_groups/m88-predictions.md; notes/a72.md).

o005_c003 (d = 2, |G| = 512, 1961: 135 of rank 0 with Lemma 93 (b), 944 of rank 1, 882 of rank 2)
does not depend on job m87, which re-runs the 45 open instances of m85b and m86 and splits the
other four classes with d = 2, so it runs beside m87 with no re-runs in front.

Everything is m69.py's, imported unchanged: the instances (m57.py's encoding and hints, the unit
clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of m66.py, the plan of
the tail, the shared budget (10 to 20 s per split instance), the child process, the check and the
grading. This file sets m69's lists, as m87.py does without the re-runs, and checks that the class
was not split before.

Parts:
    check   m69.py's check of the class, and that it is not among those split before.
    solve   m69.py's solve.
    grade   m69.py's grade.

Usage: python m88.py --part check|solve|grade [--group a] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os

import m69 as b

TAILS = {"a": ("r3b_t7_B6_o005_c003",), "b": ()}
# Job m64a's sweep instance of the class (logs/run-03-python.stdout.txt): UNKNOWN at 150 s.
SWEEP = {"r3b_t7_B6_o005_c003": "open"}
# m66's run (m66-prop33count-v1 out/count.json).
GATE = {
    "r3b_t7_B6_o005_c003": {"d": 2, "order": 512, "valid": 176126, "orbits": 1961,
                            "by_rank": {"0": 135, "1": 944, "2": 882}},
}
# Classes of (B6) closed by the second-matrix split and its re-runs (jobs m69a to m86b), as in
# m87.py, and the seven re-run or split by m87.
CLOSED_SPLIT = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011",
                "r3b_t7_B6_o009_c008", "r3b_t7_B6_o011_c002", "r3b_t7_B6_o004_c001",
                "r3b_t7_B6_o006_c001", "r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000",
                "r3b_t7_B6_o008_c004", "r3b_t7_B6_o003_c004", "r3b_t7_B6_o012_c009",
                "r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003", "r3b_t7_B6_o012_c004",
                "r3b_t7_B6_o008_c002", "r3b_t7_B6_o009_c003", "r3b_t7_B6_o007_c001",
                "r3b_t7_B6_o010_c002", "r3b_t7_B6_o007_c004", "r3b_t7_B6_o007_c007",
                "r3b_t7_B6_o009_c000", "r3b_t7_B6_o009_c002", "r3b_t7_B6_o009_c009",
                "r3b_t7_B6_o012_c001", "r3b_t7_B6_o009_c001", "r3b_t7_B6_o009_c004",
                "r3b_t7_B6_o008_c000", "r3b_t7_B6_o008_c001", "r3b_t7_B6_o008_c003",
                "r3b_t7_B6_o009_c005", "r3b_t7_B6_o009_c006", "r3b_t7_B6_o010_c003",
                "r3b_t7_B6_o010_c005", "r3b_t7_B6_o010_c004", "r3b_t7_B6_o010_c006",
                "r3b_t7_B6_o009_c007", "r3b_t7_B6_o010_c000", "r3b_t7_B6_o010_c007")
SPLIT_ELSEWHERE = ("r3b_t7_B6_o010_c001", "r3b_t7_B6_o010_c008", "r3b_t7_B6_o005_c002",
                   "r3b_t7_B6_o003_c000", "r3b_t7_B6_o005_c000", "r3b_t7_B6_o003_c001",
                   "r3b_t7_B6_o005_c001")
REPS_FILE = "m88_reps.json"

_plan69 = b.plan


def install():
    """m69's lists become this job's; m57.build keeps Lemma 93 (b)."""
    b.install()
    b.NAMED = {"a": (), "b": ()}
    b.TAILS, b.SWEEP, b.GATE, b.REPS_FILE = TAILS, SWEEP, GATE, REPS_FILE
    b.plan = _plan69


install()


def check(group, out_dir):
    install()
    st = b.check(group, out_dir)
    st["graded"]["not_split_before"] = not set(TAILS[group]) & (set(CLOSED_SPLIT)
                                                                | set(SPLIT_ELSEWHERE))
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m88-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
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
    ap.add_argument("--group", choices=["a"], default="a")
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
