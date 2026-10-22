# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m91: the second-matrix splits of o003_c000 and o005_c000, the last two classes of (B6) still
open (both d = 2, rank-0 sweep open; Proposition 33, notes/a52.md), at t = 7 and dim V = 9, one
class per group (cube_groups/m91-predictions.md; notes/a78.md).

What came back on 2026-10-22: job m87a-b6rerun-v3 ran its check (all graded true) and then its
solve part, which the host interrupted after 68 minutes ("interrupted", no grade step). By then all
20 re-runs of o010_c001 were UNSAT in CaDiCaL (19.49 to 84.49 s), so that class is empty, and the
split of o003_c000 had reached its 24th rank-0 instance: all 1344 of rank 1 and 2 UNSAT, 13 of the
24 rank-0 ones UNSAT and 11 UNKNOWN at 10 s. o005_c000 was not reached. A full re-run of m87a would
not fit both splits into one group's 150 minutes, so this job splits each class alone, as m88.py
split o005_c003.

Group a (job m91a): o003_c000 (d = 2, |G| = 1536, 1599: 255 of rank 0 with Lemma 93 (b), 896 of
  rank 1, 448 of rank 2).
Group b (job m91b): o005_c000 (d = 2, |G| = 512, 1913: 135, 920, 858).

This file is m88.py with new lists. Everything is m69.py's, imported unchanged: the instances
(m57.py's encoding and hints, the unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones),
the orbit roots of m66.py, the plan of the tail, the shared budget (10 to 20 s per split instance),
the child process, the check and the grading. This file sets m69's lists and checks that the class
is not among those already closed.

Parts:
    check   m69.py's check of the group's class, and that it is not among those closed before.
    solve   m69.py's solve.
    grade   m69.py's grade.

Usage: python m91.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os

import m69 as b

TAILS = {"a": ("r3b_t7_B6_o003_c000",), "b": ("r3b_t7_B6_o005_c000",)}
# Job m64a's sweep instance of each class (logs/run-03-python.stdout.txt): UNKNOWN at 150 s.
SWEEP = {"r3b_t7_B6_o003_c000": "open", "r3b_t7_B6_o005_c000": "open"}
# m66's run (m66-prop33count-v1 out/count.json), as in m87.py, whose check confirmed both.
GATE = {
    "r3b_t7_B6_o003_c000": {"d": 2, "order": 1536, "valid": 176126, "orbits": 1599,
                            "by_rank": {"0": 255, "1": 896, "2": 448}},
    "r3b_t7_B6_o005_c000": {"d": 2, "order": 512, "valid": 176126, "orbits": 1913,
                            "by_rank": {"0": 135, "1": 920, "2": 858}},
}
# Classes of (B6) closed by the second-matrix split and its re-runs (jobs m69a to m90b and
# m87a-v3): m90.py's 43, o005_c003 (m88a-v2, m90a, m90b) and o010_c001 (m86a, m87a-v3).
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
                "r3b_t7_B6_o009_c007", "r3b_t7_B6_o010_c000", "r3b_t7_B6_o010_c007",
                "r3b_t7_B6_o010_c008", "r3b_t7_B6_o005_c002", "r3b_t7_B6_o003_c001",
                "r3b_t7_B6_o005_c001", "r3b_t7_B6_o005_c003", "r3b_t7_B6_o010_c001")
REPS_FILE = "m91_reps.json"

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
    st["graded"]["not_closed_before"] = not set(TAILS[group]) & set(CLOSED_SPLIT)
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m91-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
    return out


def summary_line(out):
    cls = {n[10:]: {k: v for k, v in c.items() if k != "open"} for n, c in out.get("classes", {}).items()}
    opened = {n[10:]: c["open"][:60] for n, c in out.get("classes", {}).items()}
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
