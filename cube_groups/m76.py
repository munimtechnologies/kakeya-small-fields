# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m76: the second-matrix splits of three more classes of (B6) whose rank-0 sweep was UNSAT
(Proposition 33, notes/a52.md), at t = 7 and dim V = 9 (cube_groups/m72-predictions.md,
m76-predictions.md; notes/a62.md).

What came back on 2026-10-21: m72a's and m72b's checks held (36 and 32 graded, all true) and nothing
was SAT. All 80 re-runs of the split instances m70 left open (rank 0 on X_1, with Lemma 93 (b))
were UNSAT by CaDiCaL within 300 s (at most 244.1 s; the XOR arm was never needed), so o004_c000,
o006_c000, o008_c004, o003_c004, o003_c002 and o003_c003 are empty, and the splits of o012_c009 and
o012_c004 (d = 0) were UNSAT in every instance (median 1.27 s, slowest 4.33 s), so they are empty
too (Corollaries 76 to 83). No split instance of a class is left open, so this job has no re-runs.

Group a (job m76a): the splits of o009_c002 and o009_c009 (d = 1, sweep UNSAT: 1888 + 1888
  instances of rank 1 and 2).
Group b (job m76b): the split of o012_c001 (d = 0, sweep UNSAT: 3584 instances of rank 1 and 2).
Instances not reached are SKIPPED and stay open.

Everything else is m69.py's, imported unchanged: the instances (m57.py's encoding and hints, the
unit clauses fixing A_(v_1)), the orbit roots of m66.py, the plan of the tails, the shared budget
(10 to 20 s per split instance), the check, the child process and the grading. This file sets
m69's lists and adds one graded check: no class split here was split before or is in flight.

Parts:
    check   m69.py's check of the group's classes, and the check above. Writes m76_reps.json.
    solve   m69.py's solve.
    grade   m69.py's grade, without its (B5) entries.

Usage: python m76.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os

import m69 as b

TAILS = {"a": ("r3b_t7_B6_o009_c002", "r3b_t7_B6_o009_c009"),
         "b": ("r3b_t7_B6_o012_c001",)}
# Job m64a's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {"r3b_t7_B6_o009_c002": "UNSAT", "r3b_t7_B6_o009_c009": "UNSAT",
         "r3b_t7_B6_o012_c001": "UNSAT"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o009_c002": {"d": 1, "order": 384, "valid": 176126, "orbits": 2023,
                            "by_rank": {"0": 135, "1": 944, "2": 944}},
    "r3b_t7_B6_o009_c009": {"d": 1, "order": 384, "valid": 176126, "orbits": 2023,
                            "by_rank": {"0": 135, "1": 944, "2": 944}},
    "r3b_t7_B6_o012_c001": {"d": 0, "order": 168, "valid": 176128, "orbits": 3840,
                            "by_rank": {"0": 256, "1": 1792, "2": 1792}},
}
# Classes of (B6) closed by the second-matrix split (jobs m69a, m69b, m70a, m71a, m72a, m72b), and
# the classes in flight in job m73: none may be split here.
CLOSED_SPLIT = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011",
                "r3b_t7_B6_o009_c008", "r3b_t7_B6_o011_c002", "r3b_t7_B6_o004_c001",
                "r3b_t7_B6_o006_c001", "r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000",
                "r3b_t7_B6_o008_c004", "r3b_t7_B6_o003_c004", "r3b_t7_B6_o012_c009",
                "r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003", "r3b_t7_B6_o012_c004")
SPLIT_ELSEWHERE = ("r3b_t7_B6_o008_c002", "r3b_t7_B6_o010_c002", "r3b_t7_B6_o009_c003",
                   "r3b_t7_B6_o007_c001", "r3b_t7_B6_o007_c004", "r3b_t7_B6_o007_c007",
                   "r3b_t7_B6_o009_c000")
REPS_FILE = "m76_reps.json"


def install():
    """m69's lists become this job's; m57.build keeps Lemma 93 (b) (not used: every sweep UNSAT)."""
    b.install()
    b.NAMED = {"a": (), "b": ()}
    b.TAILS, b.SWEEP, b.GATE, b.REPS_FILE = TAILS, SWEEP, GATE, REPS_FILE


install()


def check(group, out_dir):
    install()
    st = b.check(group, out_dir)
    st["graded"]["not_split_before"] = (
        not set(TAILS[group]) & (set(CLOSED_SPLIT) | set(SPLIT_ELSEWHERE))
        and not set(CLOSED_SPLIT) & set(SPLIT_ELSEWHERE))
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m76-predictions.md) ----------

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
