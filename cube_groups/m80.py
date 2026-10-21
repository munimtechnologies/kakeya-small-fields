# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m80: the 7 instances of the last (B5) class that m78a and m78b left open, re-run for longer,
at t = 7 and dim V = 9, d = dim(X_1 n R) = 2 (Proposition 34, notes/a58.md; cube_groups/
m80-predictions.md, notes/a67.md).

What came back on 2026-10-21: m75b, m78a, m78b and m78r held every graded check. m75b found all
3654 instances of r3b_t7_B5_o006_c000 UNSAT and m78r found r3s_t7_B5_o004_c001_a1240 UNSAT, so both
classes are empty (Corollaries 96 and 97) and (B5) stands at 419 of 420. Of the 6720 instances of
r3b_t7_B5_o005_c005, 6713 were UNSAT and 7 (all of rank 1 on X_1) were UNKNOWN at their 10 s
budgets: a1774 (m78a) and a3821, a3845, a4910, a4982, a5005, a5032 (m78b).

Group r (job m80r): each of the 7 gets 5 minutes of CaDiCaL and then, only if it is still open, 5
minutes of XOR, as m78r ran a1240. o005_c005 is empty only if all 7 are UNSAT here.

Everything is m78.py with its lists rebound (as m78 rebinds m75): m75's check, unchanged, runs with
this job's plan (one entry per instance) and class lists; m78's solve and grade run unchanged; this
file adds one graded check of its own.

Parts:
    check   graded: m75's check of o005_c005 (m57's own check; m55's structure with d = 2, |G| =
            Proposition 34 (c), |Adm|, class counts by rank equal to m74's run; every root
            admissible, of its rank, distinct with its sum with A_u; the plan; hints and units of
            the first instance in both arms); and that m55's roots at the 7 orders are the
            instances m78a and m78b left open. Writes m80_reps.json.
    solve   m78.py's solve.
    grade   m78.py's grade: status and time of every instance; whether all 7 are UNSAT.

Usage: python m80.py --part check|solve|grade [--group r] [--group-minutes 75] [--out-dir DIR]
"""
import argparse
import json
import os

import m75
import m78
import m60

T = 7
O5 = m78.O5
RERUN_CAP = m78.RERUN_CAP
# (m55 order k, m55 index, rank on X_1, A_(h_1)) of each instance left UNKNOWN, copied from m78a's
# and m78b's out/r3s_t7_B5_o005_c005_a{k}__cadical.json.
REOPEN = ((1774, 12342, 1, 8590557958), (3821, 262198, 1, 134316806),
          (3845, 262534, 1, 134382858), (4910, 546834, 1, 25769908272),
          (4982, 560182, 1, 17180232534), (5005, 561206, 1, 25769902918),
          (5032, 564278, 1, 25770167126))
TAILS = {"r": O5}
PLANNED = {"r": len(REOPEN)}
REPS_FILE = "m80_reps.json"


def plan(group, reps):
    """[(spec, arm, cap seconds, condition, named)] as m78.plan's group r, for each instance."""
    rs = reps[O5]
    out = []
    for k, _, _, _ in REOPEN:
        sp = m60.split_spec(O5, k, rs[k])
        out += [(sp, "cadical", RERUN_CAP, None, True), (dict(sp), "xor", RERUN_CAP, "open", True)]
    return out


def install():
    """m78's lists become this job's; m78.install then sets m75's from them."""
    m78.TAILS, m78.PLANNED, m78.REPS_FILE = dict(TAILS), dict(PLANNED), REPS_FILE
    m78.plan = plan
    m78.install()
    m75.planned = lambda name: len(REOPEN)


install()


# ---------- check ----------

def check(group, out_dir):
    install()
    st = m75.check(group, out_dir)
    graded = st["graded"]
    rs = m75.load_reps(out_dir)[O5]
    graded["reopen"] = all(k < len(rs) and rs[k]["index"] == idx and rs[k]["rank_x1"] == rk
                           and rs[k]["a1"] == a1 for k, idx, rk, a1 in REOPEN)
    st["graded"] = graded
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m80-predictions.md) ----------

def grade(group, out_dir):
    install()
    return m78.grade(group, out_dir)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group", choices=["r"], default="r")
    ap.add_argument("--group-minutes", type=float, default=75.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    install()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        m78.run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(m78.summary_line(out), flush=True)
    else:
        st = check(args.group, args.out_dir)
        print(f"check: {json.dumps({k: v for k, v in st.items() if k != 'm57'}, sort_keys=True)}",
              flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
