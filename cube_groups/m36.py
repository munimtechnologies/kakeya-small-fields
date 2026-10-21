# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Jobs m36 and m37: the last four classes of ("B", 5) at t = 6 that jobs m30, m32, m33 and m34
left open (notes/a20.md and its "Results of jobs m33 and m34"), with longer budgets.

Job m33 gave the eleven open classes of pair orbits 0 to 4 twelve minutes each and found seven
UNSAT; job m34 found all fourteen of pair orbits 6 to 8 UNSAT. Open now: classes 0 and 1 of pair
orbit 2 (R = span(e_1, e_2, e_3)) and classes 0 and 1 of pair orbit 4 (R = span(e_0 + e_3, e_1,
e_2)), each UNKNOWN at 12 minutes. The rule of m32/predictions.md: 10 or fewer open -> at least 40
minutes each, at most three per job. Here two per job, so each gets more:

    m36: pair orbit 2, classes 0 and 1
    m37: pair orbit 4, classes 0 and 1

Within a job the instances run in order, and each gets an equal share of the group time still
left (the first gets half; if it finishes early the second gets the rest). Every instance is
rebuilt with job m30's seeds (a6_r3m.py, unchanged) and its A_u is compared with the value job m30
used (m32.EXPECTED_AU) before it runs. The positive control at t = 6 and the grading are those of
m32.py (--part control6, --part grade), run as separate steps of the job.

Parts: open --group m36|m37 (needs python-sat).
"""
import argparse
import json
import os
import time

import a6_r3m as m
import m32

T = m32.T
RHO = m32.RHO

GROUPS = {"m36": ["r3m_t6_r3_B5_o002_m000", "r3m_t6_r3_B5_o002_m001"],
          "m37": ["r3m_t6_r3_B5_o004_m000", "r3m_t6_r3_B5_o004_m001"]}
MIN_SECONDS = 40 * 60     # the floor of the pre-registered rule


def share(left_seconds, remaining):
    """An equal share of the group time still left among the instances still to run."""
    return left_seconds / remaining if remaining > 0 else 0.0


def run_open(group, group_seconds, out_dir):
    """The group's instances, each with its share of what is left; an instance whose rebuilt A_u
    differs from job m30's is not run (status MISMATCH)."""
    os.makedirs(out_dir, exist_ok=True)
    by_name = {sp["name"]: sp for sp in m.specs(T, T + 1, RHO, "B", 5, out_dir)}
    names = GROUPS[group]
    start = time.time()
    counts = {}
    for k, name in enumerate(names):
        sp = by_name.get(name)
        budget = share(group_seconds - (time.time() - start), len(names) - k)
        if sp is None or sp["au"] != m32.EXPECTED_AU[name]:
            res = {"name": name, "status": "MISMATCH", "au": sp["au"] if sp else None}
            with open(os.path.join(out_dir, name + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        elif budget < 1:
            res = dict(sp, status="SKIPPED")
            with open(os.path.join(out_dir, name + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            print(f"m36 {group}: {name} with {budget / 60:.1f} minutes", flush=True)
            res = m.solve_one(sp, "auto", budget, out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    print(f"SUMMARY open {group} instances {len(names)} {json.dumps(counts, sort_keys=True)}",
          flush=True)
    return counts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["open"], default="open")
    ap.add_argument("--group", choices=sorted(GROUPS), default="m36")
    ap.add_argument("--group-minutes", type=float, default=148.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    run_open(args.group, args.group_minutes * 60, args.out_dir)


if __name__ == "__main__":
    main()
