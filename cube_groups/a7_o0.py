# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m22: the one instance of job m21 left undecided, orbit 0 at (t, k) = (7, 4)
(M_1 = M_2 = M_3 = 0), with a long time budget. The CNF is a7_c.encode_a7 unchanged, so the
answer does not use Lemma 59 or Theorem 29 of notes/a7.md: it is an independent check of them
(Lemma 59 says this CNF, like every CNF of a7_c.py at (7, 4), is unsatisfiable).

Usage: python a7_o0.py --part solve|grade [--budget-minutes 170] [--out-dir DIR]
"""
import argparse
import json
import os

import a7_c


def solve(budget_minutes, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    idx, Ms = a7_c.reps(7, 4)[0]
    return a7_c.solve_one(7, 4, idx, Ms, "auto", budget_minutes * 60, out_dir)


# Pre-registered (m22/predictions.md): the instance is orbit 0 with Ms = (0, 0, 0); there is no
# SAT answer. UNSAT and UNKNOWN are both consistent with Lemma 59; a SAT answer would refute it.
def grade(out_dir):
    idx, Ms = a7_c.reps(7, 4)[0]
    path = os.path.join(out_dir, a7_c.instance_name(7, 4, idx) + ".json")
    graded, ungraded = {"orbit_0_is_zero": idx == 0 and tuple(Ms) == (0, 0, 0)}, {}
    try:
        with open(path) as f:
            r = json.load(f)
    except (OSError, ValueError):
        r = {"status": "missing"}
    if r["status"] in ("SAT", "UNSAT"):
        graded["no_sat"] = r["status"] == "UNSAT"
    else:
        ungraded["no_sat"] = r["status"]
    if r["status"] == "SAT":
        graded["sat_verified"] = bool(r.get("verified"))
    return {"graded": graded, "ungraded": ungraded, "status": r["status"],
            "wall_seconds": r.get("wall_seconds")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["solve", "grade"], default="grade")
    ap.add_argument("--budget-minutes", type=float, default=170.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    if args.part == "solve":
        res = solve(args.budget_minutes, args.out_dir)
        print(f"SUMMARY solve {res['name']} {res['status']}", flush=True)
    else:
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"ungraded {json.dumps(out['ungraded'])}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
