# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m65: the rest of job m47's list of (B6) at t = 7 and dim V = 9, under the rule that job m61
wrote down before it ran (cube_groups/m61-predictions.md; notes/a53.md, a54.md).

m61b gave CaDiCaL 15 minutes on the 16 classes with d = dim(X_1 n R) = 1 of m47's list: 4 UNSAT,
7 UNKNOWN at 900 s, 5 SKIPPED because their whole 15 minutes no longer fitted. m61's rule: "SKIPPED
classes and the 5 with d = 0: the next job, unchanged, 15 minutes each." This job is that job:

  the 5 classes m61b skipped (d = 1), then the 5 classes with d = 0 of m47's list,
  CaDiCaL for 15 minutes each, whole budgets only, 152 minutes in all (so all 10 fit even if every
  one runs to its cap).

The 7 classes m61b left open join the second-matrix split of Proposition 33 (notes/a52.md); they are
not in this job. Instances, representatives and the check are m61.py's, imported unchanged (m61.py
imports m57.py, which imports sat_aniso.py, all unchanged).

Parts:
    check   graded: m61.py's own check (m57.py's 14 checks, the kind-L setting, m47's list with d by
            hand, both probes); m61b's 4 + 7 + 5 = 16 classes with d = 1 and this job's 10 classes,
            each in m47's list with the d of its group, the lists disjoint, none closed before.
    solve   the plan in order.
    grade   graded checks and every SAT verified; statuses by d.

Usage: python m65.py --part check|solve|grade [--group-minutes 152] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m57 as m
import m61

# m61b's results (compete-results/m61b-b6m47d1-v1/out/grade.json, graded 2026-10-21).
UNSAT_M61B = ("r3b_t7_B6_o007_c002", "r3b_t7_B6_o007_c003", "r3b_t7_B6_o007_c006",
              "r3b_t7_B6_o007_c009")
OPEN_M61B = ("r3b_t7_B6_o007_c001", "r3b_t7_B6_o007_c007", "r3b_t7_B6_o008_c004",
             "r3b_t7_B6_o009_c000", "r3b_t7_B6_o009_c001", "r3b_t7_B6_o009_c002",
             "r3b_t7_B6_o009_c003")
SKIPPED_M61B = ("r3b_t7_B6_o009_c005", "r3b_t7_B6_o010_c004", "r3b_t7_B6_o010_c006",
                "r3b_t7_B6_o010_c007", "r3b_t7_B6_o010_c008")
D0_M47 = ("r3b_t7_B6_o011_c002", "r3b_t7_B6_o011_c003", "r3b_t7_B6_o012_c004",
          "r3b_t7_B6_o012_c009", "r3b_t7_B6_o012_c011")
GROUP_OF = dict([(n, "d1") for n in SKIPPED_M61B] + [(n, "d0") for n in D0_M47])


def plan():
    """[(spec, arm, cap seconds, "full")]: whole budgets only, as m61.plan."""
    return [(m61.b6_spec(n, m61.OPEN_M47[n]), "cadical", m61.CLASS_CAP, "full")
            for n in SKIPPED_M61B + D0_M47]


# ---------- check ----------

def check(out_dir):
    start = time.time()
    st61 = m61.check(out_dir)
    graded = {"m61_" + k: v for k, v in st61["graded"].items()}
    st = {"m61": {k: v for k, v in st61.items() if k != "graded"}}
    d1 = {s["name"] for s in m61.classes_with_d(1)}
    d0 = {s["name"] for s in m61.classes_with_d(0)}
    parts = (UNSAT_M61B, OPEN_M61B, SKIPPED_M61B)
    graded["m61b_partition"] = (sum(len(p) for p in parts) == len(d1) == 16
                                and set().union(*map(set, parts)) == d1)
    graded["d0_list"] = len(D0_M47) == 5 and set(D0_M47) == d0
    graded["not_closed"] = not (set(GROUP_OF) & set(m61.CLOSED_KNOWN)
                                or set(GROUP_OF) & set(m61.OPEN_M45_NAMES))
    graded["plan"] = ([e[0]["name"] for e in plan()] == list(SKIPPED_M61B + D0_M47)
                      and all(m.meet_d(e[0]) == (1 if GROUP_OF[e[0]["name"]] == "d1" else 0)
                              for e in plan()))
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- solving ----------

def run_solve(group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    counts = {}
    for spec, arm, cap, _ in plan():
        left = group_seconds - (time.time() - start)
        if left < cap:
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = m.solve_one(spec, arm, cap, out_dir)
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m65-predictions.md) ----------

def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    rows, by_key, status = {}, {}, {}
    for spec, arm, _, _ in plan():
        tag = m.tag_of(spec, arm)
        path = os.path.join(out_dir, tag + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows[tag] = [s, r.get("wall_seconds"), r.get("budget_seconds")]
        status[spec["name"]] = s
        if s == "SAT":
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
        key = GROUP_OF[spec["name"]]
        by_key.setdefault(key, {})
        by_key[key][s] = by_key[key].get(s, 0) + 1
    names = list(SKIPPED_M61B + D0_M47)
    return {"graded": graded, "ungraded": ungraded, "rows": rows, "by": by_key,
            "any_sat_7": any(v[0] == "SAT" for v in rows.values()),
            "m65": {n: status.get(n) for n in names},
            "b6_unsat": [n for n in names if status.get(n) == "UNSAT"],
            "b6_skipped": [n for n in names if status.get(n) == "SKIPPED"],
            "b6_open": [n for n in names if status.get(n) not in ("UNSAT", "SKIPPED")]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group-minutes", type=float, default=152.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} b6_unsat {len(out['b6_unsat'])} "
              f"b6_skipped {len(out['b6_skipped'])} by {json.dumps(out['by'], sort_keys=True)}",
              flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
