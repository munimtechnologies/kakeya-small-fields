# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m119: m102's full sweep CNF at 1,500 s on the one d = 1 case with k(T(N)) <= 4 that has had
no sweep run yet, o010_c008 t3_m012_032, skipped by shard m112l when its 210 minutes ran out
(notes/a107.md, notes/a108.md, cube_groups/m119-predictions.md).

What came back on 2026-10-27/28 (notes/a108.md): job m116 refuted 11 of the 14 cases m112i-k had
skipped and left 3 UNKNOWN; job m115 verified the DRAT certificates of the last two m110 cases. So
3,845 of the 3,876 d = 1 cases have UNSAT answers, 30 are UNKNOWN at 1,500 s, and this case is the
only one never run at 1,500 s. A thin wrapper on m112.solve_sweep, as m116 was.

Parts:

    check     m112l's grade file lists this case as skipped, with no UNSAT answer; it is a d = 1 case
    controls  m110's three controls at "n" (60 s); each must be SAT with a verified model
    run       the case with the sweep CNF (1,500 s)
    grade     the graded checks of m119-predictions.md (as m112's)

Usage: python m119.py --part check|controls|run|grade [--sweep-seconds S] [--out-dir D]
       (the grade file m112l_grade.json must be in the working directory)
"""
import argparse
import json
import os
import time

import m100
import m102
import m106
import m110
import m112

CASE = "r3b_t8_B7_o010_c008_t3_m012_032"
N_CAP = 60.0
SWEEP_CAP = 1500.0


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the parts ----------

def run_check(out_dir):
    g = {}
    m = m100.load(".", "m112l_grade.json")
    g["grade_loaded"] = m is not None
    g["skipped_in_m112l"] = bool(m) and f"{CASE}_sweep" in m["skipped"]
    g["not_unsat"] = bool(m) and CASE not in m["unsat"]
    g["case_d1"] = CASE in m112.d1_cases()
    save(out_dir, "m119_check.json", {"case": CASE, "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check all_match {not bad} graded {len(g)} failed {bad}", flush=True)


def run_controls(cap, out_dir):
    rows = []
    for spec, case in m110.control_cases():
        x = m102.inst_name(spec, case)
        row = m106.solve_masks(spec, case, m106.n_masks(), f"{x}_control", "control", cap, out_dir)
        m110.drop_child(out_dir, row)
        rows.append(row)
    g = {"controls_sat": len(rows) == 3 and all(r["status"] == "SAT" and r.get("verified")
                                                for r in rows)}
    save(out_dir, "m119_controls.json", {"graded": g, "rows": rows})
    print(f"SUMMARY controls all_match {all(g.values())} "
          f"{json.dumps([[r['instance'][10:], r['status'], r.get('verified')] for r in rows])}",
          flush=True)


def run(cap, out_dir):
    start = time.time()
    row = m112.solve_sweep(CASE, cap, start + 3600, out_dir)
    m110.drop_child(out_dir, row)
    save(out_dir, "m119_rows.json", [row])
    save(out_dir, "m119_skipped.json", [])
    print(f"SUMMARY run {CASE[10:]} {row['status']} wall {row.get('wall_seconds')} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade(out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m119_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    rows = m100.load(out_dir, "m119_rows.json") or []
    skipped = m100.load(out_dir, "m119_skipped.json")
    rg, out = m112.grade_rows(rows, skipped or [], [CASE])
    g.update(rg)
    g["run_ran"] = skipped is not None
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "run", "grade"], default="check")
    ap.add_argument("--sweep-seconds", type=float, default=SWEEP_CAP)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.out_dir)
    elif args.part == "controls":
        run_controls(N_CAP, args.out_dir)
    elif args.part == "run":
        run(args.sweep_seconds, args.out_dir)
    else:
        out = grade(args.out_dir)
        save(args.out_dir, "m119_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "by_label")}
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad} "
              f"{json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
