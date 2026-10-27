# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m116: m102's full sweep CNF at 1,500 s on the 14 d = 1 cases with k(T(N)) <= 4 that shards
m112i-k skipped when their 210 minutes ran out (notes/a106.md, cube_groups/m116-predictions.md).

What came back on 2026-10-27 (notes/a106.md): shards m112i-k of the 1,500 s sweep refuted 75 of their
99 cases, left 10 UNKNOWN and skipped 14; job m114 refuted 76 of its 80 and left 4 UNKNOWN, skipping
none. Shard m112l was stopped from outside and is re-filed. As in m114, the cases that stayed UNKNOWN
at 1,500 s are not in this job (they go to cube and conquer); only the skipped ones are. Two shards
of 7, so each finishes well inside its time.

Parts:

    check     the grade files of m112i-k; their 14 skipped cases (as listed below, read by hand),
              none with an UNSAT answer, all d = 1 cases; this shard's share
    controls  m110's three controls at "n" (60 s); each must be SAT with a verified model
    run       this shard's cases with the sweep CNF (1,500 s each), two at a time
    grade     the graded checks of m116-predictions.md (as m112's)

Usage: python m116.py --part check|controls|run|grade --shard a|b [--sweep-seconds S]
       [--workers W] [--minutes M] [--out-dir D]
       (the grade files m112{i,j,k}_grade.json must be in the working directory)
"""
import argparse
import concurrent.futures as cf
import json
import os
import time

import m100
import m102
import m106
import m110
import m112

M112_RUN = "ijk"               # m112l was stopped from outside at 08:22 UTC and is re-filed
SHARDS = "ab"
SKIPPED = sorted("r3b_t8_B7_" + x for x in (
    "o010_c003_t2_m011", "o010_c003_t3_m021_047", "o010_c005_t2_m012", "o010_c006_t2_m026",
    "o010_c007_t2_m031", "o010_c008_t2_m058",                                   # m112i
    "o010_c001_t3_m011_017", "o010_c003_t2_m012", "o010_c003_t3_m031_036", "o010_c005_t2_m015",
    "o010_c006_t2_m031", "o010_c007_t2_m034", "o010_c008_t2_m059",              # m112j
    "o010_c008_t3_m004_034"))                                                    # m112k
N_CAP = 60.0
SWEEP_CAP = 1500.0


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def sources(src="."):
    """{shard: m112 grade} for i-k, or None if a grade file is missing."""
    m = {s: m100.load(src, f"m112{s}_grade.json") for s in M112_RUN}
    return None if any(v is None for v in m.values()) else m


def skipped_of(m):
    return sorted(t[:-len("_sweep")] for s in M112_RUN for t in m[s]["skipped"])


def shard_list(shard, names):
    return [x for i, x in enumerate(names) if SHARDS[i % len(SHARDS)] == shard]


# ---------- the parts ----------

def run_check(shard, out_dir):
    g, info = {}, {}
    m = sources()
    g["grades_loaded"] = m is not None
    names = skipped_of(m) if m else []
    g["skipped_14_as_listed"] = names == SKIPPED
    g["none_unsat"] = bool(m) and not set(SKIPPED) & {x for s in M112_RUN for x in m[s]["unsat"]}
    g["names_d1"] = all(x in m112.d1_cases() for x in SKIPPED)
    mine = shard_list(shard, SKIPPED)
    g["shard_size"] = len(mine) == 7
    info.update({"shard": mine, "total": len(names), "graded": g})
    save(out_dir, f"m116{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"shard {len(mine)}", flush=True)


def run_controls(shard, cap, out_dir):
    rows = []
    for spec, case in m110.control_cases():
        x = m102.inst_name(spec, case)
        row = m106.solve_masks(spec, case, m106.n_masks(), f"{x}_control", "control", cap, out_dir)
        m110.drop_child(out_dir, row)
        rows.append(row)
    g = {"controls_sat": len(rows) == 3 and all(r["status"] == "SAT" and r.get("verified")
                                                for r in rows)}
    save(out_dir, f"m116{shard}_controls.json", {"graded": g, "rows": rows})
    print(f"SUMMARY controls {shard} all_match {all(g.values())} "
          f"{json.dumps([[r['instance'][10:], r['status'], r.get('verified')] for r in rows])}",
          flush=True)


def run(shard, cap, workers, minutes, out_dir):
    start = time.time()
    name = f"m116{shard}_rows.json"
    info = m100.load(out_dir, f"m116{shard}_check.json") or {"shard": []}
    tab, skipped = {}, []
    m112.d1_cases()            # build the table once, before the threads start
    deadline = start + minutes * 60
    # each solve runs in its own child process (m102.solve_one), so threads are enough
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        futs = {ex.submit(m112.solve_sweep, x, cap, deadline, out_dir): x for x in info["shard"]}
        for fut in cf.as_completed(futs):
            row = fut.result()
            if row is None:
                skipped.append(f"{futs[fut]}_sweep")
                continue
            m110.drop_child(out_dir, row)
            m112.append_row(out_dir, name, row)
            m112.tally(tab, "sweep", row["status"])
    save(out_dir, f"m116{shard}_skipped.json", sorted(skipped))
    print(f"SUMMARY run {shard} skipped {len(skipped)} {json.dumps(tab, sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m116{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m116{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m116{shard}_rows.json") or []
    skipped = m100.load(out_dir, f"m116{shard}_skipped.json")
    rg, out = m112.grade_rows(rows, skipped or [], chk["shard"])
    g.update(rg)
    g["run_ran"] = skipped is not None
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "run", "grade"], default="check")
    ap.add_argument("--shard", choices=list(SHARDS), default="a")
    ap.add_argument("--sweep-seconds", type=float, default=SWEEP_CAP)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, N_CAP, args.out_dir)
    elif args.part == "run":
        run(args.shard, args.sweep_seconds, args.workers, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m116{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
