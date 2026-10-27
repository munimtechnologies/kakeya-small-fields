# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m114: m102's full sweep CNF at 1,500 s on the 80 d = 1 cases with k(T(N)) <= 4 that have not
had it yet (notes/a105.md, cube_groups/m114-predictions.md).

What came back on 2026-10-26 (notes/a105.md): the re-filed shard m110i ran to the end and left 54 of
its 387 cases open (333 UNSAT), and shards m112a-h of the 1,500 s sweep refuted 231 of their 267
cases, left 10 UNKNOWN at 1,500 s and skipped 26 when the shard's 210 minutes ran out. Shards
m112i-l are still in the queue.

So this job takes the cases that the rule of m112-predictions.md has not been applied to yet: the 54
m110i left open and the 26 m112a-h skipped. The 10 that stayed UNKNOWN at 1,500 s are not in it:
by that rule they go to cube and conquer, not to a longer cap. Six shards of 13 or 14 cases, so
each shard should finish well inside its time.

Parts:

    check     the grade files of m110i and m112a-h; 54 open in m110i, 26 skipped in m112a-h,
              disjoint, none with an UNSAT answer, all d = 1 cases; this shard's share; which
              leave pi(R) invariant, by label
    controls  m110's three controls at "n" (60 s); each must be SAT with a verified model
    run       this shard's cases with the sweep CNF (1,500 s each), two at a time, while time
              remains
    grade     the graded checks of m114-predictions.md (as m112's)

Usage: python m114.py --part check|controls|run|grade --shard a..f [--sweep-seconds S]
       [--workers W] [--minutes M] [--out-dir D]
       (the grade files m110i_grade.json and m112{a..h}_grade.json must be in the working
       directory)
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
import m111
import m112

M112_RUN = "abcdefgh"          # m112i-l were still queued when this job was written
SHARDS = "abcdef"
N_M110I_OPEN = 54
N_M112_SKIPPED = 26
TOTAL = N_M110I_OPEN + N_M112_SKIPPED
# 80 = 6 * 13 + 2: shards a and b take 14 cases, c-f 13
SIZE = {s: 14 if s in "ab" else 13 for s in SHARDS}
N_CAP = 60.0
SWEEP_CAP = 1500.0


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def sources(src="."):
    """(m110i grade, {shard: m112 grade}), or None if a grade file is missing."""
    g = m100.load(src, "m110i_grade.json")
    if g is None:
        return None
    m = {}
    for s in M112_RUN:
        m[s] = m100.load(src, f"m112{s}_grade.json")
        if m[s] is None:
            return None
    return g, m


def split(g, m):
    """(m110i's open cases, m112a-h's skipped cases), each sorted by name."""
    skipped = [t[:-len("_sweep")] for s in M112_RUN for t in m[s]["skipped"]]
    return sorted(g["open"]), sorted(skipped)


def unsat_before(g, m):
    """Every case with an UNSAT answer in m110i or m112a-h."""
    out = {x for x, parts in g["cases"].items() if "UNSAT" in parts.values()}
    for s in M112_RUN:
        out |= set(m[s]["unsat"])
    return out


def shard_list(shard, names):
    return [x for i, x in enumerate(names) if SHARDS[i % len(SHARDS)] == shard]


# ---------- the parts ----------

def run_check(shard, out_dir):
    g, info = {}, {}
    src = sources()
    g["grades_loaded"] = src is not None
    opened, skipped = split(*src) if src else ([], [])
    g["m110i_open_54"] = len(opened) == N_M110I_OPEN
    g["m112_skipped_26"] = len(skipped) == N_M112_SKIPPED
    g["disjoint"] = not set(opened) & set(skipped)
    names = sorted(set(opened) | set(skipped))
    g["total_80"] = len(names) == TOTAL
    g["none_unsat"] = bool(src) and not set(names) & unsat_before(*src)
    cases = m112.d1_cases()
    g["names_d1"] = all(x in cases for x in names)
    mine = shard_list(shard, names)
    g["shard_size"] = len(mine) == SIZE[shard]
    pres = {x: m111.features(*cases[x])["pres_r"] for x in names if x in cases}
    by_label = {}
    for x, p in pres.items():
        m112.tally(by_label, x[20:], "pres_r" if p else "not")
    info.update({"shard": mine, "total": len(names), "from_m110i": len(opened),
                 "from_m112": len(skipped), "pres_r": sum(pres.values()),
                 "not_pres_r": sorted(x for x, p in pres.items() if not p),
                 "by_label": by_label, "graded": g})
    save(out_dir, f"m114{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    short = {k: info[k] for k in ("total", "from_m110i", "from_m112", "pres_r", "not_pres_r")}
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps(dict(short, shard=len(mine)), sort_keys=True)}", flush=True)


def run_controls(shard, cap, out_dir):
    rows = []
    for spec, case in m110.control_cases():
        x = m102.inst_name(spec, case)
        row = m106.solve_masks(spec, case, m106.n_masks(), f"{x}_control", "control", cap, out_dir)
        m110.drop_child(out_dir, row)
        rows.append(row)
    g = {"controls_sat": len(rows) == 3 and all(r["status"] == "SAT" and r.get("verified")
                                                for r in rows)}
    save(out_dir, f"m114{shard}_controls.json", {"graded": g, "rows": rows})
    print(f"SUMMARY controls {shard} all_match {all(g.values())} "
          f"{json.dumps([[r['instance'][10:], r['status'], r.get('verified')] for r in rows])}",
          flush=True)


def run(shard, cap, workers, minutes, out_dir):
    start = time.time()
    name = f"m114{shard}_rows.json"
    info = m100.load(out_dir, f"m114{shard}_check.json") or {"shard": []}
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
    save(out_dir, f"m114{shard}_skipped.json", sorted(skipped))
    print(f"SUMMARY run {shard} skipped {len(skipped)} {json.dumps(tab, sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m114{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m114{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m114{shard}_rows.json") or []
    skipped = m100.load(out_dir, f"m114{shard}_skipped.json")
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
    ap.add_argument("--minutes", type=float, default=210.0)
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
        save(args.out_dir, f"m114{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
