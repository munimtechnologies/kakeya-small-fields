# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m118: DRAT certificates for the 333 d = 1 cases with k(T(N)) <= 4 that the re-filed job
m110i refuted (332 by m106's "n" CNF, one by m102's sweep CNF at 120 s), exactly as job m113
certified the 3,075 of m110a-h and j (cube_groups/m118-predictions.md).

What came back on 2026-10-27 (notes/a107.md): m113's six shards verified 3,073 of their 3,075
cases (the other two are re-run by m115 with doubled caps); m113 left m110i out because m110i had
been stopped from outside and was re-filed. Its 333 UNSAT answers are the cheapest part of what
Proposition 40 still needs: in m113 an "n" certificate took about 8 s of CaDiCaL and 9 s of
drat-trim (median).

Parts:

    check     m110i's grade file; its 333 cases with an UNSAT answer, by the CNF that was UNSAT
              (332 "n", 1 "sweep"); all d = 1 cases; none of them among m113's 3,075; the two
              programs present
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      the 333 cases, two at a time, while time remains, with m113's caps
    grade     the graded checks of m118-predictions.md (m113.grade_rows)

Usage: python m118.py --part check|controls|cert|grade [--tools DIR] [--workers W] [--minutes M]
       [--out-dir D]
       (the grade files m110{a..j}_grade.json must be in the working directory)
"""
import argparse
import concurrent.futures as cf
import json
import os
import time

import m100
import m111
import m113

TOTAL = 333
BY_MODE = {"n": 332, "sweep": 1}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def run_check(tools, out_dir):
    g = {}
    parts = m111.m110_parts("i")
    done = m111.m110_parts(m113.M110_DONE)
    g["grades_loaded"] = parts is not None and done is not None
    items = m113.decided(parts or {})
    g["total_333"] = len(items) == TOTAL
    by_mode = {}
    for _, m in items:
        by_mode[m] = by_mode.get(m, 0) + 1
    g["by_mode"] = by_mode == BY_MODE
    cases = m113.d1_cases()
    g["names_d1"] = all(x in cases for x, _ in items)
    m113_set = {x for x, _ in m113.decided(done or {})}
    g["m113_3075"] = len(m113_set) == m113.TOTAL
    g["disjoint_from_m113"] = not any(x in m113_set for x, _ in items)
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, "m118_check.json", {"shard": items, "by_mode": by_mode, "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'by_mode': by_mode, 'cases': len(items)}, sort_keys=True)}", flush=True)


def run_controls(tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, "m118_controls.json"))


def run_cert(tools, workers, minutes, out_dir):
    start = time.time()
    info = m100.load(out_dir, "m118_check.json") or {"shard": []}
    rows, counts = [], {}
    m113.d1_cases()            # build the table once, before the threads start
    deadline = start + minutes * 60
    # CaDiCaL and drat-trim run as child processes (m104), so threads are enough
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(m113.certify_item, tools, x, mode, deadline) for x, mode in info["shard"]]
        for fut in cf.as_completed(futs):
            row = fut.result()
            rows.append(row)
            save(out_dir, "m118_cert.json", rows)
            m113.tally(counts, row.get("mode"), row["cert"])
            if row["cert"] != "SKIPPED":
                print(f"cert {row['instance']}: {row['cert']} {row['mode']} inv {row['inv']} "
                      f"{row['type']} cadical {row['cadical']['seconds']} s drat "
                      f"{(row.get('drat') or {}).get('seconds')} s proof {row['proof_bytes']} B "
                      f"clauses {row['clauses']}", flush=True)
    print(f"SUMMARY cert cases {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def grade(out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m118_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, "m118_check.json") or {"shard": []}
    rows = m100.load(out_dir, "m118_cert.json")
    g["cert_ran"] = rows is not None
    rg, out = m113.grade_rows(rows or [], chk["shard"])
    g.update(rg)
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--minutes", type=float, default=200.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.tools, args.workers, args.minutes, args.out_dir)
    else:
        out = grade(args.out_dir)
        save(args.out_dir, "m118_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
