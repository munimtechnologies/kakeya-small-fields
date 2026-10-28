# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m120: DRAT certificates for the 435 d = 1 cases with k(T(N)) <= 4 that only m102's sweep CNF
refuted (jobs m112a-l, m114a-f, m116a-b and m119, at 1,500 s) and that the pilot m117 did not
already certify (cube_groups/m120-predictions.md).

What came back on 2026-10-28 (notes/a109.md): the pilot m117 VERIFIED all three of its sweep cases;
the CaDiCaL binary with proof logging took 0.49 to 0.66 times pysat's time, drat-trim 0.98 to 1.26
times CaDiCaL's, the largest proof was 554 MB and the wall time per case 1.0 to 1.5 times pysat's.
By m117's decision rule (all three VERIFIED at most 3x pysat's time) the full run is filed. m118
VERIFIED all 333 cases of m110i, and m119 refuted the one case never run at 1,500 s, so 3,846 of the
3,876 d = 1 cases have UNSAT answers and 3,411 have checked certificates (m113, m115, m117, m118).
This job certifies the other 435, each as m113 does it, with CaDiCaL at 1,800 s and drat-trim at
3,000 s (CaDiCaL ran well under pysat's time in m117, and pysat's times were all under 1,500 s).

Parts:

    check     the grade files: the sweep UNSATs of m112a-l, m114a-f, m116a-b and m119 (438), less
              m117's three VERIFIED cases, gives 435; all d = 1 cases; none among the 3,408 that
              m110a-j decided; this shard's share (by index mod 16 in name order); both programs
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      this shard's cases, two at a time; no case starts after --minutes
    grade     the graded checks of m120-predictions.md (m113.grade_rows)

Usage: python m120.py --part check|controls|cert|grade --shard a..p [--tools DIR] [--workers W]
       [--minutes M] [--out-dir D]
       (the grade files of m110a-j, m112a-l, m114a-f, m116a-b, m117 and m119 in the working
       directory)
"""
import argparse
import concurrent.futures as cf
import json
import os
import time

import m100
import m111
import m113

SHARDS = "abcdefghijklmnop"
SWEEP_SOURCES = (["m112" + s for s in "abcdefghijkl"] + ["m114" + s for s in "abcdef"]
                 + ["m116a", "m116b", "m119"])
PILOT = "m117"
N_SWEEP_UNSAT = 438            # 3,846 UNSAT answers minus the 3,408 that m110a-j decided
N_PILOT = 3
N_M110 = 3408
TOTAL = 435
# 435 = 16 * 27 + 3: shards a-c take 28 cases, d-p 27
SIZE = {s: 28 if s in "abc" else 27 for s in SHARDS}
MODE = "sweep"
CADICAL_CAP = 1800.0
DRAT_CAP = {"n": 1200, "sweep": 3000}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def sweep_unsat(src="."):
    """Every case that a sweep grade file gives as UNSAT, or None if a grade file is missing."""
    out = set()
    for name in SWEEP_SOURCES:
        g = m100.load(src, f"{name}_grade.json")
        if g is None:
            return None
        out |= set(g["unsat"])
    return out


def pilot_verified(src="."):
    """The cases m117 VERIFIED, or None if its grade file is missing."""
    g = m100.load(src, f"{PILOT}_grade.json")
    if g is None:
        return None
    return {x for x, row in g["rows"].items() if row[0] == "VERIFIED"}


def cases(src="."):
    """The cases to certify, sorted by name, or None if a grade file is missing."""
    unsat, pilot = sweep_unsat(src), pilot_verified(src)
    if unsat is None or pilot is None:
        return None
    return sorted(unsat - pilot)


def shard_list(shard, names):
    return [[x, MODE] for i, x in enumerate(names) if SHARDS[i % len(SHARDS)] == shard]


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    unsat, pilot = sweep_unsat(), pilot_verified()
    parts = m111.m110_parts("abcdefghij")
    g["grades_loaded"] = unsat is not None and pilot is not None and parts is not None
    unsat, pilot = unsat or set(), pilot or set()
    g["sweep_unsat_438"] = len(unsat) == N_SWEEP_UNSAT
    g["pilot_3_inside"] = len(pilot) == N_PILOT and pilot <= unsat
    names = sorted(unsat - pilot)
    g["total_435"] = len(names) == TOTAL
    d1 = m113.d1_cases()
    g["names_d1"] = all(x in d1 for x in names)
    decided = {x for x, _ in m113.decided(parts or {})}
    g["m110_3408"] = len(decided) == N_M110
    g["disjoint_from_m110"] = not set(names) & decided
    mine = shard_list(shard, names)
    g["shard_size"] = len(mine) == SIZE[shard]
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"m120{shard}_check.json", {"shard": mine, "total": len(names), "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'total': len(names), 'shard': len(mine)}, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"m120{shard}_controls.json"))


def run_cert(shard, tools, workers, minutes, out_dir):
    m113.CADICAL_CAP, m113.DRAT_CAP = CADICAL_CAP, DRAT_CAP
    start = time.time()
    name = f"m120{shard}_cert.json"
    info = m100.load(out_dir, f"m120{shard}_check.json") or {"shard": []}
    rows, counts = [], {}
    m113.d1_cases()            # build the table once, before the threads start
    deadline = start + minutes * 60
    # CaDiCaL and drat-trim run as child processes (m104), so threads are enough
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(m113.certify_item, tools, x, mode, deadline) for x, mode in info["shard"]]
        for fut in cf.as_completed(futs):
            row = fut.result()
            rows.append(row)
            save(out_dir, name, rows)
            m113.tally(counts, row.get("mode"), row["cert"])
            if row["cert"] != "SKIPPED":
                print(f"cert {row['instance']}: {row['cert']} {row['mode']} inv {row['inv']} "
                      f"{row['type']} cadical {row['cadical']['seconds']} s drat "
                      f"{(row.get('drat') or {}).get('seconds')} s proof {row['proof_bytes']} B "
                      f"clauses {row['clauses']} wall {row['wall_seconds']} s", flush=True)
    print(f"SUMMARY cert {shard} cases {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m120{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m120{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m120{shard}_cert.json")
    g["cert_ran"] = rows is not None
    rg, out = m113.grade_rows(rows or [], chk["shard"])
    g.update(rg)
    done = [r for r in rows or [] if "wall_seconds" in r]
    out["wall_seconds_max"] = max((r["wall_seconds"] for r in done), default=None)
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--shard", choices=list(SHARDS), default="a")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--minutes", type=float, default=190.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.shard, args.tools, args.workers, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m120{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
