# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m123: DRAT certificates for the 30 d = 1 refutations that m120e, m120f and m120g skipped for
time (notes/a111.md, cube_groups/m123-predictions.md).

What came back on 2026-10-28 (notes/a111.md): m120e VERIFIED 17 sweep certificates, m120f 13 and
m120g 18, none NOT_VERIFIED, no SAT, but they skipped 9, 13 and 8 cases when their 190 minutes ran
out (two cases at a time, about 30 minutes of CaDiCaL and drat-trim per case). This job certifies
those 30 exactly as m120 does it (sweep CNF, CaDiCaL at 1,800 s, drat-trim at 3,000 s), three at a
time with 230 minutes to start cases, so that every case should start.

Parts:

    check     the grade files: m120e-g skipped 30 (9 + 13 + 8) and VERIFIED 48; the two disjoint, all
              d = 1 cases, none among the 3,408 that m110a-j decided; this shard's share (by index
              mod 2 in name order); both programs
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      this shard's cases, --workers at a time; no case starts after --minutes
    grade     the graded checks of m123-predictions.md (m113.grade_rows)

Usage: python m123.py --part check|controls|cert|grade --shard a|b [--tools DIR] [--workers W]
       [--minutes M] [--out-dir D]
       (the grade files of m110a-j and m120e-g in the working directory)
"""
import argparse
import concurrent.futures as cf
import json
import os
import time

import m100
import m111
import m113

SHARDS = "ab"
SOURCES = ("m120e", "m120f", "m120g")
N_SKIPPED = 30                 # 9 (m120e) + 13 (m120f) + 8 (m120g)
N_VERIFIED = 48                # 17 + 13 + 18
N_M110 = 3408
TOTAL = 30
SIZE = {"a": 15, "b": 15}
MODE = "sweep"
CADICAL_CAP = 1800.0
DRAT_CAP = {"n": 1200, "sweep": 3000}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def source_rows(src="."):
    """{instance: cert} over m120e-g's grade files, or None if one is missing."""
    out = {}
    for name in SOURCES:
        g = m100.load(src, f"{name}_grade.json")
        if g is None:
            return None
        out.update({x: row[0] for x, row in g["rows"].items()})
    return out


def cases(src="."):
    """The cases to certify (SKIPPED in m120e-g), sorted by name, or None if a file is missing."""
    rows = source_rows(src)
    return None if rows is None else sorted(x for x, c in rows.items() if c == "SKIPPED")


def shard_list(shard, names):
    return [[x, MODE] for i, x in enumerate(names) if SHARDS[i % len(SHARDS)] == shard]


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    rows = source_rows()
    parts = m111.m110_parts("abcdefghij")
    g["grades_loaded"] = rows is not None and parts is not None
    rows = rows or {}
    names = sorted(x for x, c in rows.items() if c == "SKIPPED")
    verified = {x for x, c in rows.items() if c == "VERIFIED"}
    g["skipped_30"] = len(names) == N_SKIPPED
    g["verified_48"] = len(verified) == N_VERIFIED
    g["disjoint"] = not set(names) & verified
    d1 = m113.d1_cases()
    g["names_d1"] = all(x in d1 for x in names)
    decided = {x for x, _ in m113.decided(parts or {})}
    g["m110_3408"] = len(decided) == N_M110
    g["disjoint_from_m110"] = not set(names) & decided
    mine = shard_list(shard, names)
    g["shard_size"] = len(mine) == SIZE[shard]
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"m123{shard}_check.json", {"shard": mine, "total": len(names), "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'total': len(names), 'shard': len(mine)}, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"m123{shard}_controls.json"))


def run_cert(shard, tools, workers, minutes, out_dir):
    m113.CADICAL_CAP, m113.DRAT_CAP = CADICAL_CAP, DRAT_CAP
    start = time.time()
    name = f"m123{shard}_cert.json"
    info = m100.load(out_dir, f"m123{shard}_check.json") or {"shard": []}
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
        st = m100.load(out_dir, f"m123{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m123{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m123{shard}_cert.json")
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
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--minutes", type=float, default=230.0)
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
        save(args.out_dir, f"m123{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
