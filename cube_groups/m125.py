# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m125: DRAT certificates for the d = 1 refutations that the certificate jobs m120a and
m120h-l skipped for time, and a second try, with longer limits, at the four that ran out of
CaDiCaL's 1,800 s limit (m120k, m122a, m123a, m123b) (notes/a115.md,
cube_groups/m125-predictions.md).

What came back by 2026-10-29 (notes/a114.md, a115.md): m120a, h, i, j, k and l skipped 11, 15, 1,
3, 8 and 4 cases (42) when their start windows ran out, and four cases came back UNKNOWN at
CaDiCaL's 1,800 s limit. Shards a, b and c certify the 42 exactly as m120 does it (sweep CNF,
CaDiCaL at 1,800 s, drat-trim at 3,000 s), 14 each, three at a time; shard d runs the four
UNKNOWN cases with CaDiCaL at 4,800 s and drat-trim at 7,200 s, four at a time.

Parts:

    check     the grade files: the 42 SKIPPED and the 4 UNKNOWN, disjoint from every VERIFIED row of
              those files, all d = 1 cases, none among the 3,408 that m110a-j decided; this shard's
              share (a-c by index mod 3 in name order; d the UNKNOWN cases); both programs
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      this shard's cases, --workers at a time; no case starts after --minutes
    grade     the graded checks of m125-predictions.md (m113.grade_rows)

Usage: python m125.py --part check|controls|cert|grade --shard a|b|c|d [--tools DIR]
       [--workers W] [--minutes M] [--out-dir D]
       (the grade files of m110a-j, m120a and m120h-l, m122a and m123a-b in the working directory)
"""
import argparse
import concurrent.futures as cf
import json
import os
import time

import m100
import m111
import m113

SKIP_SHARDS = "abc"
SOURCES_SKIPPED = ("m120a", "m120h", "m120i", "m120j", "m120k", "m120l")
SOURCES_UNKNOWN = ("m120k", "m122a", "m123a", "m123b")
N_SKIPPED = 42                 # 11 + 15 + 1 + 3 + 8 + 4
N_UNKNOWN = 4                  # one each in m120k, m122a, m123a, m123b
N_M110 = 3408
SIZE = {"a": 14, "b": 14, "c": 14, "d": 4}
MODE = "sweep"
CADICAL_CAP = {"a": 1800.0, "b": 1800.0, "c": 1800.0, "d": 4800.0}
DRAT_CAP = {"a": 3000, "b": 3000, "c": 3000, "d": 7200}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def source_rows(names, src="."):
    """{instance: [cert, ...]} over the named grade files, or None if one is missing."""
    out = {}
    for name in names:
        g = m100.load(src, f"{name}_grade.json")
        if g is None:
            return None
        for x, row in g["rows"].items():
            out.setdefault(x, []).append(row[0])
    return out


def cases(src="."):
    """(SKIPPED names, UNKNOWN names), each sorted, or None if a grade file is missing."""
    skipped = source_rows(SOURCES_SKIPPED, src)
    unknown = source_rows(SOURCES_UNKNOWN, src)
    if skipped is None or unknown is None:
        return None
    return (sorted(x for x, c in skipped.items() if "SKIPPED" in c),
            sorted(x for x, c in unknown.items() if "UNKNOWN" in c))


def shard_list(shard, skipped, unknown):
    if shard == "d":
        return [[x, MODE] for x in unknown]
    return [[x, MODE] for i, x in enumerate(skipped) if SKIP_SHARDS[i % len(SKIP_SHARDS)] == shard]


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    both = cases()
    rows_s = source_rows(SOURCES_SKIPPED) or {}
    rows_u = source_rows(SOURCES_UNKNOWN) or {}
    parts = m111.m110_parts("abcdefghij")
    g["grades_loaded"] = both is not None and parts is not None
    skipped, unknown = both or ([], [])
    verified = {x for r in (rows_s, rows_u) for x, c in r.items() if "VERIFIED" in c}
    g["skipped_42"] = len(skipped) == N_SKIPPED
    g["unknown_4"] = len(unknown) == N_UNKNOWN
    g["disjoint"] = not (set(skipped) | set(unknown)) & verified and not set(skipped) & set(unknown)
    d1 = m113.d1_cases()
    g["names_d1"] = all(x in d1 for x in skipped + unknown)
    decided = {x for x, _ in m113.decided(parts or {})}
    g["m110_3408"] = len(decided) == N_M110
    g["disjoint_from_m110"] = not (set(skipped) | set(unknown)) & decided
    mine = shard_list(shard, skipped, unknown)
    g["shard_size"] = len(mine) == SIZE[shard]
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"m125{shard}_check.json",
         {"shard": mine, "skipped": len(skipped), "unknown": len(unknown), "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'skipped': len(skipped), 'unknown': len(unknown), 'shard': len(mine)}, sort_keys=True)}",
          flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"m125{shard}_controls.json"))


def run_cert(shard, tools, workers, minutes, out_dir):
    m113.CADICAL_CAP = CADICAL_CAP[shard]
    m113.DRAT_CAP = {"n": 1200, "sweep": DRAT_CAP[shard]}
    start = time.time()
    name = f"m125{shard}_cert.json"
    info = m100.load(out_dir, f"m125{shard}_check.json") or {"shard": []}
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
        st = m100.load(out_dir, f"m125{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m125{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m125{shard}_cert.json")
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
    ap.add_argument("--shard", choices=list(SIZE), default="a")
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
        save(args.out_dir, f"m125{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
