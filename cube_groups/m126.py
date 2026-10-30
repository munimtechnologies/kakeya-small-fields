# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m126: DRAT certificates, with longer limits and one case per job, for the four d = 1
refutations that job m125 left without a checked certificate (notes/a117.md,
cube_groups/m126-predictions.md).

What came back on 2026-10-29 (notes/a116.md, a117.md): three cases ran out of CaDiCaL's 1,800 s
limit with proof logging on (r3b_t8_B7_o010_c004_t2_m031 in m125b, r3b_t8_B7_o010_c006_t3_m011_017
and r3b_t8_B7_o010_c007_t2_m031 in m125c), and in m125d drat-trim was killed by the job's 3 GB
memory cap while loading the 2.67 GB proof of r3b_t8_B7_o010_c000_t2_m011 (CaDiCaL had answered
UNSAT in 4,511 s), with three other cases running beside it. Shards a, b and c take the three
UNKNOWN cases in name order, CaDiCaL at 4,800 s and drat-trim at 7,200 s; shard d takes the
DRAT_STOPPED case alone, CaDiCaL at 6,000 s and drat-trim at 9,000 s. One case per job, so no
drat-trim shares memory with another.

Parts:

    check     the grade files of m125b, m125c and m125d: the 3 UNKNOWN and the 1 DRAT_STOPPED rows,
              all d = 1 cases, none among the 3,408 that m110a-j decided; this shard's case; both
              programs
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      this shard's case
    grade     the graded checks of m126-predictions.md (m113.grade_rows)

Usage: python m126.py --part check|controls|cert|grade --shard a|b|c|d [--tools DIR] [--out-dir D]
       (the grade files of m110a-j and m125b-d in the working directory)
"""
import argparse
import json
import os
import time

import m100
import m111
import m113

SOURCES = {"m125b": "UNKNOWN", "m125c": "UNKNOWN", "m125d": "DRAT_STOPPED"}
N_UNKNOWN = 3                  # one in m125b, two in m125c
N_STOPPED = 1                  # m125d
N_M110 = 3408
SHARDS = "abcd"                # a-c: the UNKNOWN cases in name order; d: the DRAT_STOPPED case
MODE = "sweep"
CADICAL_CAP = {"a": 4800.0, "b": 4800.0, "c": 4800.0, "d": 6000.0}
DRAT_CAP = {"a": 7200, "b": 7200, "c": 7200, "d": 9000}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def cases(src="."):
    """(UNKNOWN names, DRAT_STOPPED names), each sorted, or None if a grade file is missing."""
    found = {"UNKNOWN": set(), "DRAT_STOPPED": set()}
    for name, status in SOURCES.items():
        g = m100.load(src, f"{name}_grade.json")
        if g is None:
            return None
        found[status] |= {x for x, row in g["rows"].items() if row[0] == status}
    return sorted(found["UNKNOWN"]), sorted(found["DRAT_STOPPED"])


def verified(src="."):
    """Names with a VERIFIED row in any of the source grade files."""
    out = set()
    for name in SOURCES:
        g = m100.load(src, f"{name}_grade.json") or {"rows": {}}
        out |= {x for x, row in g["rows"].items() if row[0] == "VERIFIED"}
    return out


def shard_list(shard, unknown, stopped):
    items = unknown + stopped
    i = SHARDS.index(shard)
    return [[items[i], MODE]] if i < len(items) else []


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    both = cases()
    parts = m111.m110_parts("abcdefghij")
    g["grades_loaded"] = both is not None and parts is not None
    unknown, stopped = both or ([], [])
    g["unknown_3"] = len(unknown) == N_UNKNOWN
    g["stopped_1"] = len(stopped) == N_STOPPED
    g["disjoint"] = not (set(unknown) | set(stopped)) & verified() and not set(unknown) & set(stopped)
    d1 = m113.d1_cases()
    g["names_d1"] = all(x in d1 for x in unknown + stopped)
    decided = {x for x, _ in m113.decided(parts or {})}
    g["m110_3408"] = len(decided) == N_M110
    g["disjoint_from_m110"] = not (set(unknown) | set(stopped)) & decided
    mine = shard_list(shard, unknown, stopped)
    g["shard_size"] = len(mine) == 1
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"m126{shard}_check.json",
         {"shard": mine, "unknown": unknown, "stopped": stopped, "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'unknown': len(unknown), 'stopped': len(stopped), 'shard': mine}, sort_keys=True)}",
          flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"m126{shard}_controls.json"))


def run_cert(shard, tools, out_dir):
    m113.CADICAL_CAP = CADICAL_CAP[shard]
    m113.DRAT_CAP = {"n": 1200, "sweep": DRAT_CAP[shard]}
    start = time.time()
    name = f"m126{shard}_cert.json"
    info = m100.load(out_dir, f"m126{shard}_check.json") or {"shard": []}
    rows, counts = [], {}
    for x, mode in info["shard"]:
        try:
            row = m113.certify_item(tools, x, mode, start + 3600)
        except Exception as e:  # keep the part's exit code 0; the grade sees the missing row
            print(f"cert {x}: error {e!r}", flush=True)
            continue
        rows.append(row)
        save(out_dir, name, rows)
        m113.tally(counts, row.get("mode"), row["cert"])
        print(f"cert {row['instance']}: {row['cert']} {row['mode']} inv {row.get('inv')} "
              f"{row.get('type')} cadical {(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"clauses {row.get('clauses')} wall {row.get('wall_seconds')} s", flush=True)
    save(out_dir, name, rows)
    print(f"SUMMARY cert {shard} cases {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m126{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m126{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m126{shard}_cert.json")
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
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.shard, args.tools, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m126{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
