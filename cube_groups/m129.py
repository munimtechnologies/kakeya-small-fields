# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m129: the 30 d = 1 cases of (B7)_8 that no solver has refuted yet (notes/a122.md,
cube_groups/m129-predictions.md), each alone, with long limits and a DRAT certificate.

Where they come from: m128 recounted every published grade file against m113's 3,876 d = 1 cases
(2026-10-31): 3,846 have a VERIFIED row, and these 30 have no row in any grade file and no UNSAT
answer from m110a-j. They were open at 1,500 s in the sweeps (notes/a109.md), several cases sharing a
job; the cube pilot m121 left two of them open at 600 s per cube, and the adaptive pilot m124 was
stopped from outside before it reached them. Jobs m126 and m127 showed that a case alone runs 2 to 3
times faster than beside others (the former UNKNOWN cases needed 504 to 1,199 s alone).

So each of 15 shards a-o takes 2 cases, items k and k + 15 of the 30 in name order (so every shard
mixes early and late names), and runs them one after the other: CaDiCaL at 4,800 s with an ASCII
DRAT proof, drat-trim at 7,200 s; the second case starts only if 7,000 s have not yet passed (else
it is SKIPPED, not failed). Shards a-h are the pilot; i-o follow by the rule in m129-predictions.md.

Parts:

    check     m128_count.json: its 30 missing cases are the 30 below, all d = 1 cases, none among
              the 3,408 that m110a-j decided; this shard's 2 cases; both programs
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      this shard's cases, one at a time
    grade     the graded checks (m113.grade_rows)

Usage: python m129.py --part check|controls|cert|grade --shard a..o [--tools DIR] [--out-dir D]
       (m128_count.json and the grade files of m110a-j in the working directory)
"""
import argparse
import json
import os
import time

import m100
import m111
import m113

OPEN = [
    "r3b_t8_B7_o007_c003_t2_m011", "r3b_t8_B7_o007_c003_t2_m026",
    "r3b_t8_B7_o007_c004_t2_m011", "r3b_t8_B7_o007_c004_t2_m026",
    "r3b_t8_B7_o007_c004_t3_m011_017", "r3b_t8_B7_o007_c006_t3_m031_036",
    "r3b_t8_B7_o007_c007_t2_m031", "r3b_t8_B7_o008_c000_t2_m011",
    "r3b_t8_B7_o008_c001_t2_m011", "r3b_t8_B7_o008_c001_t2_m026",
    "r3b_t8_B7_o008_c001_t3_m011_017", "r3b_t8_B7_o008_c003_t3_m031_036",
    "r3b_t8_B7_o009_c001_t2_m026", "r3b_t8_B7_o009_c001_t2_m059",
    "r3b_t8_B7_o009_c002_t2_m011", "r3b_t8_B7_o009_c002_t2_m031",
    "r3b_t8_B7_o009_c002_t2_m038", "r3b_t8_B7_o009_c003_t2_m011",
    "r3b_t8_B7_o009_c003_t2_m030", "r3b_t8_B7_o009_c003_t2_m031",
    "r3b_t8_B7_o009_c003_t3_m011_017", "r3b_t8_B7_o009_c004_t2_m026",
    "r3b_t8_B7_o009_c007_t2_m031", "r3b_t8_B7_o010_c001_t2_m011",
    "r3b_t8_B7_o010_c001_t2_m026", "r3b_t8_B7_o010_c001_t3_m011_017",
    "r3b_t8_B7_o010_c006_t2_m031", "r3b_t8_B7_o010_c007_t2_m011",
    "r3b_t8_B7_o010_c008_t2_m031", "r3b_t8_B7_o010_c008_t2_m059",
]
N_OPEN = 30
N_M110 = 3408
SHARDS = "abcdefghijklmno"
MODE = "sweep"
CADICAL_CAP = 4800.0
DRAT_CAP = 7200
SECOND_START_BY = 7000          # seconds after the cert part starts


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def shard_list(shard, items):
    """Items k and k + 15 for shard number k."""
    i = SHARDS.index(shard)
    half = len(SHARDS)
    return [items[i], items[i + half]] if i + half < len(items) else items[i:i + 1]


def m128_missing(src="."):
    """The sorted names m128 reported without a VERIFIED row, or None."""
    c = m100.load(src, "m128_count.json")
    return None if c is None else sorted(c.get("missing", {}))


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    missing = m128_missing()
    parts = m111.m110_parts("abcdefghij")
    g["files_loaded"] = missing is not None and parts is not None
    g["open_30"] = len(OPEN) == N_OPEN == len(set(OPEN)) and OPEN == sorted(OPEN)
    g["matches_m128"] = missing == OPEN
    d1 = m113.d1_cases()
    g["names_d1"] = all(x in d1 for x in OPEN)
    decided = {x for x, _ in m113.decided(parts or {})}
    g["m110_3408"] = len(decided) == N_M110
    g["disjoint_from_m110"] = not set(OPEN) & decided
    mine = [[x, MODE] for x in shard_list(shard, OPEN)]
    g["shard_size"] = len(mine) == 2
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"m129{shard}_check.json", {"shard": mine, "open": OPEN, "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'open': len(OPEN), 'shard': mine}, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"m129{shard}_controls.json"))


def run_cert(shard, tools, out_dir):
    m113.CADICAL_CAP = CADICAL_CAP
    m113.DRAT_CAP = {"n": 1200, "sweep": DRAT_CAP}
    start = time.time()
    name = f"m129{shard}_cert.json"
    info = m100.load(out_dir, f"m129{shard}_check.json") or {"shard": []}
    rows, counts = [], {}
    for x, mode in info["shard"]:
        try:
            row = m113.certify_item(tools, x, mode, start + SECOND_START_BY)
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
        st = m100.load(out_dir, f"m129{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m129{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m129{shard}_cert.json")
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
        save(args.out_dir, f"m129{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
