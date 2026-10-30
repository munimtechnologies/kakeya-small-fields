# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m127: DRAT certificates for the 16 d = 1 refutations that the sweep shards m120m, m120n and
m120p left without a checked certificate (notes/a118.md, a120.md; cube_groups/m127-predictions.md):
15 SKIPPED because the shard's time budget ran out before they started, and 1 UNKNOWN at CaDiCaL's
1,800 s limit with three cases sharing the job (r3b_t8_B7_o009_c006_t2_m031, m120p).

m126 showed that a case alone runs far faster than three at a time (the three former UNKNOWN cases
needed 504 to 857 s alone). So each of the 8 shards a-h takes 2 cases in name order and runs them
one after the other, never side by side: CaDiCaL at 3,600 s and drat-trim at 5,400 s per case; the
second case starts only if 9,000 s have not yet passed (else it is SKIPPED, not failed).

Parts:

    check     the grade files of m120m, m120n and m120p: 16 SKIPPED or UNKNOWN rows, all d = 1 cases,
              none VERIFIED there and none among the 3,408 that m110a-j decided; this shard's 2
              cases; both programs
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      this shard's cases, one at a time
    grade     the graded checks of m127-predictions.md (m113.grade_rows)

Usage: python m127.py --part check|controls|cert|grade --shard a..h [--tools DIR] [--out-dir D]
       (the grade files of m110a-j and m120m, m120n, m120p in the working directory)
"""
import argparse
import json
import os
import time

import m100
import m111
import m113

SOURCES = ("m120m", "m120n", "m120p")
OPEN = ("SKIPPED", "UNKNOWN")
N_OPEN = 16                     # m120m 3, m120n 5, m120p 7 SKIPPED + 1 UNKNOWN
N_M110 = 3408
SHARDS = "abcdefgh"
PER_SHARD = 2
CADICAL_CAP = 3600.0
DRAT_CAP = 5400
SECOND_START_BY = 9000          # seconds after the cert part starts


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def cases(src="."):
    """[[name, mode], ...] of the SKIPPED or UNKNOWN rows, sorted by name, or None if a grade file
    is missing."""
    found = {}
    for name in SOURCES:
        g = m100.load(src, f"{name}_grade.json")
        if g is None:
            return None
        for x, row in g["rows"].items():
            if row[0] in OPEN:
                found[x] = row[1] or "sweep"
    return [[x, found[x]] for x in sorted(found)]


def verified(src="."):
    """Names with a VERIFIED row in any of the source grade files."""
    out = set()
    for name in SOURCES:
        g = m100.load(src, f"{name}_grade.json") or {"rows": {}}
        out |= {x for x, row in g["rows"].items() if row[0] == "VERIFIED"}
    return out


def shard_list(shard, items):
    i = SHARDS.index(shard)
    return items[PER_SHARD * i:PER_SHARD * (i + 1)]


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    items = cases()
    parts = m111.m110_parts("abcdefghij")
    g["grades_loaded"] = items is not None and parts is not None
    items = items or []
    names = [x for x, _ in items]
    g["open_16"] = len(items) == N_OPEN
    g["modes_sweep"] = all(m == "sweep" for _, m in items)
    g["disjoint_from_verified"] = not set(names) & verified()
    d1 = m113.d1_cases()
    g["names_d1"] = all(x in d1 for x in names)
    decided = {x for x, _ in m113.decided(parts or {})}
    g["m110_3408"] = len(decided) == N_M110
    g["disjoint_from_m110"] = not set(names) & decided
    mine = shard_list(shard, items)
    g["shard_size"] = len(mine) == PER_SHARD
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"m127{shard}_check.json", {"shard": mine, "open": items, "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'open': len(items), 'shard': mine}, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"m127{shard}_controls.json"))


def run_cert(shard, tools, out_dir):
    m113.CADICAL_CAP = CADICAL_CAP
    m113.DRAT_CAP = {"n": 1200, "sweep": DRAT_CAP}
    start = time.time()
    name = f"m127{shard}_cert.json"
    info = m100.load(out_dir, f"m127{shard}_check.json") or {"shard": []}
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
        st = m100.load(out_dir, f"m127{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m127{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m127{shard}_cert.json")
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
        save(args.out_dir, f"m127{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
