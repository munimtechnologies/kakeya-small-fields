# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m122: DRAT certificates for the 53 d = 1 refutations that m120's finished shards did not
certify: the 38 cases that m120b, m120c and m120d skipped for time, and the 15 cases that m111b and
m111c refuted, which m120's case list left out (notes/a110.md, cube_groups/m122-predictions.md).

What came back on 2026-10-28 (notes/a110.md): m120b, c and d VERIFIED 43 sweep certificates, none
NOT_VERIFIED, no SAT, but skipped 38 cases when their 190 minutes ran out; m120a was stopped from
outside. Their check part found 420 cases, not 435: m120 counted 438 sweep UNSATs, but the grade
files of m112a-l, m114a-f, m116a-b and m119 hold 423. The other 15 of the 3,846 UNSAT answers were
given by m111b (7) and m111c (8), at "in4", "out3" or m102's sweep CNF at 600 s, before m112 ran.
None of them has a certificate yet. Every CNF of m111 is implied by the sweep CNF (each asks
sigma(h) != 0 on a subset of V), so the sweep CNF is UNSAT for these 15 too, and each is certified
here with the sweep CNF, as m120 does it (CaDiCaL at 1,800 s, drat-trim at 3,000 s).

Parts:

    check     the grade files: m111b-c decided 15; m120b-d skipped 38; the two disjoint, all d = 1
              cases, none among the 3,408 that m110a-j decided, none among m120b-d's VERIFIED;
              this shard's share (by index mod 3 in name order); both programs
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      this shard's cases, two at a time; no case starts after --minutes
    grade     the graded checks of m122-predictions.md (m113.grade_rows)

Usage: python m122.py --part check|controls|cert|grade --shard a|b|c [--tools DIR] [--workers W]
       [--minutes M] [--out-dir D]
       (the grade files of m110a-j, m111b-c and m120b-d in the working directory)
"""
import argparse
import concurrent.futures as cf
import json
import os
import time

import m100
import m111
import m113

SHARDS = "abc"
M111_SOURCES = ("m111b", "m111c")
M120_DONE = ("m120b", "m120c", "m120d")
N_M111 = 15                    # 7 (m111b) + 8 (m111c)
N_SKIPPED = 38                 # 13 (m120b) + 10 (m120c) + 15 (m120d)
N_M110 = 3408
TOTAL = 53
# 53 = 3 * 17 + 2: shards a, b take 18 cases, c 17
SIZE = {"a": 18, "b": 18, "c": 17}
MODE = "sweep"
CADICAL_CAP = 1800.0
DRAT_CAP = {"n": 1200, "sweep": 3000}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def m111_decided(src="."):
    """The cases m111b-c refuted, or None if a grade file is missing."""
    out = set()
    for name in M111_SOURCES:
        g = m100.load(src, f"{name}_grade.json")
        if g is None:
            return None
        out |= set(g["decided"])
    return out


def m120_rows(src="."):
    """{instance: cert} over m120b-d's grade files, or None if one is missing."""
    out = {}
    for name in M120_DONE:
        g = m100.load(src, f"{name}_grade.json")
        if g is None:
            return None
        out.update({x: row[0] for x, row in g["rows"].items()})
    return out


def m120_skipped(src="."):
    rows = m120_rows(src)
    return None if rows is None else {x for x, c in rows.items() if c == "SKIPPED"}


def cases(src="."):
    """The cases to certify, sorted by name, or None if a grade file is missing."""
    a, b = m111_decided(src), m120_skipped(src)
    if a is None or b is None:
        return None
    return sorted(a | b)


def shard_list(shard, names):
    return [[x, MODE] for i, x in enumerate(names) if SHARDS[i % len(SHARDS)] == shard]


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    a, rows = m111_decided(), m120_rows()
    parts = m111.m110_parts("abcdefghij")
    g["grades_loaded"] = a is not None and rows is not None and parts is not None
    a, rows = a or set(), rows or {}
    b = {x for x, c in rows.items() if c == "SKIPPED"}
    g["m111_15"] = len(a) == N_M111
    g["skipped_38"] = len(b) == N_SKIPPED
    g["disjoint"] = not a & b
    g["not_in_m120_verified"] = not a & {x for x, c in rows.items() if c == "VERIFIED"}
    names = sorted(a | b)
    g["total_53"] = len(names) == TOTAL
    d1 = m113.d1_cases()
    g["names_d1"] = all(x in d1 for x in names)
    decided = {x for x, _ in m113.decided(parts or {})}
    g["m110_3408"] = len(decided) == N_M110
    g["disjoint_from_m110"] = not set(names) & decided
    mine = shard_list(shard, names)
    g["shard_size"] = len(mine) == SIZE[shard]
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"m122{shard}_check.json", {"shard": mine, "total": len(names), "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'total': len(names), 'shard': len(mine)}, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"m122{shard}_controls.json"))


def run_cert(shard, tools, workers, minutes, out_dir):
    m113.CADICAL_CAP, m113.DRAT_CAP = CADICAL_CAP, DRAT_CAP
    start = time.time()
    name = f"m122{shard}_cert.json"
    info = m100.load(out_dir, f"m122{shard}_check.json") or {"shard": []}
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
        st = m100.load(out_dir, f"m122{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m122{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m122{shard}_cert.json")
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
        save(args.out_dir, f"m122{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
