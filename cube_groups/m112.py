# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m112: m102's full sweep CNF at 1,500 s on every d = 1 case with k(T(N)) <= 4 that jobs
m110a-h, m110j and m111b-c left open (notes/a104.md, cube_groups/m112-predictions.md).

What came back on 2026-10-26 (notes/a104.md): job m111a confirmed by machine that T(N) leaves
pi(R) = (R + X_1) / X_1 invariant in 313 of the 315 cases m110a-g left open (486 of all 3,876 d = 1
cases are of that form). In the pilot m111b-c (one open case per label, 22 labels), anisotropy on
N + span(h_1..h_4) ("in4") or on N + span(h_5, h_6, h_7) ("out3") decided one case only (the
not-invariant o008_c003 t2_m092), while the sweep CNF at 600 s refuted 14 of the other 21, in 186 to
582 s, most of them above 400 s. Shards m110h and m110j left 46 and 53 cases open; all but
o010_c008 t3_m063_205 leave pi(R) invariant. Shard m110i was stopped from outside and is re-filed;
its open cases are not in this job.

So the rule of m111-predictions.md ("the sweep at 600 s on the open cases that leave pi(R)
invariant") applies, with the cap raised to 1,500 s because the pilot's UNSAT answers sat close to
600 s, and with the two open cases that do not leave pi(R) invariant included.

Parts:

    check     the grade files of m110a-h, j and m111b-c; 414 open cases, m111's 15 decided ones
              among them, 399 left, all d = 1 cases; this shard's share; which leave pi(R)
              invariant, by label
    controls  m110's three controls at "n" (60 s); each must be SAT with a verified model
    run       this shard's cases with the sweep CNF (1,500 s each), two at a time, while time
              remains
    grade     the graded checks of m112-predictions.md

Usage: python m112.py --part check|controls|run|grade --shard a..l [--sweep-seconds S]
       [--workers W] [--minutes M] [--out-dir D]
       (the grade files m110{a..h,j}_grade.json and m111{b,c}_grade.json must be in the working
       directory)
"""
import argparse
import concurrent.futures as cf
import functools
import json
import os
import time

import m100
import m102
import m103
import m104
import m106
import m110
import m111

M110_DONE = "abcdefghj"        # m110i was stopped from outside at 08:22 UTC and is re-filed
M111_RUN = "bc"
SHARDS = "abcdefghijkl"
OPEN_M110 = 414                # 315 (a-g, notes/a103.md) + 46 (h) + 53 (j)
DECIDED_M111 = 15              # 7 (m111b) + 8 (m111c)
TOTAL = OPEN_M110 - DECIDED_M111
# 399 = 12 * 33 + 3: shards a-c take 34 cases, d-l 33
SIZE = {s: 34 if s in "abc" else 33 for s in SHARDS}
N_CAP = 60.0
SWEEP_CAP = 1500.0


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


def append_row(out_dir, name, row):
    rows = m100.load(out_dir, name) or []
    rows.append(row)
    save(out_dir, name, rows)


# ---------- the cases ----------

@functools.lru_cache(maxsize=None)
def d1_cases():
    """{instance: (spec, case)} for the 3,876 d = 1 cases with k <= 4."""
    return {m102.inst_name(s, c): (s, c) for s, c in m110.sweep_cases()}


def m111_decided(src="."):
    """The cases job m111b-c decided (sorted), or None if a grade file is missing."""
    out = []
    for s in M111_RUN:
        g = m100.load(src, f"m111{s}_grade.json")
        if g is None:
            return None
        out += g["decided"]
    return sorted(out)


def open_cases(parts, decided):
    """The cases with no UNSAT answer in m110 that m111 did not decide, sorted by name."""
    done = set(decided)
    return sorted(x for x, f in m111.finals(parts).items() if f != "UNSAT" and x not in done)


def shard_of(i):
    return SHARDS[i % len(SHARDS)]


def shard_list(shard, names):
    return [x for i, x in enumerate(names) if shard_of(i) == shard]


# ---------- the parts ----------

def run_check(shard, out_dir):
    g, info = {}, {}
    parts = m111.m110_parts(M110_DONE)
    decided = m111_decided()
    g["grades_loaded"] = parts is not None and decided is not None
    parts, decided = parts or {}, decided or []
    fin = m111.finals(parts)
    g["open_414"] = sum(f != "UNSAT" for f in fin.values()) == OPEN_M110
    g["decided_15_open"] = (len(decided) == DECIDED_M111
                            and all(fin.get(x, "UNSAT") != "UNSAT" for x in decided))
    names = open_cases(parts, decided)
    g["total_399"] = len(names) == TOTAL
    cases = d1_cases()
    g["names_d1"] = all(x in cases for x in names)
    mine = shard_list(shard, names)
    g["shard_size"] = len(mine) == SIZE[shard]
    pres = {x: m111.features(*cases[x])["pres_r"] for x in names if x in cases}
    by_label = {}
    for x, p in pres.items():
        tally(by_label, x[20:], "pres_r" if p else "not")
    info.update({"shard": mine, "total": len(names), "pres_r": sum(pres.values()),
                 "not_pres_r": sorted(x for x, p in pres.items() if not p),
                 "by_label": by_label, "graded": g})
    save(out_dir, f"m112{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    short = {k: info[k] for k in ("total", "pres_r", "not_pres_r")}
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
    save(out_dir, f"m112{shard}_controls.json", {"graded": g, "rows": rows})
    print(f"SUMMARY controls {shard} all_match {all(g.values())} "
          f"{json.dumps([[r['instance'][10:], r['status'], r.get('verified')] for r in rows])}",
          flush=True)


def solve_sweep(x, cap, deadline, out_dir):
    """The sweep CNF on case x, or None if the deadline has passed (the case is skipped)."""
    if time.time() > deadline:
        return None
    spec, case = d1_cases()[x]
    row = m102.solve_one(spec, case, "sweep", cap, out_dir, "sweep")
    row["tag"] = f"{x}_sweep"
    row["inv"], row["type"] = m104.k_and_type(m103.space_of(case))
    return row


def run(shard, cap, workers, minutes, out_dir):
    start = time.time()
    name = f"m112{shard}_rows.json"
    info = m100.load(out_dir, f"m112{shard}_check.json") or {"shard": []}
    tab, skipped = {}, []
    d1_cases()                 # build the table once, before the threads start
    deadline = start + minutes * 60
    # each solve runs in its own child process (m102.solve_one), so threads are enough
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        futs = {ex.submit(solve_sweep, x, cap, deadline, out_dir): x for x in info["shard"]}
        for fut in cf.as_completed(futs):
            row = fut.result()
            if row is None:
                skipped.append(f"{futs[fut]}_sweep")
                continue
            m110.drop_child(out_dir, row)
            append_row(out_dir, name, row)
            tally(tab, "sweep", row["status"])
    save(out_dir, f"m112{shard}_skipped.json", sorted(skipped))
    print(f"SUMMARY run {shard} skipped {len(skipped)} {json.dumps(tab, sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade_rows(rows, skipped, mine):
    """(graded, out) for a shard from its rows, skipped tags and case list."""
    g, out = {}, {}
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g[f"verified_{r['tag']}"] = bool(r.get("verified"))
    ran = [r["instance"] for r in rows]
    g["all_accounted"] = sorted(ran + [t[:-len("_sweep")] for t in skipped]) == sorted(mine)
    # a model anisotropic on all of V would be a system with t = 8, dim V = 11: flag it
    out["full_models"] = sorted(r["tag"] for r in rows if r["status"] == "SAT"
                                and r.get("check", {}).get("anisotropic"))
    by_status, by_label, by_type = {}, {}, {}
    for r in rows:
        tally(by_status, "sweep", r["status"])
        tally(by_label, r["instance"][20:], r["status"])
        tally(by_type, r["type"], r["status"])
    unsat = sorted(r["instance"] for r in rows if r["status"] == "UNSAT")
    secs = sorted(r["wall_seconds"] for r in rows if r["status"] == "UNSAT")
    out.update({"by_status": by_status, "by_label": by_label, "by_type": by_type,
                "unsat": unsat, "open": sorted(set(mine) - set(unsat)),
                "skipped": sorted(skipped),
                "unsat_wall_seconds": {"min": secs[0] if secs else None,
                                       "median": secs[len(secs) // 2] if secs else None,
                                       "max": secs[-1] if secs else None}})
    return g, out


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m112{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m112{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m112{shard}_rows.json") or []
    skipped = m100.load(out_dir, f"m112{shard}_skipped.json")
    rg, out = grade_rows(rows, skipped or [], chk["shard"])
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
        save(args.out_dir, f"m112{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
