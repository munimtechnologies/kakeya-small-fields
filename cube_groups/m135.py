# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m135: late mop-up of the d = 0 census of (B7)_8 (cube_groups/m135-predictions.md).
Made with AI agents working in MV2's name.

m134's mop-up covers m133 shards 0 .. 21 only. m135 does the same for the cases of later census
jobs that have no VERIFIED row in their published cert files: cases that did not start before
the job's start limit, cases whose job was stopped from outside, and cases that ended UNKNOWN,
DRAT_STOPPED or ERROR. Each SCOPE is a fixed, pre-registered set of published cert files with the
counts expected in them; the list is rebuilt from those files at run time, hard cases first, and
split into strided chunks. The certification is unchanged (m113.certify at the sweep CNF), with
m134's mop-up caps (CaDiCaL 4,000 s, drat-trim 6,000 s, 10,000 s for a DRAT_STOPPED case) and no
new case after 12,000 s.

Scope "a" (a141): m133 shards 22, 23 and 24 and m134 part k25p0 (shard 25, third 0).
Scope "b" (a143): m134 parts k25p1 and k25p2 (shard 25, thirds 1 and 2).

Usage:
    python m135.py --step check|controls|cert|grade --scope a|b --chunk C [--tools DIR] [--out-dir D]
"""
import argparse
import json
import os
import tempfile
import time

import m113
import m130
import m132
import m133
import m134

PREFIX = "m135"
MODE = "sweep"
RESULTS133 = m134.RESULTS
RESULTS134 = ("https://raw.githubusercontent.com/munimtechnologies/kakeya-small-fields/main/"
              "cube_groups/results/m134/")

SCOPES = {
    "a": {
        "m133_shards": [22, 23, 24],
        "parts": [(25, 0)],
        "expect_verified": 75,      # 23 + 29 + 18 (shards 22, 23, 24) + 5 (k25p0), a139 and a141
        "expect_mopup": 22,         # 6 + 0 + 11 + 5
        "expect_hard": 0,
        "nchunk": 3,
    },
    "b": {
        "m133_shards": [],
        "parts": [(25, 1), (25, 2)],
        "expect_verified": 14,      # 8 (k25p1, a142) + 6 (k25p2, a143)
        "expect_mopup": 5,          # 2 + 3
        "expect_hard": 3,           # k25p1: 1 UNKNOWN + 1 DRAT_STOPPED; k25p2: 1 UNKNOWN
        "nchunk": 3,                # 2, 2 and 1 cases: no chunk holds two worst-case hard cases
    },
}

HARD = m134.HARD
MOP_CADICAL = m134.MOP_CADICAL
MOP_DRAT = m134.MOP_DRAT
MOP_DRAT_STOPPED = m134.MOP_DRAT_STOPPED
NO_START_AFTER = m134.NO_START_AFTER


def tag(scope, chunk):
    return f"{PREFIX}{scope}{chunk:02d}"


def fname(t, step):
    return f"{t}_{step}.json"


def part_cases(shard, third, cen):
    return m133.shard_cases(shard, cen)[third::m134.NPART]


def sources(scope, cen):
    """(label, url, cases) for every cert file of the scope."""
    sc = SCOPES[scope]
    out = []
    for k in sc["m133_shards"]:
        out.append((f"m133s{k:02d}", RESULTS133 + m133.fname(k, "cert"), m133.shard_cases(k, cen)))
    for k, p in sc["parts"]:
        t = m134.tag("part", shard=k, third=p)
        out.append((t, RESULTS134 + m134.fname(t, "cert"), part_cases(k, p, cen)))
    return out


def collect(srcs, get):
    """Status of every case of the sources that is not VERIFIED in its published cert file. A case
    with no row (not started, or its job was stopped from outside) is 'MISSING'."""
    status = {}
    verified = 0
    missing_files = []
    for label, url, cases in srcs:
        try:
            rows = get(url)
        except Exception as e:
            print(f"{label}: no published cert file ({e!r})", flush=True)
            missing_files.append(label)
            rows = []
        by = {r.get("instance"): r.get("cert") for r in rows}
        for x in cases:
            s = by.get(x) or "MISSING"
            if s == "VERIFIED":
                verified += 1
            else:
                status[x] = s
    return status, verified, missing_files


def run_check(args, out_dir, get=m134.fetch_json):
    table = m130.by_name()
    cen = m133.census()
    t = tag(args.scope, args.chunk)
    g = {"census_1394": len(cen) == m133.EXPECT_CENSUS, "scope_known": args.scope in SCOPES}
    info = {"tag": t, "scope": args.scope, "mode": MODE}
    xs = []
    if g["scope_known"]:
        sc = SCOPES[args.scope]
        srcs = sources(args.scope, cen)
        status, verified, missing = collect(srcs, get)
        hard, fresh = m134.order(status)
        ordered = hard + fresh
        xs = m134.chunk_of(ordered, args.chunk, sc["nchunk"])
        g["chunk_in_range"] = 0 <= args.chunk < sc["nchunk"]
        g["files_all_published"] = not missing
        g["verified_expected"] = verified == sc["expect_verified"]
        g["mopup_expected"] = len(ordered) == sc["expect_mopup"]
        g["hard_expected"] = len(hard) == sc["expect_hard"]
        info.update({"chunk": args.chunk, "nchunk": sc["nchunk"],
                     "sources": [s[0] for s in srcs], "verified_published": verified,
                     "missing_files": missing, "mopup_total": len(ordered),
                     "hard_total": len(hard), "status": {x: status[x] for x in xs},
                     "all_mopup": ordered,
                     "caps": {"cadical": MOP_CADICAL, "drat": MOP_DRAT,
                              "drat_if_drat_stopped": MOP_DRAT_STOPPED,
                              "no_start_after": NO_START_AFTER}})
    m134.common_gates(g, xs, table)
    g["tools"] = m134.tools_ok(args.tools)
    info["cases"] = xs
    info["graded"] = g
    m134.save(out_dir, fname(t, "check"), info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {t} all_match {not bad} graded {len(g)} failed {bad} cases {len(xs)} "
          f"first {xs[:2]}", flush=True)


def run_controls(args, out_dir):
    t = tag(args.scope, args.chunk)
    m113.run_controls("a", args.tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, fname(t, "controls")))


def run_cert(args, out_dir):
    t = tag(args.scope, args.chunk)
    chk = m134.load(out_dir, fname(t, "check"))
    if chk is None or not all((chk.get("graded") or {}).values()):
        m134.save(out_dir, fname(t, "cert"), [])
        print(f"SUMMARY cert {t} refused: the check step did not pass", flush=True)
        return
    status = chk.get("status") or {}
    start = time.time()
    table = m130.by_name()
    rows = []
    for x in chk["cases"]:
        if time.time() - start > NO_START_AFTER:
            rows.append({"instance": x, "mode": MODE, "cert": "NOT_STARTED"})
            continue
        m113.CADICAL_CAP = MOP_CADICAL
        drat = MOP_DRAT_STOPPED if status.get(x) == "DRAT_STOPPED" else MOP_DRAT
        m113.DRAT_CAP = {"n": m133.DRAT_CAP["n"], "sweep": drat}
        spec, case = table[x]
        try:
            with tempfile.TemporaryDirectory() as tmp:
                row = m113.certify(args.tools, spec, case, MODE, tmp)
        except Exception as e:  # keep the step's exit code 0; the grade sees the row
            print(f"cert {x}: error {e!r}", flush=True)
            row = {"instance": x, "name": spec["name"], "mode": MODE, "cert": "ERROR",
                   "error": repr(e)}
        row.setdefault("instance", x)
        row["caps"] = {"cadical": m113.CADICAL_CAP, "drat": drat}
        if x in status:
            row["before"] = status[x]
        rows.append(row)
        m134.save(out_dir, fname(t, "cert"), rows)
        print(f"cert {x}: {row.get('cert')} cadical {(row.get('cadical') or {}).get('status')} "
              f"{(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"elapsed {round(time.time() - start)} s", flush=True)
    m134.save(out_dir, fname(t, "cert"), rows)
    print(f"SUMMARY cert {t} rows {len(rows)} seconds {round(time.time() - start)}", flush=True)


def grade(args, out_dir):
    t = tag(args.scope, args.chunk)
    g = {}
    for step in ("check", "controls"):
        st = m134.load(out_dir, fname(t, step))
        if st is None:
            g[step + "_ran"] = False
        else:
            g.update({step + "_" + k: v for k, v in (st.get("graded") or {}).items()})
    rows = m134.load(out_dir, fname(t, "cert"))
    g["cert_ran"] = bool(rows)
    rows = rows or []
    done = [r for r in rows if r.get("cert") not in ("NOT_STARTED", None)]
    status = [(r.get("cadical") or {}).get("status") for r in done]
    secs = [(r.get("cadical") or {}).get("seconds") for r in done
            if (r.get("cadical") or {}).get("status") == "UNSAT"]
    secs = [s for s in secs if isinstance(s, (int, float))]
    counts = {}
    for r in done:
        counts[r.get("cert")] = counts.get(r.get("cert"), 0) + 1
    hard_rows = [r for r in done if r.get("before") in HARD]
    fresh_rows = [r for r in done if r.get("before") not in HARD]
    g["no_error"] = not any(r.get("cert") in ("ERROR", "MISSING") for r in done)
    g["no_sat"] = "SAT" not in status
    g["no_solution"] = not any(m132.is_solution(r) for r in done)
    g["all_started"] = len(done) == len(rows) and bool(rows)
    g["fresh_all_verified"] = all(r.get("cert") == "VERIFIED" for r in fresh_rows)
    return {"graded": g, "tag": t, "scope": args.scope, "mode": MODE, "done": len(done),
            "rows": len(rows), "counts": counts,
            "hard": {r.get("instance"): {"before": r.get("before"), "now": r.get("cert")}
                     for r in hard_rows},
            "fresh_done": len(fresh_rows),
            "fresh_verified": sum(1 for r in fresh_rows if r.get("cert") == "VERIFIED"),
            "cadical_unsat_seconds": {"median": m132.median(secs),
                                      "max": max(secs) if secs else None, "n": len(secs)},
            "drat_seconds_max": max([(r.get("drat") or {}).get("seconds") or 0
                                     for r in done] or [0]),
            "proof_bytes_max": max([r.get("proof_bytes") or 0 for r in done] or [0]),
            "verified": sorted(r.get("instance") for r in done if r.get("cert") == "VERIFIED"),
            "open": sorted(r.get("instance") for r in rows if r.get("cert") != "VERIFIED"),
            "solutions": [r.get("instance") for r in done if m132.is_solution(r)]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--step", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--scope", default="a")
    ap.add_argument("--chunk", type=int, default=0)
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.step == "check":
        run_check(args, args.out_dir)
    elif args.step == "controls":
        run_controls(args, args.out_dir)
    elif args.step == "cert":
        run_cert(args, args.out_dir)
    else:
        t = tag(args.scope, args.chunk)
        try:
            out = grade(args, args.out_dir)
        except Exception as e:  # a grading crash must not hide the logs
            out = {"graded": {"grade_ran": False}, "error": repr(e)}
        m134.save(args.out_dir, fname(t, "grade"), out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: out.get(k) for k in ("done", "counts", "hard", "fresh_done", "fresh_verified",
                                         "cadical_unsat_seconds", "drat_seconds_max",
                                         "proof_bytes_max", "solutions")}
        print(f"SUMMARY grade {t} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
