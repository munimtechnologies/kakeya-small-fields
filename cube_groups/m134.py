# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m134: shorter census jobs for the d = 0 cases of (B7)_8 (cube_groups/m134-predictions.md).
Made with AI agents working in MV2's name.

Why: m133's shards (29 cases, about 7 hours each) have two problems. (1) Cases that do not start
inside the 25,000 s budget, or that end UNKNOWN, pile up (76 cases after shards 0 to 21, a138).
(2) Long jobs were stopped from outside three times at about 08:22 UTC (2026-11-06, -07, -08), and
they block maintenance of the shared machine. m134 runs the same certification (m113.certify,
sweep CNF, CaDiCaL with an ASCII DRAT proof, drat-trim) in shorter jobs, in two forms:

    mopup  every case of m133 shards 0 .. LAST_SHARD that has no VERIFIED row in the published
           cert files (cube_groups/results/m133/m133sKK_cert.json, read from GitHub at run time),
           hard cases (UNKNOWN, DRAT_STOPPED, ERROR) first, split into NCHUNK strided chunks;
           CaDiCaL 4,000 s, drat-trim 6,000 s (10,000 s for a DRAT_STOPPED case)
    part   one third of an m133 shard K >= FIRST_PART_SHARD (m133.shard_cases(K)[P::3]) with
           m133's caps (CaDiCaL 1,500 s, drat-trim 4,000 s)

Each job stops starting new cases after NO_START_AFTER seconds and saves its rows after every
case, as m133 does. The cert step refuses to run if the check step's gates do not all pass.

Parts:

    check     the job's cases (list rebuilt from the published files), the gates, tools built
    controls  m113's controls (as m131 to m133)
    cert      the cases at the sweep CNF
    grade     the graded checks of m134-predictions.md for this job

Usage:
    python m134.py --step check|controls|cert|grade --src mopup --chunk C [--tools DIR] [--out-dir D]
    python m134.py --step check|controls|cert|grade --src part --shard K --third P [...]
"""
import argparse
import json
import os
import tempfile
import time
import urllib.request

import m113
import m130
import m132
import m133

PREFIX = "m134"
MODE = "sweep"
RESULTS = ("https://raw.githubusercontent.com/munimtechnologies/kakeya-small-fields/main/"
           "cube_groups/results/m133/")

# mop-up of m133 shards 0 .. LAST_SHARD (published by a129 .. a138)
LAST_SHARD = 21
EXPECT_VERIFIED = 564          # VERIFIED rows of m133 shards 0 .. 21 (a138: 670 - 6 pilot - 100 m132)
EXPECT_MOPUP = 76              # 640 cases of shards 0 .. 21 minus 564
EXPECT_HARD = 6                # 5 UNKNOWN + 1 DRAT_STOPPED (a137, a138)
NCHUNK = 10
HARD = ("UNKNOWN", "DRAT_STOPPED", "ERROR")
MOP_CADICAL = 4000.0
MOP_DRAT = 6000
MOP_DRAT_STOPPED = 10000

# thirds of m133 shards that have not been filed as m133 jobs
FIRST_PART_SHARD = 25
NPART = 3
PART_CADICAL = m133.CADICAL_CAP
PART_DRAT = m133.DRAT_CAP["sweep"]

NO_START_AFTER = 12000         # seconds after the cert step starts


def tag(src, chunk=0, shard=0, third=0):
    if src == "mopup":
        return f"{PREFIX}c{chunk:02d}"
    return f"{PREFIX}k{shard:02d}p{third}"


def fname(t, step):
    return f"{t}_{step}.json"


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def load(out_dir, name):
    p = os.path.join(out_dir, name)
    if not os.path.exists(p):
        return None
    with open(p) as f:
        return json.load(f)


def fetch_json(url, tries=6):
    last = None
    for i in range(tries):
        try:
            with urllib.request.urlopen(url, timeout=120) as r:
                return json.loads(r.read().decode())
        except Exception as e:  # retried, then raised
            last = e
            print(f"fetch {url}: attempt {i + 1} failed ({e!r})", flush=True)
            time.sleep(20)
    raise last


def collect(cen, get, last=LAST_SHARD):
    """Status of every case of m133 shards 0 .. last that is not VERIFIED in the published cert
    files. A case with no row (its shard was stopped from outside) is 'MISSING'."""
    status = {}
    verified = 0
    missing_files = []
    for k in range(last + 1):
        try:
            rows = get(RESULTS + m133.fname(k, "cert"))
        except Exception as e:
            print(f"shard {k}: no published cert file ({e!r})", flush=True)
            missing_files.append(k)
            rows = []
        by = {r.get("instance"): r.get("cert") for r in rows}
        for x in m133.shard_cases(k, cen):
            s = by.get(x) or "MISSING"
            if s == "VERIFIED":
                verified += 1
            else:
                status[x] = s
    return status, verified, missing_files


def order(status):
    """Hard cases first (sorted), then the cases that never ran (sorted)."""
    hard = sorted(x for x, s in status.items() if s in HARD)
    fresh = sorted(x for x, s in status.items() if s not in HARD)
    return hard, fresh


def chunk_of(ordered, c, n=NCHUNK):
    return ordered[c::n]


def tools_ok(tools):
    return all(os.access(os.path.join(tools, t), os.X_OK) for t in ("cadical", "drat-trim"))


def common_gates(g, xs, table):
    g["d0_1500"] = len(table) == m130.EXPECT_D0
    g["nonempty"] = bool(xs)
    g["distinct"] = len(set(xs)) == len(xs)
    g["all_d0"] = all(x in table and table[x][0]["dmeet"] == 0 for x in xs)
    g["names_match"] = all(m130.m102.inst_name(*table[x]) == x for x in xs)
    pilot = m132.pilot()
    g["none_pilot_or_m132"] = not (set(xs) & (set(pilot) | set(m133.done_names())))


def run_check(args, out_dir, get=fetch_json):
    table = m130.by_name()
    cen = m133.census()
    g = {"census_1394": len(cen) == m133.EXPECT_CENSUS}
    t = tag(args.src, args.chunk, args.shard, args.third)
    info = {"src": args.src, "tag": t, "mode": MODE}
    if args.src == "mopup":
        status, verified, missing = collect(cen, get)
        hard, fresh = order(status)
        ordered = hard + fresh
        xs = chunk_of(ordered, args.chunk)
        g["chunk_in_range"] = 0 <= args.chunk < NCHUNK
        g["files_all_published"] = not missing
        g["verified_564"] = verified == EXPECT_VERIFIED
        g["mopup_76"] = len(ordered) == EXPECT_MOPUP
        g["hard_6"] = len(hard) == EXPECT_HARD
        info.update({"chunk": args.chunk, "nchunk": NCHUNK, "last_shard": LAST_SHARD,
                     "verified_published": verified, "missing_files": missing,
                     "mopup_total": len(ordered), "hard_total": len(hard),
                     "status": {x: status[x] for x in xs}, "all_mopup": ordered,
                     "caps": {"cadical": MOP_CADICAL, "drat": MOP_DRAT,
                              "drat_if_drat_stopped": MOP_DRAT_STOPPED,
                              "no_start_after": NO_START_AFTER}})
    else:
        sh = m133.shard_cases(args.shard, cen) if 0 <= args.shard < m133.NSH else []
        xs = sh[args.third::NPART]
        g["shard_in_range"] = FIRST_PART_SHARD <= args.shard < m133.NSH
        g["third_in_range"] = 0 <= args.third < NPART
        g["shard_size_29"] = len(sh) == 29
        info.update({"shard": args.shard, "third": args.third,
                     "caps": {"cadical": PART_CADICAL, "drat": PART_DRAT,
                              "no_start_after": NO_START_AFTER}})
    common_gates(g, xs, table)
    g["tools"] = tools_ok(args.tools)
    info["cases"] = xs
    info["graded"] = g
    save(out_dir, fname(t, "check"), info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {t} all_match {not bad} graded {len(g)} failed {bad} cases {len(xs)} "
          f"first {xs[:2]}", flush=True)


def run_controls(args, out_dir):
    t = tag(args.src, args.chunk, args.shard, args.third)
    m113.run_controls("a", args.tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, fname(t, "controls")))


def run_cert(args, out_dir):
    t = tag(args.src, args.chunk, args.shard, args.third)
    chk = load(out_dir, fname(t, "check"))
    if chk is None or not all((chk.get("graded") or {}).values()):
        save(out_dir, fname(t, "cert"), [])
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
        if args.src == "mopup":
            m113.CADICAL_CAP = MOP_CADICAL
            drat = MOP_DRAT_STOPPED if status.get(x) == "DRAT_STOPPED" else MOP_DRAT
        else:
            m113.CADICAL_CAP = PART_CADICAL
            drat = PART_DRAT
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
        save(out_dir, fname(t, "cert"), rows)
        print(f"cert {x}: {row.get('cert')} cadical {(row.get('cadical') or {}).get('status')} "
              f"{(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"elapsed {round(time.time() - start)} s", flush=True)
    save(out_dir, fname(t, "cert"), rows)
    print(f"SUMMARY cert {t} rows {len(rows)} seconds {round(time.time() - start)}", flush=True)


def grade(args, out_dir):
    t = tag(args.src, args.chunk, args.shard, args.third)
    g = {}
    for step in ("check", "controls"):
        st = load(out_dir, fname(t, step))
        if st is None:
            g[step + "_ran"] = False
        else:
            g.update({step + "_" + k: v for k, v in (st.get("graded") or {}).items()})
    rows = load(out_dir, fname(t, "cert"))
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
    out = {"graded": g, "tag": t, "src": args.src, "mode": MODE, "done": len(done),
           "rows": len(rows), "counts": counts,
           "hard": {r.get("instance"): {"before": r.get("before"), "now": r.get("cert")}
                    for r in hard_rows},
           "fresh_done": len(fresh_rows),
           "fresh_verified": sum(1 for r in fresh_rows if r.get("cert") == "VERIFIED"),
           "cadical_unsat_seconds": {"median": m132.median(secs),
                                     "max": max(secs) if secs else None, "n": len(secs)},
           "drat_seconds_max": max([(r.get("drat") or {}).get("seconds") or 0 for r in done] or [0]),
           "proof_bytes_max": max([r.get("proof_bytes") or 0 for r in done] or [0]),
           "verified": sorted(r.get("instance") for r in done if r.get("cert") == "VERIFIED"),
           "open": sorted(r.get("instance") for r in rows if r.get("cert") != "VERIFIED"),
           "solutions": [r.get("instance") for r in done if m132.is_solution(r)]}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--step", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--src", choices=["mopup", "part"], default="mopup")
    ap.add_argument("--chunk", type=int, default=0)
    ap.add_argument("--shard", type=int, default=FIRST_PART_SHARD)
    ap.add_argument("--third", type=int, default=0)
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
        t = tag(args.src, args.chunk, args.shard, args.third)
        try:
            out = grade(args, args.out_dir)
        except Exception as e:  # a grading crash must not hide the logs
            out = {"graded": {"grade_ran": False}, "error": repr(e)}
        save(args.out_dir, fname(t, "grade"), out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: out.get(k) for k in ("done", "counts", "hard", "fresh_done", "fresh_verified",
                                         "cadical_unsat_seconds", "drat_seconds_max",
                                         "proof_bytes_max", "solutions")}
        print(f"SUMMARY grade {t} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
