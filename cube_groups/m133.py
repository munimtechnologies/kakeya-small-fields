# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m133: the census of the d = 0 cases of (B7)_8 that have no certificate yet, at the sweep
CNF, one case at a time, each UNSAT checked by drat-trim (cube_groups/m133-predictions.md).

Why: m132 (2026-11-03) ran a stratified sample of 120 of the 1,494 uncertified d = 0 cases. All
100 cases that finished were UNSAT with drat-trim VERIFIED proofs (median CaDiCaL time 335 to
489 s per shard, max 895 s; drat-trim at most 1,185 s); none was UNKNOWN, SAT or an error; 20
were not started inside the shards' time budget. m132's decision rule then says: census of the
rest, in shards of the same form, a few shards a day.

The census: m132.remaining() (the 1,500 d = 0 cases minus the six pilot cases, sorted by name)
minus the 100 cases m132 certified (m133_done.json, copied from cube_groups/results/m132/), which
leaves 1,394. Shard k (k = 0 .. 47) takes census[k::48], so shards 0 and 1 hold 30 cases and the
others 29, and every shard is spread over the whole list. Same caps as m132: CaDiCaL 1,500 s with
an ASCII DRAT proof, drat-trim 4,000 s, no new case after 25,000 s, rows saved after each case.

Parts:

    check     the shard's cases are d = 0 cases, distinct, none certified before, tools built
    controls  m113's controls (as m131/m132)
    cert      the cases at the sweep CNF (m113.certify)
    grade     the graded checks of m133-predictions.md for this shard

Usage: python m133.py --part check|controls|cert|grade --shard K [--tools DIR] [--out-dir D]
"""
import argparse
import json
import os
import tempfile
import time

import m113
import m130
import m132

NSH = 48
MODE = "sweep"
CADICAL_CAP = 1500.0
DRAT_CAP = {"n": 1200, "sweep": 4000}
NO_START_AFTER = 25000          # seconds after the cert part starts (job limit 540 min)
PREFIX = "m133"
HERE = os.path.dirname(os.path.abspath(__file__))
DONE_FILE = os.path.join(HERE, "m133_done.json")
EXPECT_DONE = 100
EXPECT_CENSUS = 1394


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def load(out_dir, name):
    path = os.path.join(out_dir, name)
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


def fname(shard, part):
    return f"{PREFIX}s{shard:02d}_{part}.json"


def done_names():
    with open(DONE_FILE) as f:
        d = json.load(f)
    return sorted(set(d["m132a"]) | set(d["m132b"]) | set(d["m132c"]))


def census(names=None, done=None):
    """The d = 0 case names without a certificate yet, sorted."""
    names = m132.remaining() if names is None else names
    done = set(done_names() if done is None else done)
    return [x for x in names if x not in done]


def shard_cases(shard, names=None):
    return (census() if names is None else names)[shard::NSH]


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    table = m130.by_name()
    p = m132.pilot()
    done = done_names()
    rem = m132.remaining()
    cen = census()
    xs = cen[shard::NSH]
    g["d0_1500"] = len(table) == m130.EXPECT_D0
    g["pilot_6"] = len(p) == 6
    g["done_100"] = len(done) == EXPECT_DONE
    g["done_in_remaining"] = set(done) <= set(rem)
    g["census_1394"] = len(cen) == EXPECT_CENSUS
    g["shard_size"] = len(xs) == (30 if shard < 2 else 29)
    g["all_d0"] = all(x in table and table[x][0]["dmeet"] == 0 for x in xs)
    g["none_certified"] = not (set(xs) & (p | set(done)))
    g["names_match"] = all(m130.m102.inst_name(*table[x]) == x for x in xs)
    g["tools"] = all(os.access(os.path.join(tools, t), os.X_OK) for t in ("cadical", "drat-trim"))
    classes = sorted({table[x][0]["name"] for x in xs})
    save(out_dir, fname(shard, "check"), {"shard": shard, "cases": xs, "mode": MODE,
                                          "classes": classes,
                                          "caps": {"cadical": CADICAL_CAP, "drat": DRAT_CAP},
                                          "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} cases {len(xs)} "
          f"classes {len(classes)} first {xs[:2]}", flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, fname(shard, "controls")))


def run_cert(shard, tools, out_dir):
    m113.CADICAL_CAP = CADICAL_CAP
    m113.DRAT_CAP = dict(DRAT_CAP)
    start = time.time()
    table = m130.by_name()
    rows = []
    for x in shard_cases(shard):
        if time.time() - start > NO_START_AFTER:
            rows.append({"instance": x, "mode": MODE, "cert": "NOT_STARTED"})
            continue
        spec, case = table[x]
        try:
            with tempfile.TemporaryDirectory() as tmp:
                row = m113.certify(tools, spec, case, MODE, tmp)
        except Exception as e:  # keep the part's exit code 0; the grade sees the row
            print(f"cert {x}: error {e!r}", flush=True)
            row = {"instance": x, "name": spec["name"], "mode": MODE, "cert": "ERROR",
                   "error": repr(e)}
        row.setdefault("instance", x)
        rows.append(row)
        save(out_dir, fname(shard, "cert"), rows)
        print(f"cert {x}: {row.get('cert')} cadical {(row.get('cadical') or {}).get('status')} "
              f"{(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"elapsed {round(time.time() - start)} s", flush=True)
    save(out_dir, fname(shard, "cert"), rows)
    print(f"SUMMARY cert {shard} rows {len(rows)} seconds {round(time.time() - start)}", flush=True)


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = load(out_dir, fname(shard, part))
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in (st.get("graded") or {}).items()})
    rows = load(out_dir, fname(shard, "cert"))
    g["cert_ran"] = rows is not None
    rows = rows or []
    done = [r for r in rows if r.get("cert") not in ("NOT_STARTED", None)]
    status = [(r.get("cadical") or {}).get("status") for r in done]
    secs = [(r.get("cadical") or {}).get("seconds") for r in done
            if (r.get("cadical") or {}).get("status") == "UNSAT"]
    secs = [s for s in secs if isinstance(s, (int, float))]
    counts = {}
    for r in done:
        counts[r.get("cert")] = counts.get(r.get("cert"), 0) + 1
    g["no_error"] = not any(r.get("cert") in ("ERROR", "MISSING") for r in done)
    g["all_verified"] = bool(done) and all(r.get("cert") == "VERIFIED" for r in done)
    g["no_unknown"] = "UNKNOWN" not in status
    g["no_sat"] = "SAT" not in status
    g["no_solution"] = not any(m132.is_solution(r) for r in done)
    g["all_started"] = len(done) == len(rows) and bool(rows)
    out = {"graded": g, "shard": shard, "mode": MODE, "done": len(done), "rows": len(rows),
           "counts": counts, "cadical_unsat_seconds": {"median": m132.median(secs),
                                                       "max": max(secs) if secs else None,
                                                       "n": len(secs)},
           "drat_seconds_max": max([(r.get("drat") or {}).get("seconds") or 0 for r in done] or [0]),
           "proof_bytes_max": max([r.get("proof_bytes") or 0 for r in done] or [0]),
           "verified": sorted(r.get("instance") for r in done if r.get("cert") == "VERIFIED"),
           "open": sorted(r.get("instance") for r in rows if r.get("cert") != "VERIFIED"),
           "solutions": [r.get("instance") for r in done if m132.is_solution(r)]}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    if not 0 <= args.shard < NSH:
        raise SystemExit(f"shard must be 0 .. {NSH - 1}")
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.shard, args.tools, args.out_dir)
    else:
        try:
            out = grade(args.shard, args.out_dir)
        except Exception as e:  # a grading crash must not hide the logs
            out = {"graded": {"grade_ran": False}, "error": repr(e)}
        save(args.out_dir, fname(args.shard, "grade"), out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: out.get(k) for k in ("done", "counts", "cadical_unsat_seconds", "drat_seconds_max",
                                         "proof_bytes_max", "solutions")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
