# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m132: a stratified sample of 120 of the 1,494 d = 0 cases of (B7)_8 not yet certified, at the
sweep CNF, one case at a time, each UNSAT checked by drat-trim (cube_groups/m132-predictions.md).

Why: m131 (2026-11-02) refuted all three remaining pilot cases at the sweep CNF with drat-trim
VERIFIED proofs (CaDiCaL 115, 397, 498 s; drat-trim 106, 675, 502 s), including the case whose "n"
model was spurious and the two that were UNKNOWN at "n" after 600 s. So the sweep CNF, not "n", is
the setting for d = 0. Before a census of all 1,494 cases this sample measures the time per case
and whether any case is SAT or UNKNOWN at a fixed cap.

The sample: the 1,500 d = 0 cases (m130.by_name) sorted by name, minus m130's six pilot cases (all
six now certified: three in m130 at "n", three in m131 at sweep), then 120 names evenly spaced
(index floor(k * 1494 / 120), k = 0 .. 119); shard a takes k = 0, 3, 6, ..., b takes k = 1, 4, ...,
c takes k = 2, 5, .... Each shard runs its 40 cases in order and starts no new case after
NO_START_AFTER seconds, so the job ends inside its time limit; rows are saved after every case.

Parts:

    check     the 40 cases of the shard are d = 0 cases, distinct, none a pilot case, tools built
    controls  m113's controls (as m131)
    cert      the cases at the sweep CNF (m113.certify), CaDiCaL 1,500 s, drat-trim 4,000 s
    grade     the graded checks of m132-predictions.md for this shard

Usage: python m132.py --part check|controls|cert|grade --shard a|b|c [--tools DIR] [--out-dir D]
"""
import argparse
import json
import os
import tempfile
import time

import m113
import m130

SHARDS = ("a", "b", "c")
SAMPLE = 120
MODE = "sweep"
CADICAL_CAP = 1500.0
DRAT_CAP = {"n": 1200, "sweep": 4000}
NO_START_AFTER = 25000          # seconds after the cert part starts (job limit 540 min)
PREFIX = "m132"
# m131's three cases (certified at sweep 2026-11-02); they must be among m130's six pilot cases
M131_CASES = ("r3b_t8_B7_o012_c003_t2_m204", "r3b_t8_B7_o012_c002_t2_m085",
              "r3b_t8_B7_o012_c005_t2_m170")


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
    return f"{PREFIX}{shard}_{part}.json"


def pilot():
    return set(m130.pilot_names(list(m130.by_name())))


def remaining():
    """The d = 0 case names without a certificate yet, sorted."""
    p = pilot()
    return sorted(x for x in m130.by_name() if x not in p)


def sample(names=None, n=SAMPLE):
    names = remaining() if names is None else names
    return [names[(k * len(names)) // n] for k in range(n)]


def shard_cases(shard, names=None):
    s = sample(names)
    i = SHARDS.index(shard)
    return [x for k, x in enumerate(s) if k % len(SHARDS) == i]


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    table = m130.by_name()
    p = pilot()
    xs = shard_cases(shard)
    g["d0_1500"] = len(table) == m130.EXPECT_D0
    g["pilot_6"] = len(p) == 6
    g["m131_cases_in_pilot"] = set(M131_CASES) <= p
    g["remaining_1494"] = len(remaining()) == m130.EXPECT_D0 - 6
    g["sample_distinct"] = len(set(sample())) == SAMPLE
    g["shard_40"] = len(xs) == SAMPLE // len(SHARDS)
    g["all_d0"] = all(x in table and table[x][0]["dmeet"] == 0 for x in xs)
    g["none_pilot"] = not (set(xs) & p)
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


def is_solution(row):
    """A SAT row whose model passes every m106 check (anisotropic included)."""
    chk = row.get("check") or {}
    return (row.get("cert") == "SAT" and row.get("satisfies_cnf") is True and bool(chk)
            and all(v is True for v in chk.values()))


def median(xs):
    xs = sorted(xs)
    if not xs:
        return None
    k = len(xs) // 2
    return xs[k] if len(xs) % 2 else (xs[k - 1] + xs[k]) / 2


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
    g["no_solution"] = not any(is_solution(r) for r in done)
    g["at_least_20_done"] = len(done) >= 20
    out = {"graded": g, "shard": shard, "mode": MODE, "done": len(done), "rows": len(rows),
           "counts": counts, "cadical_unsat_seconds": {"median": median(secs),
                                                       "max": max(secs) if secs else None,
                                                       "n": len(secs)},
           "drat_seconds_max": max([(r.get("drat") or {}).get("seconds") or 0 for r in done] or [0]),
           "proof_bytes_max": max([r.get("proof_bytes") or 0 for r in done] or [0]),
           "verified": sorted(r.get("instance") for r in done if r.get("cert") == "VERIFIED"),
           "open": sorted(r.get("instance") for r in rows if r.get("cert") != "VERIFIED"),
           "solutions": [r.get("instance") for r in done if is_solution(r)]}
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
