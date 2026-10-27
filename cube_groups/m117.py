# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m117: a pilot of DRAT certificates for the d = 1 cases that only the sweep CNF refuted at
1,500 s (jobs m110i, m112a-l, m114a-f), three cases at three solve times
(cube_groups/m117-predictions.md).

What came back on 2026-10-27 (notes/a107.md): job m113 certified 3,073 of the 3,075 d = 1 cases
that m110a-h and j refuted (2,049 in shards b, c, e, f; 513 in a; 511 in d), mostly "n" CNFs of
about 546,000 clauses checked in seconds. With m112l, 3,834 of the 3,876 d = 1 cases have UNSAT
answers. 761 of those have no certificate yet: the 333 of m110i, two that m115 re-runs, and 426
refuted only by m102's sweep CNF (about 907,000 clauses) at 1,500 s, by pysat's CaDiCaL in 260 to
1,500 s (jobs m112a-l and m114a-f). Nobody has measured what a
DRAT proof of one of these costs: CaDiCaL's time with proof logging, the size of the proof on disk
and drat-trim's time. The full run (about 760 cases) is sized from this pilot.

The three cases are sweep UNSATs of job m112l (pysat CaDiCaL 1.9.5 times 260 s, 422 s and 713 s, the
last being m112l's median), one t3 and two t2, in three orbits. Each is certified as m113 does it
(m113.certify: the sweep CNF built again, CaDiCaL with an ASCII DRAT proof, drat-trim, the proof
deleted once checked), one at a time, fastest first, with CaDiCaL at 2,400 s and drat-trim at
4,800 s, and its clause count compared with the one m112l wrote down.

Parts:

    controls  m113's controls: cert1's three tool controls and the "n" control o007_c008 t2_m012
              (SAT, with a model that passes m106's checks)
    cert      the three cases, one at a time, while time remains
    grade     the graded checks of m117-predictions.md

Usage: python m117.py --part controls|cert|grade [--tools DIR] [--minutes M] [--out-dir D]
"""
import argparse
import json
import os
import time

import m100
import m113

# instance -> (clauses of the sweep CNF in job m112l, pysat CaDiCaL seconds in m112l), fastest first
CASES = {
    "r3b_t8_B7_o007_c005_t2_m034": (907089, 260.24),
    "r3b_t8_B7_o009_c002_t3_m004_034": (906105, 421.64),
    "r3b_t8_B7_o010_c000_t2_m047": (907113, 712.78),
}
MODE = "sweep"
CADICAL_CAP = 2400.0           # m113: 600 s; m115: 1,200 s
DRAT_CAP = {"n": 2400, "sweep": 4800}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def order():
    """The cases, fastest (in m112l) first."""
    return sorted(CASES, key=lambda x: CASES[x][1])


def run_controls(tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, "m117_controls.json"))


def run_cert(tools, minutes, out_dir):
    m113.CADICAL_CAP, m113.DRAT_CAP = CADICAL_CAP, DRAT_CAP
    deadline = time.time() + minutes * 60
    rows = []
    m113.d1_cases()
    for x in order():
        row = m113.certify_item(tools, x, MODE, deadline)
        rows.append(row)
        save(out_dir, "m117_cert.json", rows)
        if row["cert"] == "SKIPPED":
            print(f"cert {x}: SKIPPED", flush=True)
            continue
        print(f"cert {x}: {row['cert']} cadical {row['cadical'].get('seconds')} s (pysat "
              f"{CASES[x][1]} s) drat {(row.get('drat') or {}).get('seconds')} s proof "
              f"{row['proof_bytes']} B clauses {row['clauses']}", flush=True)


def grade_rows(rows):
    """(graded, out) from the cert rows."""
    done = [r for r in rows if r["cert"] != "SKIPPED"]
    g = {"all_accounted": sorted(r["instance"] for r in rows) == sorted(CASES),
         "mode_sweep": all(r.get("mode") == MODE for r in rows),
         "same_cnf": all(r.get("clauses") == CASES[r["instance"]][0] for r in done
                         if r["instance"] in CASES),
         "no_sat": not any(r["cert"] == "SAT" for r in done),
         "all_verified": bool(rows) and all(r["cert"] == "VERIFIED" for r in rows)}
    out = {"rows": {r["instance"]: [r["cert"], (r.get("cadical") or {}).get("seconds"),
                                    (r.get("drat") or {}).get("seconds"), r.get("proof_bytes"),
                                    r.get("wall_seconds"), CASES.get(r["instance"], (0, 0))[1]]
                    for r in rows},
           "verified": sum(r["cert"] == "VERIFIED" for r in rows),
           "skipped": sorted(r["instance"] for r in rows if r["cert"] == "SKIPPED")}
    ver = [r for r in done if r["cert"] == "VERIFIED"]
    if ver:
        # what the full run would cost, per case, scaled from the pilot
        out["per_case"] = {
            "wall_seconds_mean": round(sum(r["wall_seconds"] for r in ver) / len(ver), 1),
            "proof_bytes_max": max(r["proof_bytes"] for r in ver),
            "cadical_over_pysat": [round(r["cadical"]["seconds"] / CASES[r["instance"]][1], 2)
                                   for r in ver],
            "drat_over_cadical": [round(r["drat"]["seconds"] / max(r["cadical"]["seconds"], 0.01),
                                        2) for r in ver]}
    return g, out


def grade(out_dir):
    g = {}
    ctl = m100.load(out_dir, "m117_controls.json")
    if ctl is None:
        g["controls_ran"] = False
    else:
        g.update({"controls_" + k: v for k, v in ctl["graded"].items()})
    rows = m100.load(out_dir, "m117_cert.json")
    g["cert_ran"] = rows is not None
    rg, out = grade_rows(rows or [])
    g.update(rg)
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["controls", "cert", "grade"], default="controls")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--minutes", type=float, default=240.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.tools, args.minutes, args.out_dir)
    else:
        out = grade(args.out_dir)
        save(args.out_dir, "m117_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k != "graded"}
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad} "
              f"{json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
