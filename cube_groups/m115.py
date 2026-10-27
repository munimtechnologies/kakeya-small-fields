# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m115: the d = 1 cases whose DRAT certificate run in job m113 stopped at CaDiCaL's 600 s cap
(status UNKNOWN), each re-run alone with every cap doubled, as the decision rule of
m113-predictions.md says (cube_groups/m115-predictions.md).

Jobs m113b, c and f certified all of their 1,538 cases; m113e certified 511 of its 512 and stopped
at 600 s on o007_c001 t2_m026 ("n" CNF). The first attempt of m113d, stopped from outside after 283
cases, had stopped at 600 s on o007_c009 t3_m011_017 ("n" CNF) too. pysat's CaDiCaL had refuted both
"n" CNFs within 60 s in jobs m110e and m110d; the binary with proof logging did not within 600 s.

Each case is certified as m113 does it (m113.certify: the CNF built again, its SHA-256 compared with
the one m113 wrote down, CaDiCaL with an ASCII DRAT proof, drat-trim), one at a time, with CaDiCaL
at 1,200 s and drat-trim at 2,400 s.

Parts:

    controls  m113's controls: cert1's three tool controls and the "n" control o007_c008 t2_m012
              (SAT, with a model that passes m106's checks)
    cert      the cases, one at a time
    grade     the graded checks of m115-predictions.md

Usage: python m115.py --part controls|cert|grade [--tools DIR] [--out-dir D]
"""
import argparse
import json
import os
import tempfile

import m100
import m113

# instance -> (CNF that was UNSAT for it, SHA-256 of that CNF as job m113 wrote it)
CASES = {
    "r3b_t8_B7_o007_c001_t2_m026":
        ("n", "5615ad636863fa8e4cf3baf4b1ea60b94e3bd6cb3f24627836f6ff6266aeb115"),
    "r3b_t8_B7_o007_c009_t3_m011_017":
        ("n", "ccf1a168eb0268b46d4a50547e3770e3068834f53a498569a3a9ecfb86ba057e"),
}
CADICAL_CAP = 1200.0           # m113: 600 s
DRAT_CAP = {"n": 2400, "sweep": 3000}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def run_controls(tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, "m115_controls.json"))


def run_cert(tools, out_dir):
    m113.CADICAL_CAP, m113.DRAT_CAP = CADICAL_CAP, DRAT_CAP
    rows = []
    for x, (mode, _) in sorted(CASES.items()):
        spec, case = m113.d1_cases()[x]
        with tempfile.TemporaryDirectory() as tmp:
            row = m113.certify(tools, spec, case, mode, tmp)
        rows.append(row)
        save(out_dir, "m115_cert.json", rows)
        print(f"cert {x}: {row['cert']} cadical {row['cadical'].get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row['proof_bytes']} B", flush=True)


def grade_rows(rows):
    """(graded, out) from the cert rows."""
    g = {"all_accounted": sorted(r["instance"] for r in rows) == sorted(CASES),
         "same_cnf": all(r.get("cnf_sha256") == CASES[r["instance"]][1] for r in rows
                         if r["instance"] in CASES),
         "no_sat": not any(r["cert"] == "SAT" for r in rows),
         "all_verified": bool(rows) and all(r["cert"] == "VERIFIED" for r in rows)}
    out = {"rows": {r["instance"]: [r["cert"], r["mode"], r.get("cnf_sha256"),
                                    (r.get("cadical") or {}).get("seconds"),
                                    (r.get("drat") or {}).get("seconds"), r.get("proof_bytes")]
                    for r in rows},
           "verified": sum(r["cert"] == "VERIFIED" for r in rows)}
    return g, out


def grade(out_dir):
    g = {}
    ctl = m100.load(out_dir, "m115_controls.json")
    if ctl is None:
        g["controls_ran"] = False
    else:
        g.update({"controls_" + k: v for k, v in ctl["graded"].items()})
    rows = m100.load(out_dir, "m115_cert.json")
    g["cert_ran"] = rows is not None
    rg, out = grade_rows(rows or [])
    g.update(rg)
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["controls", "cert", "grade"], default="controls")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.tools, args.out_dir)
    else:
        out = grade(args.out_dir)
        save(args.out_dir, "m115_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad} "
              f"{json.dumps(out['rows'], sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
