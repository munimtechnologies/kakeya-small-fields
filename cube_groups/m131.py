# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m131: the three d = 0 pilot cases of (B7)_8 that job m130 left undecided at m106's "n" CNF,
each alone, at the sweep CNF with long limits and a DRAT certificate (notes/a127.md,
cube_groups/m131-predictions.md).

Where they come from: m130 (2026-11-02) ran six d = 0 cases at "n" (CaDiCaL 600 s). Three were
UNSAT with drat-trim-VERIFIED proofs. One, r3b_t8_B7_o012_c003_t2_m204, was SAT in 3.68 s; its model
satisfies the CNF and passes every m106 check except "anisotropic" (it is not anisotropic on all of
V), exactly like m113's d = 1 control, so it is not a solution of the case. Two,
r3b_t8_B7_o012_c002_t2_m085 and r3b_t8_B7_o012_c005_t2_m170, were UNKNOWN at 600 s. m130's
pre-registered rule sends the SAT case to the sweep CNF, and, with fewer than 4 of 6 UNSAT, sends
the rest of the pilot to the sweep CNF one case per job before any sharding. This is that step.

Shards: a = the SAT case, b and c = the two UNKNOWN cases. Each runs CaDiCaL at 4,800 s with an
ASCII DRAT proof and drat-trim at 25,000 s (m129q needed 2,035 s of drat-trim for a 1.86 GB proof
and had failed at 7,200 s on a loaded machine; m130's UNKNOWN proofs were already 0.9 to 1.2 GB
after 600 s).

Parts:

    check     the case is one of m130's 1,500 d = 0 cases (m130.by_name), its class has dmeet = 0,
              both programs are present
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      the case at the sweep CNF (m113.certify)
    grade     the graded checks of m131-predictions.md

Usage: python m131.py --part check|controls|cert|grade --shard a|b|c [--tools DIR] [--out-dir D]
"""
import argparse
import json
import os
import tempfile
import time

import m113
import m130

CASES = {
    "a": "r3b_t8_B7_o012_c003_t2_m204",   # SAT at "n" in m130, model not anisotropic on V
    "b": "r3b_t8_B7_o012_c002_t2_m085",   # UNKNOWN at "n" (600 s) in m130
    "c": "r3b_t8_B7_o012_c005_t2_m170",   # UNKNOWN at "n" (600 s) in m130
}
M130_CERT = {"a": "SAT", "b": "UNKNOWN", "c": "UNKNOWN"}
MODE = "sweep"
CADICAL_CAP = 4800.0
DRAT_CAP = {"n": 1200, "sweep": 25000}
PREFIX = "m131"


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


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    x = CASES[shard]
    table = m130.by_name()
    g["d0_1500"] = len(table) == m130.EXPECT_D0
    g["case_is_d0"] = x in table
    if x in table:
        spec, case = table[x]
        g["dmeet0"] = spec["dmeet"] == 0
        g["name_matches"] = m130.m102.inst_name(spec, case) == x
        info = {"class": spec["name"], "kind": case.get("kind")}
    else:
        g["dmeet0"] = False
        g["name_matches"] = False
        info = {}
    g["cases_distinct"] = len(set(CASES.values())) == len(CASES)
    g["tools"] = all(os.access(os.path.join(tools, t), os.X_OK) for t in ("cadical", "drat-trim"))
    save(out_dir, fname(shard, "check"), {"shard": shard, "case": x, "mode": MODE,
                                          "m130_cert": M130_CERT[shard], "info": info,
                                          "caps": {"cadical": CADICAL_CAP, "drat": DRAT_CAP},
                                          "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'case': x, 'mode': MODE, 'info': info}, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, fname(shard, "controls")))


def run_cert(shard, tools, out_dir):
    m113.CADICAL_CAP = CADICAL_CAP
    m113.DRAT_CAP = dict(DRAT_CAP)
    start = time.time()
    x = CASES[shard]
    table = m130.by_name()
    rows = []
    if x not in table:
        rows.append({"instance": x, "mode": MODE, "cert": "MISSING"})
    else:
        spec, case = table[x]
        try:
            with tempfile.TemporaryDirectory() as tmp:
                row = m113.certify(tools, spec, case, MODE, tmp)
        except Exception as e:  # keep the part's exit code 0; the grade sees the row
            print(f"cert {x}: error {e!r}", flush=True)
            row = {"instance": x, "name": spec["name"], "mode": MODE, "cert": "ERROR",
                   "error": repr(e)}
        rows.append(row)
    save(out_dir, fname(shard, "cert"), rows)
    for row in rows:
        print(f"cert {row.get('instance')}: {row.get('cert')} {row.get('mode')} inv "
              f"{row.get('inv')} {row.get('type')} cadical "
              f"{(row.get('cadical') or {}).get('status')} "
              f"{(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"clauses {row.get('clauses')} wall {row.get('wall_seconds')} s check "
              f"{json.dumps(row.get('check'), sort_keys=True)}", flush=True)
    print(f"SUMMARY cert {shard} seconds {round(time.time() - start)}", flush=True)


def is_solution(row):
    """A SAT row whose model passes every m106 check (anisotropic included)."""
    chk = row.get("check") or {}
    return (row.get("cert") == "SAT" and row.get("satisfies_cnf") is True and bool(chk)
            and all(v is True for v in chk.values()))


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
    row = rows[0] if rows else {}
    status = (row.get("cadical") or {}).get("status")
    g["row_present"] = len(rows) == 1 and row.get("instance") == CASES[shard]
    g["no_error"] = row.get("cert") not in ("ERROR", "MISSING", None)
    g["unsat"] = status == "UNSAT"
    g["verified"] = row.get("cert") == "VERIFIED"
    g["no_solution"] = not is_solution(row)
    out = {"graded": g, "shard": shard, "case": CASES[shard], "m130_cert": M130_CERT[shard],
           "mode": MODE, "cert": row.get("cert"), "status": status,
           "cadical_seconds": (row.get("cadical") or {}).get("seconds"),
           "drat_seconds": (row.get("drat") or {}).get("seconds"),
           "proof_bytes": row.get("proof_bytes"), "clauses": row.get("clauses"),
           "vars": row.get("vars"), "cnf_sha256": row.get("cnf_sha256"),
           "wall_seconds": row.get("wall_seconds"), "check": row.get("check"),
           "solution": is_solution(row)}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--shard", choices=sorted(CASES), default="a")
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
        save(args.out_dir, fname(args.shard, "grade"), out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "check")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
