# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m130: census of the d = 0 cases of the rank-0 case of (B7)_8 (t = 8, dim V = 11) and a pilot
on six of them (notes/a126.md, cube_groups/m130-predictions.md).

Where this starts: with job m129q (notes/a126.md) every one of the 3,876 d = 1 cases with
k(T(N)) <= 4 has a drat-trim-checked DRAT certificate. Note a122 lists "the d = 0 cases (1,500)" as
the next block before A(8) <= 10, but no job has listed or attempted them. This job does both:

    check     the classes of m100's shards with dmeet = 0 (the d = 0 classes), their cases from
              m102.class_cases (t1 dropped) with k(T(N)) <= 4 by m105.le4; the count (predicted
              1,500), the kinds, no name among the d = 1 cases, the tools present; six pilot cases
              spread evenly through the sorted names
    controls  m113's controls (cert1's three tool controls; the "n" control o007_c008 t2_m012 SAT
              with a model that passes m106's checks)
    cert      the six pilot cases, one at a time, at m106's "n" CNF (m102's relax CNF plus
              anisotropy on the 15 non-zero vectors of N): CaDiCaL 600 s with an ASCII DRAT proof,
              drat-trim 1,200 s; no new case starts after 150 minutes (SKIPPED, not failed)
    grade     the graded checks of m130-predictions.md

Usage: python m130.py --part check|controls|cert|grade [--tools DIR] [--out-dir D]
"""
import argparse
import functools
import json
import os
import tempfile
import time

import m100
import m102
import m105
import m113

PILOT_N = 6
MODE = "n"
CADICAL_CAP = 600.0
DRAT_CAP = {"n": 1200, "sweep": 1500}
NO_START_AFTER = 150 * 60       # seconds after the cert part starts
EXPECT_D0 = 1500                # notes/a122.md: "the d = 0 cases (1,500)"
PREFIX = "m130"


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def load(out_dir, name):
    path = os.path.join(out_dir, name)
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


@functools.lru_cache(maxsize=None)
def d0_specs():
    """The classes with dmeet = 0, in m100's shard order."""
    return tuple(spec for sh in sorted(m100.SHARDS) for spec in m100.shard_specs(sh)
                 if spec["dmeet"] == 0)


@functools.lru_cache(maxsize=None)
def d0_cases():
    """((spec, case), ...): the k <= 4 cases of the d = 0 classes, in m102's order (t1 dropped)."""
    out = []
    for spec in d0_specs():
        out += [(spec, c) for c in m102.class_cases(spec)[1:] if m105.le4(c)]
    return tuple(out)


def by_name():
    return {m102.inst_name(s, c): (s, c) for s, c in d0_cases()}


def pilot_names(names, n=PILOT_N):
    """n names spread evenly through the sorted list: index floor(k * len / n), k = 0 .. n - 1."""
    names = sorted(names)
    if len(names) <= n:
        return list(names)
    return [names[(k * len(names)) // n] for k in range(n)]


# ---------- the parts ----------

def run_check(tools, out_dir):
    g = {}
    specs = d0_specs()
    cases = d0_cases()
    names = [m102.inst_name(s, c) for s, c in cases]
    kinds = {}
    for _, c in cases:
        kinds[c["kind"]] = kinds.get(c["kind"], 0) + 1
    per_class = {}
    for s, c in cases:
        per_class[s["name"]] = per_class.get(s["name"], 0) + 1
    all_cases = {s["name"]: len(m102.class_cases(s)) - 1 for s in specs}
    d1 = set(m113.d1_cases())
    pilot = pilot_names(names)
    g["d0_classes_nonempty"] = len(specs) > 0
    g["d0_all_dmeet0"] = all(s["dmeet"] == 0 for s in specs)
    g["d0_le4_1500"] = len(cases) == EXPECT_D0
    g["names_unique"] = len(set(names)) == len(names)
    g["no_t1"] = "t1" not in kinds
    g["disjoint_from_d1"] = not (set(names) & d1)
    g["pilot_size"] = len(pilot) == min(PILOT_N, len(names))
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    save(out_dir, f"{PREFIX}_check.json", {
        "n_classes": len(specs), "classes": [s["name"] for s in specs], "n_cases": len(cases),
        "by_kind": kinds, "per_class_le4": per_class, "per_class_all": all_cases,
        "names": names, "pilot": [[x, MODE] for x in pilot], "graded": g,
        "caps": {"cadical": CADICAL_CAP, "drat": DRAT_CAP, "no_start_after": NO_START_AFTER}})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'classes': len(specs), 'cases': len(cases), 'kinds': kinds, 'pilot': pilot}, sort_keys=True)}",
          flush=True)


def run_controls(tools, out_dir):
    m113.run_controls("a", tools, out_dir)
    os.replace(os.path.join(out_dir, "m113a_controls.json"),
               os.path.join(out_dir, f"{PREFIX}_controls.json"))


def run_cert(tools, out_dir):
    m113.CADICAL_CAP = CADICAL_CAP
    m113.DRAT_CAP = dict(DRAT_CAP)
    start = time.time()
    name = f"{PREFIX}_cert.json"
    info = load(out_dir, f"{PREFIX}_check.json") or {"pilot": []}
    table = by_name()
    rows, counts = [], {}
    for x, mode in info["pilot"]:
        if x not in table:
            rows.append({"instance": x, "mode": mode, "cert": "MISSING"})
            continue
        spec, case = table[x]
        if time.time() - start > NO_START_AFTER:
            rows.append({"instance": x, "name": spec["name"], "mode": mode, "cert": "SKIPPED"})
            save(out_dir, name, rows)
            continue
        try:
            with tempfile.TemporaryDirectory() as tmp:
                row = m113.certify(tools, spec, case, mode, tmp)
        except Exception as e:  # keep the part's exit code 0; the grade sees the row
            print(f"cert {x}: error {e!r}", flush=True)
            rows.append({"instance": x, "name": spec["name"], "mode": mode, "cert": "ERROR",
                         "error": repr(e)})
            save(out_dir, name, rows)
            continue
        rows.append(row)
        save(out_dir, name, rows)
        counts[row["cert"]] = counts.get(row["cert"], 0) + 1
        print(f"cert {row['instance']}: {row['cert']} {row.get('mode')} inv {row.get('inv')} "
              f"{row.get('type')} cadical {(row.get('cadical') or {}).get('status')} "
              f"{(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"clauses {row.get('clauses')} wall {row.get('wall_seconds')} s", flush=True)
    save(out_dir, name, rows)
    print(f"SUMMARY cert cases {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def grade(out_dir):
    g = {}
    for part in ("check", "controls"):
        st = load(out_dir, f"{PREFIX}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in (st.get("graded") or {}).items()})
    chk = load(out_dir, f"{PREFIX}_check.json") or {"pilot": []}
    rows = load(out_dir, f"{PREFIX}_cert.json")
    g["cert_ran"] = rows is not None
    rows = rows or []
    want = [x for x, _ in chk["pilot"]]
    got = [r.get("instance") for r in rows]
    unsat = [r for r in rows if ((r.get("cadical") or {}).get("status") == "UNSAT")]
    sat = [r for r in rows if ((r.get("cadical") or {}).get("status") == "SAT")
           or r.get("cert") == "SAT"]
    g["pilot_all_accounted"] = sorted(got) == sorted(want)
    g["no_sat"] = not sat
    g["no_error"] = not any(r.get("cert") in ("ERROR", "MISSING") for r in rows)
    g["unsat_at_n_ge_4"] = len(unsat) >= 4
    g["all_unsat_verified"] = all(r.get("cert") == "VERIFIED" for r in unsat)
    by_cert = {}
    for r in rows:
        by_cert[r.get("cert")] = by_cert.get(r.get("cert"), 0) + 1
    cad = sorted((r.get("cadical") or {}).get("seconds") for r in rows
                 if (r.get("cadical") or {}).get("seconds") is not None)
    drat = sorted((r.get("drat") or {}).get("seconds") for r in rows
                  if (r.get("drat") or {}).get("seconds") is not None)
    out = {"graded": g, "by_cert": by_cert, "n_rows": len(rows), "unsat": len(unsat),
           "sat": len(sat), "cadical_seconds": cad, "drat_seconds": drat,
           "largest_proof": max((r.get("proof_bytes") or 0 for r in rows), default=0),
           "wall_seconds_max": max((r.get("wall_seconds") or 0 for r in rows), default=0),
           "n_classes": chk.get("n_classes"), "n_cases": chk.get("n_cases"),
           "by_kind": chk.get("by_kind"),
           "rows": [[r.get("instance"), r.get("cert"), (r.get("cadical") or {}).get("status"),
                     (r.get("cadical") or {}).get("seconds"), (r.get("drat") or {}).get("seconds"),
                     r.get("proof_bytes"), r.get("clauses"), r.get("vars")] for r in rows]}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.tools, args.out_dir)
    else:
        out = grade(args.out_dir)
        save(args.out_dir, f"{PREFIX}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows")}
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad[:12]} "
              f"{json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
