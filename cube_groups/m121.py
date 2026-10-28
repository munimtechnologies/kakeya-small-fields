# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m121 (pilot): cube and conquer on the d = 1 cases with k(T(N)) <= 4 that stayed UNKNOWN at
1,500 s with m102's sweep CNF (notes/a108.md, a109.md, cube_groups/m121-predictions.md).

What came back on 2026-10-28 (notes/a109.md): 3,846 of the 3,876 d = 1 cases have UNSAT answers;
30 stayed UNKNOWN at 1,500 s, under eight labels, and 24 of them under four: t2 m011 (8), t2 m026
(6), t2 m031 (6), t3 m011_017 (4). The decision rules of m112 and m116 say: do not raise the cap
again; split the case. This pilot splits one case of each of those four labels on K = 3 entries of
A_(h_1) (h_1 is basis index 4 of V): the three entries of A_(h_1) that no unit clause fixes and that
occur in most clauses (ties by variable number). The 2^K cubes add every sign pattern of those K
variables as unit clauses, so they cover every assignment, and the case is UNSAT exactly when every
cube is. Each cube is solved by the CaDiCaL binary (no proof yet; certificates come once the
splitting is known to work), at most 600 s.

Parts:

    check     the open list: the 3,876 d = 1 cases less the 3,408 that m110a-j decided less the 438
              sweep UNSATs (m112a-l, m114a-f, m116a-b, m119) gives 30; the pilot cases (the first
              case by name of each of the four labels); both programs present
    control   the same split on the "n" CNF of m110's control o007_c008 t2_m012, which is SAT: at
              least one cube must be SAT, with a model that satisfies the CNF (the split cannot lose
              a solution)
    run       the four cases, one after another, their cubes two at a time; no cube starts after
              --minutes
    grade     the graded checks of m121-predictions.md

Usage: python m121.py --part check|control|run|grade [--tools DIR] [--k K] [--cap S] [--workers W]
       [--minutes M] [--out-dir D]
       (the grade files of m110a-j, m112a-l, m114a-f, m116a-b and m119 in the working directory)
"""
import argparse
import collections
import concurrent.futures as cf
import itertools
import json
import os
import tempfile
import time

import m100
import m104
import m108
import m111
import m113
import m120

H1 = 4                         # index of h_1 among the basis vectors of V (u, v_1..v_3, h_1..h_7)
LABELS = ("t2_m011", "t2_m026", "t2_m031", "t3_m011_017")
N_OPEN = 30
N_D1 = 3876


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def open_cases(src="."):
    """The d = 1 cases with no UNSAT answer, sorted by name, or None if a grade file is missing."""
    unsat = m120.sweep_unsat(src)
    parts = m111.m110_parts("abcdefghij")
    if unsat is None or parts is None:
        return None
    decided = {x for x, _ in m113.decided(parts)}
    return sorted(set(m113.d1_cases()) - decided - unsat)


def pilot_cases(names):
    """The first case by name of each label of LABELS."""
    out = []
    for label in LABELS:
        mine = [x for x in names if x[20:] == label]
        if mine:
            out.append(mine[0])
    return out


# ---------- the split ----------

def cube_vars(clauses, names, k):
    """K variables of A_(h_1): not fixed by a unit clause, most occurrences first, then by number."""
    a_h1 = [v for row in names[0][H1] for v in row]
    fixed = {abs(c[0]) for c in clauses if len(c) == 1}
    count = collections.Counter(abs(x) for c in clauses for x in c)
    free = [v for v in a_h1 if v not in fixed]
    return sorted(free, key=lambda v: (-count[v], v))[:k]


def cubes(variables):
    """Every sign pattern of the variables, as lists of unit literals (2^K of them)."""
    return [[v if s else -v for v, s in zip(variables, signs)]
            for signs in itertools.product((True, False), repeat=len(variables))]


def position(names, v):
    """(row, column) of v in A_(h_1)."""
    for r, row in enumerate(names[0][H1]):
        if v in row:
            return [r, row.index(v)]
    return None


def solve_cubes(tools, cnf, names, k, cap, workers, deadline, tmp):
    """One row per cube: CaDiCaL on the CNF with the cube's unit clauses."""
    variables = cube_vars(cnf.clauses, names, k)
    paths = []
    for i, cube in enumerate(cubes(variables)):
        path = os.path.join(tmp, f"cube{i}.cnf")
        m104.write_dimacs(cnf.clauses + [[x] for x in cube], cnf.nv, path)
        paths.append((i, cube, path))

    def one(item):
        i, cube, path = item
        if time.time() > deadline:
            return {"cube": i, "units": cube, "status": "SKIPPED"}
        res, text = m104.run_cadical(tools, path, None, cap)
        row = {"cube": i, "units": cube, "status": res["status"], "seconds": res["seconds"]}
        if res["status"] == "SAT":
            row["satisfies_cnf"] = m104.satisfied(cnf.clauses, m104.model_of(text))
        os.remove(path)
        return row

    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        rows = sorted(ex.map(one, paths), key=lambda r: r["cube"])
    return {"vars": variables, "positions": [position(names, v) for v in variables],
            "cubes": rows}


def verdict(rows):
    """UNSAT if every cube is UNSAT, SAT if a cube is SAT, else OPEN."""
    st = [r["status"] for r in rows]
    if st and all(s == "UNSAT" for s in st):
        return "UNSAT"
    if "SAT" in st:
        return "SAT"
    return "OPEN"


# ---------- the parts ----------

def run_check(tools, out_dir):
    g = {}
    names = open_cases()
    g["grades_loaded"] = names is not None
    names = names or []
    g["d1_3876"] = len(m113.d1_cases()) == N_D1
    g["open_30"] = len(names) == N_OPEN
    pilot = pilot_cases(names)
    g["pilot_4"] = len(pilot) == len(LABELS)
    g["tools"] = os.access(os.path.join(tools, "cadical"), os.X_OK)
    labels = dict(collections.Counter(x[20:] for x in names))
    save(out_dir, "m121_check.json", {"open": names, "labels": labels, "pilot": pilot,
                                       "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'open': len(names), 'labels': labels, 'pilot': pilot}, sort_keys=True)}",
          flush=True)


def run_control(tools, k, workers, out_dir):
    spec, case = m113.d1_cases()[m113.CONTROL]
    cnf, names = m108.build_cert(spec, case, "n")
    with tempfile.TemporaryDirectory() as tmp:
        res = solve_cubes(tools, cnf, names, k, 120.0, workers, time.time() + 3600, tmp)
    sat = [r for r in res["cubes"] if r["status"] == "SAT"]
    g = {"control_vars_k": len(res["vars"]) == k,
         "control_cubes": len(res["cubes"]) == 2 ** k,
         "control_some_sat": bool(sat),
         "control_models_ok": bool(sat) and all(r["satisfies_cnf"] for r in sat)}
    save(out_dir, "m121_control.json", {"instance": m113.CONTROL, "graded": g, **res})
    print(f"SUMMARY control all_match {all(g.values())} "
          f"{json.dumps([[r['status'], r.get('seconds')] for r in res['cubes']])}", flush=True)


def run(tools, k, cap, workers, minutes, out_dir):
    start = time.time()
    deadline = start + minutes * 60
    info = m100.load(out_dir, "m121_check.json") or {"pilot": []}
    d1 = m113.d1_cases()
    rows = []
    for x in info["pilot"]:
        spec, case = d1[x]
        t0 = time.time()
        cnf, names = m108.build_cert(spec, case, "sweep")
        clauses = len(cnf.clauses)
        with tempfile.TemporaryDirectory() as tmp:
            res = solve_cubes(tools, cnf, names, k, cap, workers, deadline, tmp)
        del cnf
        row = {"instance": x, "label": x[20:], "clauses": clauses, "verdict": verdict(res["cubes"]),
               "wall_seconds": round(time.time() - t0, 1), **res}
        rows.append(row)
        save(out_dir, "m121_rows.json", rows)
        print(f"case {x[10:]}: {row['verdict']} cubes "
              f"{json.dumps([[c['status'], c.get('seconds')] for c in res['cubes']])}", flush=True)
    print(f"SUMMARY run cases {len(rows)} "
          f"{json.dumps(dict(collections.Counter(r['verdict'] for r in rows)), sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade(k, out_dir):
    g, out = {}, {}
    chk = m100.load(out_dir, "m121_check.json")
    ctl = m100.load(out_dir, "m121_control.json")
    rows = m100.load(out_dir, "m121_rows.json")
    for name, st in (("check", chk), ("control", ctl)):
        if st is None:
            g[name + "_ran"] = False
        else:
            g.update({name + "_" + key: v for key, v in st["graded"].items()})
    g["run_ran"] = rows is not None
    rows = rows or []
    g["all_accounted"] = sorted(r["instance"] for r in rows) == sorted((chk or {}).get("pilot", []))
    g["cubes_complete"] = all(len(r["cubes"]) == 2 ** k and len(r["vars"]) == k for r in rows)
    g["no_error"] = not any(c["status"] == "ERROR" for r in rows for c in r["cubes"])
    sat = [c for r in rows for c in r["cubes"] if c["status"] == "SAT"]
    g["sat_models_ok"] = all(c.get("satisfies_cnf") for c in sat)
    secs = sorted(c["seconds"] for r in rows for c in r["cubes"] if c["status"] == "UNSAT")
    out.update({"verdicts": {r["instance"]: r["verdict"] for r in rows},
                "cube_status": dict(collections.Counter(c["status"] for r in rows
                                                        for c in r["cubes"])),
                "unsat_cube_seconds": {"n": len(secs), "median": secs[len(secs) // 2],
                                       "max": secs[-1]} if secs else None,
                "positions": {r["instance"]: r["positions"] for r in rows},
                "sat_cubes": len(sat)})
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "control", "run", "grade"], default="check")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--k", type=int, default=3)
    ap.add_argument("--cap", type=float, default=600.0)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--minutes", type=float, default=190.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.tools, args.out_dir)
    elif args.part == "control":
        run_control(args.tools, args.k, args.workers, args.out_dir)
    elif args.part == "run":
        run(args.tools, args.k, args.cap, args.workers, args.minutes, args.out_dir)
    else:
        out = grade(args.k, args.out_dir)
        save(args.out_dir, "m121_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k != "graded"}
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad} "
              f"{json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
