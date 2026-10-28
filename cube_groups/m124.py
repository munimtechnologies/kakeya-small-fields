# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m124 (pilot): adaptive cube and conquer on the d = 1 cases with k(T(N)) <= 4 that are still
open (notes/a111.md, cube_groups/m124-predictions.md).

What came back on 2026-10-28 (notes/a111.md): m121 split four cases on K = 3 entries of A_(h_1)
into 8 cubes at 600 s each. Two of its four cases were not open: m121's open list (45) left out the
15 cases m111b-c refuted, as m120's did, and o007_c000 t2_m011 and o007_c001 t3_m011_017 are among
them (m121 agrees on the second: UNSAT in all 8 cubes). On the two open cases, o007_c003 t2_m026
and o007_c007 t2_m031, 7 and 6 of 8 cubes were UNSAT and the rest UNKNOWN at 600 s. Every cube with
the first entry true was UNSAT in about a second; the hard cubes are those with the first one or two
entries false, where the SAT control's two models lie too. By m121's decision rule (cubes UNKNOWN at
600 s) the next pilot splits further, on these cases only. m124 does it adaptively: a cube still
UNKNOWN after a short run is split on the next variable, so the work goes where it is hard.

The split: variables in order, first the free entries of A_(h_1) (h_1 is basis index 4 of V) by
number of clauses, as m121, then every other free variable by number of clauses. A node is a sign
pattern of the first d variables, added as unit clauses. Each node is solved by the CaDiCaL binary
(no proof yet) at --cap seconds, or --leaf-cap at depth --max-depth; a node UNKNOWN below the
maximum depth is split into its two children. The leaves of the tree (the nodes not split) cover
every assignment exactly once (their weights 2^-d sum to 1), so a case is UNSAT exactly when every
leaf is UNSAT, and SAT when a leaf is SAT.

Parts:

    check     the open list: the 3,876 d = 1 cases less the 3,408 that m110a-j decided, the 423
              sweep UNSATs (m112a-l, m114a-f, m116a-b, m119) and the 15 that m111b-c decided gives
              30; the pilot cases (the first open case by name of each of m121's four labels); both
              programs
    control   (1) the SAT control o007_c008 t2_m012 ("n" CNF), the first 3 levels split without
              solving: a SAT leaf whose model satisfies the CNF; (2) the UNSAT control o007_c001
              t3_m011_017 (sweep CNF; refuted by m111b and in all 8 cubes by m121): UNSAT with a
              complete tree
    run       the pilot cases one after another, each for at most --case-minutes, nodes --workers
              at a time; no node starts after --minutes
    grade     the graded checks of m124-predictions.md

Usage: python m124.py --part check|control|run|grade [--tools DIR] [--cap S] [--leaf-cap S]
       [--max-depth D] [--workers W] [--case-minutes M] [--minutes M] [--out-dir D]
       (the grade files of m110a-j, m111b-c, m112a-l, m114a-f, m116a-b and m119 in the working
       directory)
"""
import argparse
import collections
import concurrent.futures as cf
import fractions
import json
import os
import tempfile
import time

import m100
import m104
import m108
import m113
import m121
import m122

N_OPEN = 30
N_D1 = 3876
SAT_CONTROL = m113.CONTROL           # r3b_t8_B7_o007_c008_t2_m012
UNSAT_CONTROL = "r3b_t8_B7_o007_c001_t3_m011_017"
CONTROL_FORCE = 3


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the cases ----------

def open_cases(src="."):
    """The d = 1 cases with no UNSAT answer, sorted by name, or None if a grade file is missing."""
    names, refuted = m121.open_cases(src), m122.m111_decided(src)
    if names is None or refuted is None:
        return None
    return sorted(set(names) - refuted)


# ---------- the split ----------

def order_vars(clauses, names, k):
    """Up to k free variables: the entries of A_(h_1) first (as m121.cube_vars), then the rest, each
    group by number of occurrences, most first, then by number."""
    fixed = {abs(c[0]) for c in clauses if len(c) == 1}
    count = collections.Counter(abs(x) for c in clauses for x in c)
    first = m121.cube_vars(clauses, names, len([v for row in names[0][m121.H1] for v in row]))
    seen = set(first)
    rest = sorted((v for v in count if v not in fixed and v not in seen),
                  key=lambda v: (-count[v], v))
    return (first + rest)[:k]


def units(order, signs):
    return [v if s else -v for v, s in zip(order, signs)]


def leaf_weight(rows):
    """Sum of 2^-depth over the nodes not split, as a fraction (1 for a complete tree)."""
    return sum((fractions.Fraction(1, 2 ** len(r["signs"])) for r in rows if not r.get("split")),
               fractions.Fraction(0))


def tree_verdict(rows):
    """SAT if a leaf is SAT; UNSAT if the leaves cover everything and all are UNSAT; else OPEN."""
    leaves = [r["status"] for r in rows if not r.get("split")]
    if "SAT" in leaves:
        return "SAT"
    if leaves and all(s == "UNSAT" for s in leaves) and leaf_weight(rows) == 1:
        return "UNSAT"
    return "OPEN"


def conquer(tools, cnf, order, cap, leaf_cap, workers, deadline, tmp, force=0):
    """Rows of the explored tree, one per node: signs, status, seconds, split. Nodes above depth
    `force` are split without solving. Stops starting nodes after a SAT leaf or the deadline."""
    rows, todo, pending = [], [()], {}
    found = False

    def one(signs):
        path = os.path.join(tmp, "n" + "".join("1" if s else "0" for s in signs) + ".cnf")
        m104.write_dimacs(cnf.clauses + [[x] for x in units(order, signs)], cnf.nv, path)
        res, text = m104.run_cadical(tools, path, None,
                                     leaf_cap if len(signs) == len(order) else cap)
        row = {"signs": list(signs), "status": res["status"], "seconds": res["seconds"]}
        if res["status"] == "SAT":
            row["satisfies_cnf"] = m104.satisfied(cnf.clauses, m104.model_of(text))
        os.remove(path)
        return row

    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        while todo or pending:
            while todo and len(pending) < workers:
                signs = todo.pop()
                if len(signs) < force:
                    rows.append({"signs": list(signs), "status": "FORCED", "split": True})
                    todo += [signs + (False,), signs + (True,)]
                elif found or time.time() > deadline:
                    rows.append({"signs": list(signs), "status": "SKIPPED"})
                else:
                    pending[ex.submit(one, signs)] = signs
            if not pending:
                continue
            done, _ = cf.wait(pending, return_when=cf.FIRST_COMPLETED)
            for fut in done:
                signs = pending.pop(fut)
                row = fut.result()
                if row["status"] == "SAT":
                    found = True
                if row["status"] == "UNKNOWN" and len(signs) < len(order) and not found:
                    row["split"] = True
                    todo += [signs + (False,), signs + (True,)]
                rows.append(row)
    return sorted(rows, key=lambda r: (len(r["signs"]), r["signs"]))


def tree_stats(rows):
    leaves = [r for r in rows if not r.get("split")]
    solved = [r["seconds"] for r in rows if r.get("seconds") is not None]
    return {"nodes": len(rows), "leaves": len(leaves),
            "leaf_status": dict(collections.Counter(r["status"] for r in leaves)),
            "max_depth": max((len(r["signs"]) for r in rows), default=0),
            "open_leaves": sorted(r["signs"] for r in leaves if r["status"] != "UNSAT")[:20],
            "solver_seconds": round(sum(solved), 1),
            "leaf_weight_unsat": float(sum((fractions.Fraction(1, 2 ** len(r["signs"]))
                                            for r in leaves if r["status"] == "UNSAT"),
                                           fractions.Fraction(0)))}


def solve_case(tools, x, mode, args, deadline, force=0):
    spec, case = m113.d1_cases()[x]
    t0 = time.time()
    cnf, names = m108.build_cert(spec, case, mode)
    order = order_vars(cnf.clauses, names, args.max_depth)
    with tempfile.TemporaryDirectory() as tmp:
        rows = conquer(tools, cnf, order, args.cap, args.leaf_cap, args.workers, deadline, tmp,
                       force)
    out = {"instance": x, "label": x[20:], "mode": mode, "clauses": len(cnf.clauses),
           "order": order, "positions": [m121.position(names, v) for v in order],
           "verdict": tree_verdict(rows), "weight": str(leaf_weight(rows)),
           "stats": tree_stats(rows), "wall_seconds": round(time.time() - t0, 1), "rows": rows}
    del cnf
    return out


# ---------- the parts ----------

def run_check(tools, out_dir):
    g = {}
    names = open_cases()
    g["grades_loaded"] = names is not None
    names = names or []
    g["d1_3876"] = len(m113.d1_cases()) == N_D1
    g["open_30"] = len(names) == N_OPEN
    pilot = m121.pilot_cases(names)
    g["pilot_4"] = len(pilot) == len(m121.LABELS)
    refuted = m122.m111_decided() or set()
    g["pilot_not_m111"] = not set(pilot) & refuted
    g["unsat_control_m111"] = UNSAT_CONTROL in refuted
    g["tools"] = os.access(os.path.join(tools, "cadical"), os.X_OK)
    labels = dict(collections.Counter(x[20:] for x in names))
    save(out_dir, "m124_check.json", {"open": names, "labels": labels, "pilot": pilot,
                                       "graded": g})
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'open': len(names), 'labels': labels, 'pilot': pilot}, sort_keys=True)}",
          flush=True)


def run_control(tools, args, out_dir):
    g = {}
    sat = solve_case(tools, SAT_CONTROL, "n", args, time.time() + 900, force=CONTROL_FORCE)
    sat_rows = [r for r in sat["rows"] if r["status"] == "SAT"]
    g["sat_control_sat"] = sat["verdict"] == "SAT"
    g["sat_control_models_ok"] = bool(sat_rows) and all(r["satisfies_cnf"] for r in sat_rows)
    forced = sum(r["status"] == "FORCED" for r in sat["rows"])
    g["sat_control_forced"] = forced == 2 ** CONTROL_FORCE - 1
    uns = solve_case(tools, UNSAT_CONTROL, "sweep", args, time.time() + args.control_minutes * 60)
    g["unsat_control_unsat"] = uns["verdict"] == "UNSAT"
    g["unsat_control_complete"] = uns["weight"] == "1"
    save(out_dir, "m124_control.json", {"graded": g, "sat": sat, "unsat": uns})
    print(f"SUMMARY control all_match {all(g.values())} {json.dumps(g, sort_keys=True)} "
          f"sat {json.dumps(sat['stats'], sort_keys=True)} unsat "
          f"{json.dumps(uns['stats'], sort_keys=True)}", flush=True)


def run(tools, args, out_dir):
    start = time.time()
    deadline = start + args.minutes * 60
    info = m100.load(out_dir, "m124_check.json") or {"pilot": []}
    out = []
    for x in info["pilot"]:
        end = min(deadline, time.time() + args.case_minutes * 60)
        res = solve_case(tools, x, "sweep", args, end)
        out.append(res)
        save(out_dir, "m124_rows.json", out)
        print(f"case {x[10:]}: {res['verdict']} weight {res['weight']} "
              f"{json.dumps(res['stats'], sort_keys=True)}", flush=True)
    print(f"SUMMARY run cases {len(out)} "
          f"{json.dumps(dict(collections.Counter(r['verdict'] for r in out)), sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade(out_dir):
    g, out = {}, {}
    chk = m100.load(out_dir, "m124_check.json")
    ctl = m100.load(out_dir, "m124_control.json")
    rows = m100.load(out_dir, "m124_rows.json")
    for name, st in (("check", chk), ("control", ctl)):
        if st is None:
            g[name + "_ran"] = False
        else:
            g.update({name + "_" + key: v for key, v in st["graded"].items()})
    g["run_ran"] = rows is not None
    rows = rows or []
    g["all_accounted"] = sorted(r["instance"] for r in rows) == sorted((chk or {}).get("pilot", []))
    g["trees_complete"] = all(fractions.Fraction(r["weight"]) == 1 for r in rows)
    g["no_error"] = not any(n["status"] == "ERROR" for r in rows for n in r["rows"])
    sat = [n for r in rows for n in r["rows"] if n["status"] == "SAT"]
    g["sat_models_ok"] = all(n.get("satisfies_cnf") for n in sat)
    out.update({"verdicts": {r["instance"]: r["verdict"] for r in rows},
                "stats": {r["instance"]: r["stats"] for r in rows},
                "weights": {r["instance"]: r["weight"] for r in rows},
                "sat_nodes": len(sat)})
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "control", "run", "grade"], default="check")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--cap", type=float, default=90.0)
    ap.add_argument("--leaf-cap", type=float, default=1200.0)
    ap.add_argument("--max-depth", type=int, default=10)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--case-minutes", type=float, default=40.0)
    ap.add_argument("--control-minutes", type=float, default=25.0)
    ap.add_argument("--minutes", type=float, default=170.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.tools, args.out_dir)
    elif args.part == "control":
        run_control(args.tools, args, args.out_dir)
    elif args.part == "run":
        run(args.tools, args, args.out_dir)
    else:
        out = grade(args.out_dir)
        save(args.out_dir, "m124_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k != "graded"}
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad} "
              f"{json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
