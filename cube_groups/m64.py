# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m64: the rank-0 sweep of notes/a52.md for the open classes of (B6) and (B5) at t = 7 and
dim V = 9.

For a class of A_u, every system either has A_n = 0 on X_1 for every n in N = ker phi, or has an
n in N outside span(u) with A_n of rank at least 1 on X_1. The first case is one instance: m42's
instance of the class (A_u fixed, m42's hints), as m57.py builds it, plus the unit clauses
A_(v_i) = 0 on the basis vectors of X_1 other than x0 for 1 <= i < kd (kd = 3 in (B6), 4 in (B5)):
2 * 21 = 42 clauses in (B6), 3 * 21 = 63 in (B5). This needs no symmetry argument. In the second
case Lemma 93 (a) lets h_1 be that n, so the class's second-matrix split needs only its
representatives of rank 1 and 2 on X_1 once the sweep instance of the class is UNSAT.

Group a (job m64a): the 51 open classes of (B6) with d <= 2 (m58.py's OPEN_M45 and OPEN_M47),
  CaDiCaL, at most CAP_A seconds each.
Group b (job m64b): the open classes of (B5) not yet split (B5_OPEN below), CaDiCaL for at most
  CAP_B seconds, then, if open, CryptoMiniSat with native XOR for CAP_B.

Parts:
    check   graded: m57.py's own check (14 checks); m58's (B6) lists (51 classes, none closed
            before, kernels and images as the pair tables, d by hand); every (B5) class has the
            kernel and image of its pair and rank 3; on one class of each group and both arms, the
            sweep instance is m42's instance plus exactly the unit clauses above, consistent.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; status by class.

Usage: python m64.py --part check|solve|grade|child [--group a|b] [--group-minutes 150]
                     [--out-dir DIR]
"""
import argparse
import json
import os
import subprocess
import sys
import time

import m57 as m
import m58
import sat_aniso as sa

T = 7
CAP_A = 150.0
CAP_B = 600.0
# The open classes of (B5) that no job has split: the d = 3 classes o000_c001, o000_c002 (split in
# m62, not yet reported), o002_c001 and o020_c000 (A_u as m55.py's CLASSES records them), and the
# three classes with d = 2 that both arms left open (m57.py's LEFTOVERS).
B5_OPEN = {
    "r3b_t7_B5_o000_c001": 266320,
    "r3b_t7_B5_o000_c002": 270368,
    "r3b_t7_B5_o002_c001": 34089040,
    "r3b_t7_B5_o020_c000": 133152,
    "r3b_t7_B5_o004_c001": 8590204928,
    "r3b_t7_B5_o005_c005": 8590207056,
    "r3b_t7_B5_o006_c000": 4295499792,
}

_base_build_plain = m.build_plain


def b5_open():
    return dict(B5_OPEN)


def x1_cols(spec):
    return [v.bit_length() - 1 for v in spec["x1"] if v != 1]


def sweep_units(spec):
    return T * len(x1_cols(spec)) * (spec["d"] - spec["p"] - 1)


def add_sweep(cnf, names, spec):
    """A_(v_i) = 0 on X_1 for 1 <= i < kd. Returns the number of clauses added."""
    A = names[0]
    n = 0
    for i in range(1, spec["d"] - spec["p"]):
        for r in range(spec["t"]):
            for c in x1_cols(spec):
                cnf.clauses.append([-A[i][r][c]])
                n += 1
    return n


def build_plain_sweep(spec):
    cnf, names, hints, units = _base_build_plain(spec)
    if spec.get("sweep0"):
        units += add_sweep(cnf, names, spec)
    return cnf, names, hints, units


def install():
    m.build_plain = build_plain_sweep


install()


def sweep_spec(base):
    sp = dict(base)
    sp["name"] = sp["name"].replace("r3b_", "r3z_", 1)
    sp["sweep0"] = True
    sp["parent"] = base["name"]
    return sp


def specs(group):
    if group == "a":
        return [sweep_spec(m58.b6_spec(n, au)) for n, au in sorted(m58.open_b6().items())]
    return [sweep_spec(m.b5_spec(n, au)) for n, au in sorted(b5_open().items())]


def plan(group):
    """[(spec, arm, cap seconds, condition)]; "open" runs the entry only if still undecided."""
    if group == "a":
        return [(sp, "cadical", CAP_A, None) for sp in specs("a")]
    out = []
    for sp in specs("b"):
        out += [(sp, "cadical", CAP_B, None), (dict(sp), "xor", CAP_B, "open")]
    return out


# ---------- check ----------

def check(out_dir):
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}}
    b6 = [m58.b6_spec(n, au) for n, au in sorted(m58.open_b6().items())]
    graded["b6_lists"] = (len(m58.OPEN_M45) == 23 and len(m58.OPEN_M47) == 28
                          and not set(m58.OPEN_M45) & set(m58.OPEN_M47)
                          and not set(m58.open_b6()) & set(m58.CLOSED_KNOWN))
    graded["b6_reps"] = all(m.kernel(s["au"], T) == m58.X1
                            and m.column_space(s["au"], T) == tuple(s["r"])
                            and sa.rank_f2(m.cols_of(s["au"], T)) == 3
                            and m.meet_d(s) == m58.HAND_D_PAIR[s["pair"]] <= 2 for s in b6)
    b5 = [m.b5_spec(n, au) for n, au in sorted(b5_open().items())]
    graded["b5_reps"] = len(b5) == len(B5_OPEN) and all(
        m.kernel(s["au"], T) == tuple(s["x1"]) and m.column_space(s["au"], T) == tuple(s["r"])
        and sa.rank_f2(m.cols_of(s["au"], T)) == 3 for s in b5)
    st["b5_d"] = {s["name"]: m.meet_d(s) for s in b5}
    probes = {}
    for key, base, hints in (("b6", b6[0], m.HAND_HINTS["B6"]), ("b5", b5[0], m.HAND_HINTS["B5"])):
        sp = sweep_spec(base)
        for arm in ("cadical", "xor"):
            c0, _, h0, u0 = m.build(base, arm)
            c1, names, h1, u1 = m.build(sp, arm)
            extra = c1.clauses[len(c0.clauses):]
            a_vars = {names[0][i][r][c] for i in range(1, sp["d"] - sp["p"]) for r in range(T)
                      for c in x1_cols(sp)}
            probes[f"{key}_{arm}"] = [c1.nv, len(c1.clauses), h1, u1, len(extra)]
            graded[f"probe_{key}_{arm}"] = (
                c1.nv == c0.nv and c1.clauses[:len(c0.clauses)] == c0.clauses
                and u0 == 0 and len(extra) == sweep_units(sp) == u1 and h1 == h0 == hints
                and all(len(cl) == 1 and cl[0] < 0 and -cl[0] in a_vars for cl in extra)
                and len({-cl[0] for cl in extra}) == len(extra) and m.units_consistent(c1))
    st["probes"] = probes
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- solving ----------

def solve_one(spec, arm, budget, out_dir):
    """m57.solve_one with this file as the child, so that the child builds the sweep instance."""
    tag = m.tag_of(spec, arm)
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--arm", arm, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({k: v for k, v in spec.items() if k != "kind"})
    res.update({"kind": spec["kind"], "arm": arm, "wall_seconds": round(time.time() - start, 2),
                "budget_seconds": round(budget, 1)})
    if res["status"] == "SAT":
        m.verify(spec, res)
    with open(os.path.join(out_dir, tag + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {tag}: {res['status']} {res['wall_seconds']} s", flush=True)
    return res


def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    counts, decided = {}, set()
    for spec, arm, cap, cond in plan(group):
        if cond == "open" and spec["name"] in decided:
            continue
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(spec, arm, min(cap, left), out_dir)
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m64-predictions.md) ----------

def grade(group, out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    rows = {}
    for spec, arm, _, _ in plan(group):
        path = os.path.join(out_dir, m.tag_of(spec, arm) + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows.setdefault(spec["parent"], {})[arm] = [s, r.get("wall_seconds"), r.get("budget_seconds")]
        if s == "SAT":
            tag = m.tag_of(spec, arm)
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    status = {n: ("UNSAT" if any(v[0] == "UNSAT" for v in a.values())
                  else "SAT" if any(v[0] == "SAT" for v in a.values()) else "open")
              for n, a in rows.items()}
    return {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows,
            "status": status, "sweep_unsat": sorted(n for n, s in status.items() if s == "UNSAT"),
            "sweep_open": sorted(n for n, s in status.items() if s == "open"),
            "any_sat_7": any(s == "SAT" for s in status.values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade", "child"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--arm")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    install()
    if args.part == "child":
        m.child(json.loads(args.spec), args.arm, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade group {args.group} all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} sweep_unsat {len(out['sweep_unsat'])} "
              f"open {out['sweep_open']}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
