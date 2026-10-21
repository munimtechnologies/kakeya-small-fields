# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m78: the split of the last (B5) class not yet split, and the one instance m75a left open, at
t = 7 and dim V = 9, d = dim(X_1 n R) = 2 (Proposition 34, notes/a58.md; matched by job m74, notes/
a64.md; cube_groups/m78-predictions.md, notes/a66.md).

Group a (job m78a) and group b (job m78b): r3b_t7_B5_o005_c005 (|G| = 512; 7615 classes: 895 of
  rank 0, 4624 of rank 1, 2096 of rank 2). Its rank-0 sweep was UNSAT (job m64b), so by Lemma 93
  (a) only its 6720 split instances of rank 1 and 2 on X_1 are needed. In m75's order (the most
  rank on X_1 first, then m55 order) group a runs the first 3360 and group b the last 3360.
Group r (job m78r): r3s_t7_B5_o004_c001_a1240 (rank 1 on X_1, m55 index 262274), the one instance
  of m75a's 2084 that was not UNSAT (UNKNOWN at its 10 s budget), with 5 minutes of CaDiCaL and
  then, only if it is still open, 5 minutes of XOR (as m60's re-opened instances).

Everything is m75.py with its lists rebound (as m70-m77 rebind m69): m75's check, unchanged, runs
with this job's plan (one entry per instance) and class lists, and this file adds two graded checks
of its own. A group never decides a class by itself: o005_c005 is empty only if both halves are all
UNSAT, and o004_c001 only if m78r's instance is UNSAT (m75a's other 2083 were). Split instances:
CaDiCaL, a share of what is left, at least 10 s and at most 20 s; instances not reached are SKIPPED
and stay open.

Parts:
    check   graded: m75's check of the group's class (m57's own check; m55's structure with d = 2,
            |G| = Proposition 34 (c), |Adm|, class counts by rank equal to m74's run; every root
            admissible, of its rank, distinct with its sum with A_u; the plan; hints and units of
            the first instance in both arms); for a and b the ranks in the half; for r that m55's
            root at order 1240 is the instance m75a left open. Writes m78_reps.json.
    solve   the group's plan in order (as m60.run_solve).
    grade   graded checks and every SAT verified; status and time of every instance; whether every
            instance of the group is UNSAT.

Usage: python m78.py --part check|solve|grade [--group a|b|r] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import statistics
import time

import m75
import m60
import m57 as m

T = 7
O4, O5 = m75.O4, m75.O5
HALF = 3360
RERUN_CAP = 300.0
# m74's run (m74-prop34count-v1 stdout, 2026-10-21) for o005_c005.
GATE_O5 = {"order": 512, "orbits": 7615, "by_rank": {"0": 895, "1": 4624, "2": 2096}}
# (class, m55 order k, m55 index, rank on X_1, A_(h_1)) of the instance m75a left UNKNOWN, copied
# from m75a's out/r3s_t7_B5_o004_c001_a1240__cadical.json.
REOPEN = (O4, 1240, 262274, 1, 134381568)
TAILS = {"a": O5, "b": O5, "r": O4}
PLANNED = {"a": HALF, "b": HALF, "r": 1}
REPS_FILE = "m78_reps.json"


def install():
    """m75's lists become this job's; m75.install sets m74's classes on m55."""
    m75.install()
    m75.TAIL = dict(TAILS)
    m75.GATE[O5] = GATE_O5
    m75.SWEEP[O5] = "UNSAT"
    m75.REPS_FILE = REPS_FILE
    m75.plan = first_arms
    m75.planned = lambda name: HALF if name == O5 else 1


def split_order(reps):
    """o005_c005's roots of rank 1 and 2 on X_1, in m75's order."""
    rs = reps[O5]
    return [k for k in m60.tail_order(rs) if rs[k]["rank_x1"] > 0]


def plan(group, reps):
    """[(spec, arm, cap seconds, condition, named)] as m60.plan; condition "open" runs the entry
    only if the same instance is still undecided."""
    if group == "r":
        name, k = REOPEN[:2]
        sp = m60.split_spec(name, k, reps[name][k])
        return [(sp, "cadical", RERUN_CAP, None, True), (dict(sp), "xor", RERUN_CAP, "open", True)]
    ks = split_order(reps)
    ks = ks[:HALF] if group == "a" else ks[HALF:]
    return [(m60.split_spec(O5, k, reps[O5][k]), "cadical", m75.SPLIT_CAP, None, False)
            for k in ks]


def first_arms(group, reps):
    """The plan with one entry per instance (its first arm), as m75's check expects."""
    seen, out = set(), []
    for e in plan(group, reps):
        if e[0]["name"] not in seen:
            seen.add(e[0]["name"])
            out.append(e)
    return out


def half_ranks(group):
    """Ranks on X_1 in a half: rank 2 first, so group a holds every rank-2 root."""
    r2 = GATE_O5["by_rank"]["2"]
    if group == "a":
        return {2: min(HALF, r2), 1: HALF - min(HALF, r2)}
    return {2: max(0, r2 - HALF), 1: HALF - max(0, r2 - HALF)}


install()


# ---------- check ----------

def check(group, out_dir):
    install()
    st = m75.check(group, out_dir)
    graded = st["graded"]
    reps = m75.load_reps(out_dir)
    if group == "r":
        name, k, idx, rk, a1 = REOPEN
        rs = reps[name]
        graded["reopen"] = (k < len(rs) and rs[k]["index"] == idx and rs[k]["rank_x1"] == rk
                            and rs[k]["a1"] == a1)
    else:
        ranks = [e[0]["rank_x1"] for e in plan(group, reps)]
        want = half_ranks(group)
        graded["half_ranks"] = (len(split_order(reps)) == 2 * HALF
                                and {r: ranks.count(r) for r in (2, 1)} == want)
    st["graded"] = graded
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- solving (as m60.run_solve) ----------

def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    entries = plan(group, m75.load_reps(out_dir))
    shared = sum(1 for e in entries if not e[4])
    counts, decided, done_shared = {}, set(), 0
    for spec, arm, cap, cond, named in entries:
        if cond == "open" and spec["name"] in decided:
            continue
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            if named:
                budget = min(cap, left)
            else:
                budget = min(cap, max(min(m60.MIN_BUDGET, left), left / (shared - done_shared)))
            res = m.solve_one(spec, arm, budget, out_dir)
        if not named:
            done_shared += 1
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m78-predictions.md) ----------

def grade(group, out_dir):
    install()
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
        reps = m75.load_reps(out_dir)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
        return {"group": group, "graded": graded, "ungraded": ungraded, "rows": {},
                "any_sat_7": False, "part": {}}
    rows, status, wall, specs = {}, {}, {}, []
    for spec, arm, _, _, _ in plan(group, reps):
        n = spec["name"]
        if n not in status:
            specs.append(spec)
            status[n] = "missing"
        path = os.path.join(out_dir, m.tag_of(spec, arm) + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        tag = m.tag_of(spec, arm)
        rows[tag] = [s, r.get("wall_seconds"), r.get("budget_seconds")]
        if s == "SAT":
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
        if status[n] not in ("SAT", "UNSAT"):
            status[n], wall[n] = s, r.get("wall_seconds")
    by_rank = {}
    for sp in specs:
        key = str(sp["rank_x1"])
        by_rank.setdefault(key, {})
        by_rank[key][status[sp["name"]]] = by_rank[key].get(status[sp["name"]], 0) + 1
    unsat = [sp for sp in specs if status[sp["name"]] == "UNSAT"]
    walls = [wall[sp["name"]] for sp in unsat]
    slow = sorted(unsat, key=lambda sp: -wall[sp["name"]])[:10]
    return {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows,
            "part": {"name": TAILS[group], "planned": len(specs), "unsat": len(unsat),
                     "open": [sp["name"] for sp in specs if status[sp["name"]] != "UNSAT"],
                     "skipped": sum(status[sp["name"]] in ("SKIPPED", "missing") for sp in specs),
                     "by_rank": by_rank, "rank0_dropped_by_sweep": True,
                     "median_unsat_wall": round(statistics.median(walls), 2) if walls else None,
                     "max_unsat_wall": max(walls) if walls else None,
                     "slowest_ten_m55_index": [sp["m55_index"] for sp in slow],
                     "all_unsat": len(specs) == PLANNED[group] and len(unsat) == len(specs)},
            "any_sat_7": any(s == "SAT" for s in status.values())}


def summary_line(out):
    part = {k: v for k, v in out.get("part", {}).items() if k != "open"}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} part {json.dumps(part, sort_keys=True)} "
            f"open {json.dumps(out.get('part', {}).get('open', [])[:30])}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group", choices=["a", "b", "r"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    install()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(summary_line(out), flush=True)
    else:
        st = check(args.group, args.out_dir)
        print(f"check: {json.dumps({k: v for k, v in st.items() if k != 'm57'}, sort_keys=True)}",
              flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
