# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m75: the second-matrix split of two of the three classes of (B5) still open at t = 7 and
dim V = 9, all with d = dim(X_1 n R) = 2 (Proposition 34, notes/a58.md; matched by job m74, notes/
a64.md; cube_groups/m75-predictions.md, notes/a65.md).

Each class had a UNSAT rank-0 sweep in job m64b, so by Lemma 93 (a) h_1 may be taken of rank at
least 1 on X_1 and only the split instances of rank 1 and 2 are needed (as in m67a):

Group a (job m75a): r3b_t7_B5_o004_c001 (|G| = 2048; 2367 classes: 283 of rank 0, 1448 of rank 1,
  636 of rank 2): 2084 instances.
Group b (job m75b): r3b_t7_B5_o006_c000 (|G| = 1024; 4133 classes: 479, 2528, 1126): 3654.
The third, o005_c005 (6720 instances), is left for two later groups.

Everything is imported unchanged: m74.py's class list and hand orders (set on m55.py), m55.py's
group, Adm and orbit roots (smallest index in each orbit, so they do not depend on the generators
drawn), m60.py's split_spec, admissible, rank_on and tail_order (the most rank on X_1 first), and
m57.py's encoding, hints, unit clauses for A_(v_1), child and solve_one. No instance here has rank 0
on X_1, so nothing uses Lemma 93 (b). m60.py's own check grades R inside X_1 (d = 3), so this file
has its own, which grades d = 2 as m74 did. Split instances: CaDiCaL, a share of what is left, at
least 10 s and at most 20 s; instances not reached are SKIPPED and stay open.

Parts:
    check   graded: m57.py's own check; m55's structure (rank 3, kernel X_1, image R, d = 2, X_1 =
            span(e_0, ..., e_3) inside H0), |G| = Proposition 34 (c), |Adm| = 405566 with m55's
            own checks, the class counts by rank on X_1 equal to m74's run; every root admissible,
            of its recorded rank (both rank functions), distinct with its sum with A_u; the plan;
            hint and unit counts of the first instance in both arms. Writes m75_reps.json.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; status and time of every instance; whether the
            class is now empty.

Usage: python m75.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import statistics
import time

import m74
import m60
import m55
import m57 as m

T = 7
SPLIT_CAP = 20.0
ADM = 405566
O4 = "r3b_t7_B5_o004_c001"
O5 = "r3b_t7_B5_o005_c005"
O6 = "r3b_t7_B5_o006_c000"
TAIL = {"a": O4, "b": O6}
# m74's run (m74-prop34count-v1 stdout, 2026-10-21) for every class split here.
GATE = {O4: {"order": 2048, "orbits": 2367, "by_rank": {"0": 283, "1": 1448, "2": 636}},
        O6: {"order": 1024, "orbits": 4133, "by_rank": {"0": 479, "1": 2528, "2": 1126}}}
# Job m64b's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {O4: "UNSAT", O6: "UNSAT"}
REPS_FILE = "m75_reps.json"


def install():
    """m74's three classes and hand orders become m55's."""
    m74.install()


install()


def planned(name):
    by = GATE[name]["by_rank"]
    return by["1"] + by["2"]


def load_reps(out_dir):
    with open(os.path.join(out_dir, REPS_FILE)) as f:
        return json.load(f)


def plan(group, reps):
    """[(spec, arm, cap seconds, condition, named)] as m60.plan: the class's roots of rank 1 and 2
    on X_1, the most rank first; rank 0 is dropped because the sweep was UNSAT."""
    tail = TAIL[group]
    rs = reps[tail]
    return [(m60.split_spec(tail, k, rs[k]), "cadical", SPLIT_CAP, None, False)
            for k in m60.tail_order(rs) if rs[k]["rank_x1"] > 0]


# ---------- check ----------

def check(group, out_dir):
    install()
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}}
    name = TAIL[group]
    gate = GATE[name]
    au, x1, rb = m55.CLASSES[name]
    r = m55.run_class(name, random.Random(75), {})
    s = r["structure"]
    st["split"] = {k: v for k, v in r.items() if k != "reps"}
    graded["split_structure"] = (s["rank_au"] == 3 and s["ker_is_x1"] and s["im_is_r"]
                                 and not s["d3"] and s["x1_in_h0"]
                                 and tuple(r["x1"]) == m55.ALPHA
                                 and m74.meet_dim(tuple(x1), tuple(rb)) == m74.HAND_D)
    graded["split_group"] = (r["group_checked"]
                             and r["order"] == r["order_hand"] == gate["order"]
                             == m74.HAND_ORDER[name])
    graded["split_valid"] = (r["valid"] == r["valid_hand"] == ADM and r["action_closed"]
                             and r["fast_matches_slow"] and r["linear_ok"] and r["sizes_ok"])
    graded["split_counts"] = (r["orbits"] == gate["orbits"] == sum(gate["by_rank"].values())
                              and r["orbits_by_rank_x1"] == gate["by_rank"])
    out = [{"index": rep["index"], "cols": rep["cols"], "a1": m60.mask_of(rep["cols"]),
            "rank_x1": rep["rank_x1"], "size": rep["size"]} for rep in r["reps"]]
    graded["split_reps"] = (
        all(m55.cols_of(x["a1"]) == tuple(x["cols"]) and m60.admissible(x["a1"], au, x1, rb)
            and m60.rank_on(x["a1"], x1) == x["rank_x1"] == m.rank_on_x1(x["a1"]) for x in out)
        and m60.distinct_with_au([x["a1"] for x in out], au))
    reps = {name: out}
    p = plan(group, reps)
    specs = [e[0] for e in p]
    ranks = [sp["rank_x1"] for sp in specs]
    graded["plan"] = (SWEEP[name] == "UNSAT" and len(specs) == planned(name)
                      and len({sp["name"] for sp in specs}) == len(specs)
                      and all(sp["parent"] == name and sp["p"] == 5 for sp in specs)
                      and all(rk > 0 for rk in ranks) and ranks == sorted(ranks, reverse=True))
    probes = {}
    for arm in ("cadical", "xor"):
        c, _, h, u = m.build(dict(specs[0]), arm)
        probes[arm] = [c.nv, len(c.clauses), h, u, len(getattr(c, "xors", ()))]
        graded["probe_" + arm] = (h == m.HAND_HINTS["B5"] and u == T * T and m.units_consistent(c)
                                  and (arm == "cadical" or len(c.xors) > 0))
    st["probes"] = probes
    st["plan"] = {"tail": len(specs), "by_rank": {str(k): ranks.count(k) for k in (1, 2)}}
    with open(os.path.join(out_dir, REPS_FILE), "w") as f:
        json.dump(reps, f)
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- solving (m67.run_solve without named entries, with m57's child) ----------

def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    entries = plan(group, load_reps(out_dir))
    counts = {}
    for k, (spec, arm, cap, _, _) in enumerate(entries):
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            budget = min(cap, max(min(m60.MIN_BUDGET, left), left / (len(entries) - k)))
            res = m.solve_one(spec, arm, budget, out_dir)
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m75-predictions.md) ----------

def grade(group, out_dir):
    install()
    graded, ungraded = {}, {}
    tail = TAIL[group]
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
        reps = load_reps(out_dir)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
        return {"group": group, "graded": graded, "ungraded": ungraded, "rows": {},
                "any_sat_7": False, "b5_closed": []}
    rows, status, specs = {}, {}, []
    for spec, arm, _, _, _ in plan(group, reps):
        specs.append(spec)
        n = spec["name"]
        path = os.path.join(out_dir, m.tag_of(spec, arm) + ".json")
        if not os.path.exists(path):
            status[n] = "missing"
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows[n] = [s, r.get("wall_seconds"), r.get("budget_seconds")]
        status[n] = s
        if s == "SAT":
            tag = m.tag_of(spec, arm)
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    by_rank = {}
    for sp in specs:
        key = str(sp["rank_x1"])
        by_rank.setdefault(key, {})
        by_rank[key][status[sp["name"]]] = by_rank[key].get(status[sp["name"]], 0) + 1
    unsat = [sp for sp in specs if status[sp["name"]] == "UNSAT"]
    walls = [rows[sp["name"]][1] for sp in unsat]
    slow = sorted(unsat, key=lambda sp: -rows[sp["name"]][1])[:10]
    empty = len(specs) == planned(tail) and len(unsat) == len(specs)
    return {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows,
            "tail": {"name": tail, "planned": len(specs), "unsat": len(unsat),
                     "open": [sp["name"] for sp in specs if status[sp["name"]] != "UNSAT"],
                     "skipped": sum(status[sp["name"]] in ("SKIPPED", "missing") for sp in specs),
                     "by_rank": by_rank, "rank0_dropped_by_sweep": True,
                     "median_unsat_wall": round(statistics.median(walls), 2) if walls else None,
                     "max_unsat_wall": max(walls) if walls else None,
                     "slowest_ten_m55_index": [sp["m55_index"] for sp in slow],
                     "empty": empty},
            "any_sat_7": any(s == "SAT" for s in status.values()),
            "b5_closed": [tail] if empty else []}


def summary_line(out):
    tail = {k: v for k, v in out.get("tail", {}).items() if k != "open"}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} b5_closed {out.get('b5_closed')} "
            f"tail {json.dumps(tail, sort_keys=True)} "
            f"open {json.dumps(out.get('tail', {}).get('open', [])[:30])}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
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
