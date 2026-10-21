# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m60: the next passes over (B5) at t = 7 and dim V = 9, under the rules that job m59 wrote
down before it ran (cube_groups/m59-predictions.md; notes/a49.md).

m59b split the d = 3 classes r3b_t7_B5_o001_c000 (445 instances) and o002_c000 (421) by the second
matrix A_(h_1) (Proposition 32) and closed 436 and 404 of them at CaDiCaL budgets of 10 to 20 s.
m59's rule for a split class with 1 to 30 open: CaDiCaL for 5 minutes, then, if still open,
CryptoMiniSat with native XOR for 5 minutes. The 26 open instances are split over two groups of 13
(m60a, m60b), each at most 130 minutes. What is left of each group's time goes to the next class
in the playbook's order, split the same way with CaDiCaL at most 20 s per instance:

Group a (job m60a): the 9 open of o001_c000 and 4 of o002_c000 (a025, a085, a096, a117), then the
  split of r3b_t7_B5_o032_c000 (856 instances; X_1 = span(e_0, e_1, e_2, e_6), not inside H0).
Group b (job m60b): the other 13 open of o002_c000, then the split of r3b_t7_B5_o000_c000 (671).

The split instances of a class with the most rank on X_1 run first, so that the slow kind (rank 0
on X_1, a48.md) gets the larger share of what is left. Instances are m57.py's (m42.py's encoding and
hints, m53.py's unit clauses for A_(v_1), m50.py's XOR encoding) with the representatives of m55.py,
both imported unchanged. m55's orbit roots are the smallest index in each orbit, so the
representatives do not depend on the generators drawn; the check recomputes them and compares
each of the 26 instances with the A_(h_1) that m59b ran.

Rank on X_1 is taken on the columns at X_1's own basis vectors (rank_on below), not on columns 0
to 3 (m57.rank_on_x1), which is only right when X_1 = span(e_0, ..., e_3).

Parts:
    check   graded: m57.py's own check; for each class used, m55's structure, |G|, |Adm|, closed
            action and its counts of classes by rank on X_1; every representative in Adm of
            Proposition 32 (a), of the recorded rank and distinct with its sum with A_u; rank_on
            equals m57.rank_on_x1 when X_1 = span(e_0, ..., e_3); the 26 instances as m59b ran
            them; hint and unit counts of one instance in each arm. Writes m60_reps.json.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; statuses by class and rank on X_1.

Usage: python m60.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import time

import m55
import m57 as m
import sat_aniso as sa

T, D = 7, 9
MIN_BUDGET = 10.0
NAMED_CAP = 300.0
SPLIT_CAP = 20.0
REPS_FILE = "m60_reps.json"

O1 = "r3b_t7_B5_o001_c000"
O2 = "r3b_t7_B5_o002_c000"
# The instances m59b left UNKNOWN: (class, m55 order k, m55 index, rank on X_1, A_(h_1)), copied
# from m59b's out/r3s_t7_B5_o00?_c000_aKKK__cadical.json.
REOPEN = {
    "a": ((O1, 25, 512, 0, 33554432), (O1, 85, 1024, 0, 262144), (O1, 96, 2048, 0, 2048),
          (O1, 117, 2560, 0, 33556480), (O1, 153, 8704, 0, 34078720),
          (O1, 207, 41472, 0, 34078784), (O1, 210, 131072, 0, 1048576),
          (O1, 214, 131584, 0, 34603008), (O1, 227, 163840, 0, 1048640),
          (O2, 25, 512, 0, 33554432), (O2, 85, 1024, 0, 262144), (O2, 96, 2048, 0, 2064),
          (O2, 117, 2560, 0, 33556496)),
    "b": ((O2, 153, 8704, 0, 34078720), (O2, 160, 11776, 0, 34342928), (O2, 161, 32768, 0, 64),
          (O2, 170, 33280, 0, 33554496), (O2, 207, 41472, 0, 34078784),
          (O2, 210, 131072, 0, 1048576), (O2, 214, 131584, 0, 34603008),
          (O2, 219, 131949, 1, 63964942), (O2, 223, 154112, 0, 101718064),
          (O2, 227, 163840, 0, 1048640), (O2, 231, 164352, 0, 34603072),
          (O2, 262, 524801, 1, 17217617920), (O2, 338, 532992, 0, 17213947904)),
}
# m59b's totals for the two classes: (instances, UNSAT).
M59B = {O1: (445, 436), O2: (421, 404)}
TAIL = {"a": "r3b_t7_B5_o032_c000", "b": "r3b_t7_B5_o000_c000"}
# m55's counts (m55-b5split-v1 out/m55_*.json) for every class used here.
GATE = {O1: {"orbits": 445, "by_rank": {"0": 67, "1": 268, "2": 110}},
        O2: {"orbits": 421, "by_rank": {"0": 64, "1": 257, "2": 100}},
        "r3b_t7_B5_o032_c000": {"orbits": 856, "by_rank": {"0": 18, "1": 387, "2": 451}},
        "r3b_t7_B5_o000_c000": {"orbits": 671, "by_rank": {"0": 133, "1": 416, "2": 122}}}


def mask_of(cols):
    """The t^2-bit mask (entry (r, c) at bit 7 r + c) of a matrix given by its columns."""
    return sum(((cols[c] >> r) & 1) << (T * r + c) for c in range(T) for r in range(T))


def rank_on(a1, x1):
    """The rank of A on X_1, X_1 spanned by unit vectors: the rank of A's columns at them."""
    return len(m.rref([m.column(a1, v.bit_length() - 1) for v in x1]))


def admissible(a1, au, x1, rb):
    """Adm of Proposition 32 (a): kills x0, maps H0 = span(e_0, ..., e_5) into R, rank on X_1 at
    most 2, rank at most 3, rank of A + A_u at most 3, not 0, not A_u."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(rb, cols[c]) for c in range(1, 6))
            and rank_on(a1, x1) <= 2 and sa.rank_f2(m.cols_of(a1, T)) <= 3
            and sa.rank_f2(m.cols_of(a1 ^ au, T)) <= 3 and a1 != 0 and a1 != au)


def distinct_with_au(maps, au):
    return len(set(maps) | {a ^ au for a in maps}) == 2 * len(maps)


def classes_of(group):
    out = []
    for name, *_ in REOPEN[group]:
        if name not in out:
            out.append(name)
    return out + [TAIL[group]]


def split_spec(name, k, rep):
    """As m59.split_spec."""
    pi, ci = m.pair_cls(name)
    au, x1, rb = m55.CLASSES[name]
    return {"name": f"r3s_t7_B5_o{pi:03d}_c{ci:03d}_a{k:03d}", "kind": "main", "t": T, "d": D,
            "p": 5, "pair": pi, "cls": ci, "x1": list(x1), "r": list(rb), "au": au,
            "a1": rep["a1"], "rank_x1": rep["rank_x1"], "m55_index": rep["index"],
            "size": rep["size"], "parent": name}


def tail_order(reps):
    """Indices of a class's representatives, the most rank on X_1 first, then by m55 order."""
    return sorted(range(len(reps)), key=lambda k: (-reps[k]["rank_x1"], k))


def plan(group, reps):
    """[(spec, arm, cap seconds, condition, named)]; condition "open" runs the entry only if the
    same instance is still undecided; a named entry gets its full cap, the others a share of what
    is left."""
    out = []
    for name, k, _, _, _ in REOPEN[group]:
        sp = split_spec(name, k, reps[name][k])
        out += [(sp, "cadical", NAMED_CAP, None, True), (dict(sp), "xor", NAMED_CAP, "open", True)]
    tail = TAIL[group]
    out += [(split_spec(tail, k, reps[tail][k]), "cadical", SPLIT_CAP, None, False)
            for k in tail_order(reps[tail])]
    return out


def load_reps(out_dir):
    with open(os.path.join(out_dir, REPS_FILE)) as f:
        return json.load(f)


# ---------- check ----------

def check(group, out_dir):
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}, "split": {}}
    rng, cache, reps = random.Random(55), {}, {}
    alpha_agree = True
    for name in classes_of(group):
        tag = name[10:]
        gate = GATE[name]
        r = m55.run_class(name, rng, cache)
        s = r["structure"]
        st["split"][tag] = {k: v for k, v in r.items() if k != "reps"}
        graded["split_" + tag] = (s["rank_au"] == 3 and s["ker_is_x1"] and s["im_is_r"] and s["d3"]
                                  and s["x1_in_h0"] == (tuple(r["x1"]) == m55.ALPHA)
                                  and r["group_checked"] and r["order"] == r["order_hand"]
                                  and r["valid"] == r["valid_hand"] and r["action_closed"]
                                  and r["fast_matches_slow"] and r["linear_ok"] and r["sizes_ok"]
                                  and r["orbits"] == gate["orbits"]
                                  and r["orbits_by_rank_x1"] == gate["by_rank"])
        au, x1, rb = m55.CLASSES[name]
        out = [{"index": rep["index"], "cols": rep["cols"], "a1": mask_of(rep["cols"]),
                "rank_x1": rep["rank_x1"], "size": rep["size"]} for rep in r["reps"]]
        graded["split_reps_" + tag] = (
            all(m55.cols_of(x["a1"]) == tuple(x["cols"]) and admissible(x["a1"], au, x1, rb)
                and rank_on(x["a1"], x1) == x["rank_x1"] for x in out)
            and distinct_with_au([x["a1"] for x in out], au))
        if tuple(x1) == m55.ALPHA:
            alpha_agree = alpha_agree and all(rank_on(x["a1"], x1) == m.rank_on_x1(x["a1"])
                                              for x in out)
        reps[name] = out
    graded["rank_on_alpha"] = alpha_agree
    graded["reopen"] = all(k < len(reps[name]) and reps[name][k]["index"] == idx
                           and reps[name][k]["rank_x1"] == rk and reps[name][k]["a1"] == a1
                           for name, k, idx, rk, a1 in REOPEN[group])
    # Hints and units: one re-opened instance in the XOR arm, one tail instance in the CNF arm.
    probes = {}
    name, k = REOPEN[group][0][:2]
    tail = TAIL[group]
    for key, sp, arm in (("reopen_xor", split_spec(name, k, reps[name][k]), "xor"),
                         ("tail_cadical", split_spec(tail, 0, reps[tail][0]), "cadical")):
        c, _, h, u = m.build(sp, arm)
        probes[key] = [c.nv, len(c.clauses), h, u, len(getattr(c, "xors", ()))]
        graded["probe_" + key] = (h == m.HAND_HINTS["B5"] and u == T * T and m.units_consistent(c)
                                  and (arm == "cadical" or len(c.xors) > 0))
    st["probes"] = probes
    with open(os.path.join(out_dir, REPS_FILE), "w") as f:
        json.dump(reps, f)
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- solving (as m59.run_solve) ----------

def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    entries = plan(group, load_reps(out_dir))
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
                budget = min(cap, max(min(MIN_BUDGET, left), left / (shared - done_shared)))
            res = m.solve_one(spec, arm, budget, out_dir)
        if not named:
            done_shared += 1
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m60-predictions.md) ----------

def grade(group, out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    try:
        reps = load_reps(out_dir)
    except (OSError, ValueError):
        ungraded["reps"] = "missing"
        return {"group": group, "graded": graded, "ungraded": ungraded, "rows": {}, "by": {},
                "any_sat_7": False}
    rows, by_key, status, arm_of = {}, {}, {}, {}
    for spec, arm, _, _, named in plan(group, reps):
        tag = m.tag_of(spec, arm)
        path = os.path.join(out_dir, tag + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows[tag] = [s, r.get("wall_seconds")]
        if s in ("SAT", "UNSAT"):
            status[spec["name"]] = s
            arm_of[spec["name"]] = arm
        else:
            status.setdefault(spec["name"], s)
        if s == "SAT":
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
        key = f"{'reopen' if named else 'tail'}_{spec['parent'][10:]}_rank_x1_{spec['rank_x1']}"
        if named and arm == "xor":
            continue
        by_key.setdefault(key, {})
        by_key[key][s] = by_key[key].get(s, 0) + 1
    out = {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows, "by": by_key,
           "any_sat_7": any(s == "SAT" for s, _ in rows.values())}
    out["reopen"] = {}
    for name, k, *_ in REOPEN[group]:
        n = split_spec(name, k, reps[name][k])["name"]
        out["reopen"][n] = [status.get(n), arm_of.get(n)]
    out["reopen_unsat"] = sum(s == "UNSAT" for s, _ in out["reopen"].values())
    out["reopen_open"] = [n for n, (s, _) in out["reopen"].items() if s != "UNSAT"]
    # A class is empty when m59b's UNSAT and this group's re-opened ones cover all its instances
    # (o002_c000 needs both groups: grade.json of the other job decides it).
    out["class_unsat"] = {}
    for name in dict.fromkeys(n for n, *_ in REOPEN[group]):
        total, before = M59B[name]
        here = sum(1 for n2, k, *_ in REOPEN[group] if n2 == name
                   and status.get(split_spec(name, k, reps[name][k])["name"]) == "UNSAT")
        out["class_unsat"][name] = {"total": total, "unsat": before + here,
                                    "empty": before + here == total}
    tail = TAIL[group]
    tnames = [split_spec(tail, k, r)["name"] for k, r in enumerate(reps[tail])]
    unsat = sum(status.get(n) == "UNSAT" for n in tnames)
    out["tail"] = {"name": tail, "unsat": unsat, "total": len(tnames),
                   "skipped": sum(status.get(n) == "SKIPPED" for n in tnames),
                   "open": [n for n in tnames if status.get(n) != "UNSAT"],
                   "empty": len(tnames) == GATE[tail]["orbits"] and unsat == len(tnames)}
    out["b5_closed"] = ([n for n, c in out["class_unsat"].items() if c["empty"]]
                        + ([tail] if out["tail"]["empty"] else []))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade group {args.group} all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} reopen_unsat {out.get('reopen_unsat')} "
              f"tail {out.get('tail', {}).get('unsat')}/{out.get('tail', {}).get('total')} "
              f"b5_closed {out.get('b5_closed')} by {json.dumps(out['by'], sort_keys=True)}",
              flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.group, args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
