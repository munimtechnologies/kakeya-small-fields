# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m67: the next passes over (B5) at t = 7 and dim V = 9, under the rules that jobs m63 and m64
wrote down before they ran (cube_groups/m63-predictions.md, m64-predictions.md; notes/a56.md).

What came back on 2026-10-21: m63a closed all 27 open tail instances of r3b_t7_B5_o000_c001 (the
class is empty, Corollary 67) and its 6 controls; m64b's rank-0 sweep (every element of N of rank 0
on X_1) was UNSAT for o000_c002, o020_c000, o004_c001, o005_c005 and o006_c000 (and o000_c001) and
open after both arms for o002_c001. m64's rule: a class whose sweep is UNSAT needs only its split
instances of rank 1 and 2 on X_1 (Lemma 93 (a): h_1 may then be taken of rank at least 1), and a
class whose split already ran counts its rank-0 instances as closed by the sweep. So o000_c002's 20
open rank-0 tail instances are closed, and only its 5 of rank 1 or 2 (m63's TAIL_PLAIN["b"]) are
left. That makes m63b, staged and never queued, a superset of what is needed; m67 replaces it:

Group a (job m67a): o000_c002's 5 (m63.TAIL_PLAIN["b"], m62's instances unchanged), then the split
  of r3b_t7_B5_o020_c000 (Proposition 32; 1666 classes: 51 of rank 0, 900 of rank 1, 715 of rank 2)
  without its rank-0 instances, since its sweep is UNSAT: 1615 instances.
Group b (job m67b): m63b's 7 controls (m62b's re-opened instances of o000_c000, rank 0, with the
  clauses of Lemma 93 (b)), then the whole split of r3b_t7_B5_o002_c001 (1908 classes: 251 of
  rank 0, run with Lemma 93 (b); 1182 of rank 1 and 475 of rank 2, run as m62's instances).

Named entries: CaDiCaL for at most 300 s, then, if open, CryptoMiniSat with native XOR for 300 s.
Split entries: CaDiCaL, a share of what is left, at least 10 s and at most 20 s, the most rank on
X_1 first (m60.tail_order). This is m60.py's check, with its lists pointed at m67's (install());
instances are built by m57.py, m60.py and m63.py, imported unchanged, and solved in m63.py's child,
which builds with Lemma 93 when a spec asks.

Parts:
    check   m60's graded check of the group (m57's own check; m55's structure, |G|, |Adm|, class
            counts by rank for both classes used; every representative admissible with its rank;
            the named instances recomputed; hint and unit counts); m67's: the named rows, the
            split plan (count, ranks, which carry Lemma 93), and in group b the Lemma 93 instance
            of the first rank-0 split entry against the plain one in both arms. Writes the reps.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; status and time of every instance; whether
            o000_c002 (a) and the tail class are now empty; in group b m63's speed rule over its
            13 controls (m63a's 6, recorded below, and this group's 7).

Usage: python m67.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import statistics
import time

import m63
import m62
import m60
import m57 as m

T = 7
NAMED_CAP = 300.0
SPLIT_CAP = 20.0
O0, C2 = m62.O0, m62.C2
O20 = "r3b_t7_B5_o020_c000"
O21 = "r3b_t7_B5_o002_c001"
REOPEN = {"a": tuple(m63.TAIL_PLAIN["b"]),
          "b": tuple(row for row in m62.REOPEN["b"] if row[3] == 0)}
TAIL = {"a": O20, "b": O21}
# m55's counts (m55-b5split-v1 out/m55_*.json) for every class used here.
GATE = {O0: m62.GATE[O0], C2: m62.GATE[C2],
        O20: {"orbits": 1666, "by_rank": {"0": 51, "1": 900, "2": 715}},
        O21: {"orbits": 1908, "by_rank": {"0": 251, "1": 1182, "2": 475}}}
REPS_FILE = "m67_reps.json"
# Job m64b's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {C2: "UNSAT", O20: "UNSAT", O21: "open"}
# o000_c002's split: (instances, closed before m67) = m62b's 1802 UNSAT plus the rank-0 tail
# instances m62b left open, which m64b's sweep closes (m64's rule).
M_BEFORE = {C2: (m63.M62_TAIL[C2][0], m63.M62_TAIL[C2][1] + len(m63.TAIL_OPEN["b"]))}
# m63's speed rule: CaDiCaL [status, wall seconds] of the 13 controls in m62 (m62a's and m62b's
# out/grade.json rows) and of m63a's 6 (m63a out/grade.json rows), under m63's names.
M62_CTRL = {
    "r3l_t7_B5_o032_c000_a014": ("UNSAT", 67.04), "r3l_t7_B5_o032_c000_a023": ("UNSAT", 32.63),
    "r3l_t7_B5_o032_c000_a053": ("UNSAT", 32.92), "r3l_t7_B5_o032_c000_a083": ("UNSAT", 46.62),
    "r3l_t7_B5_o000_c000_a031": ("UNKNOWN", 300.01), "r3l_t7_B5_o000_c000_a098": ("UNSAT", 76.5),
    "r3l_t7_B5_o000_c000_a123": ("UNSAT", 87.39), "r3l_t7_B5_o000_c000_a155": ("UNSAT", 107.27),
    "r3l_t7_B5_o000_c000_a162": ("UNSAT", 46.06), "r3l_t7_B5_o000_c000_a273": ("UNSAT", 101.68),
    "r3l_t7_B5_o000_c000_a277": ("UNSAT", 70.19), "r3l_t7_B5_o000_c000_a308": ("UNSAT", 52.08),
    "r3l_t7_B5_o000_c000_a363": ("UNSAT", 35.67)}
M63A_CTRL = {
    "r3l_t7_B5_o032_c000_a014": ("UNSAT", 32.67), "r3l_t7_B5_o032_c000_a023": ("UNSAT", 10.45),
    "r3l_t7_B5_o032_c000_a053": ("UNSAT", 11.1), "r3l_t7_B5_o032_c000_a083": ("UNSAT", 44.05),
    "r3l_t7_B5_o000_c000_a031": ("UNSAT", 21.43), "r3l_t7_B5_o000_c000_a098": ("UNSAT", 4.33)}


def install():
    """m63's builder (Lemma 93 when a spec asks), with m60's lists pointed at m67's."""
    m63.install()
    m60.REOPEN, m60.TAIL, m60.GATE, m60.REPS_FILE = REOPEN, TAIL, GATE, REPS_FILE
    m60.M59B = {O0: (671, 671), C2: M_BEFORE[C2]}


install()


def drop_rank0(group):
    return SWEEP[TAIL[group]] == "UNSAT"


def named_spec(group, name, k, rep):
    """Group a: m62's instance unchanged; group b: with Lemma 93 (b), as m63b would have run it."""
    return m63.spec93(name, k, rep) if group == "b" else m60.split_spec(name, k, rep)


def tail_spec(name, k, rep):
    return m63.spec93(name, k, rep) if rep["rank_x1"] == 0 else m60.split_spec(name, k, rep)


def plan(group, reps):
    """[(spec, arm, cap seconds, condition, named)] as m60.plan."""
    out = []
    for name, k, *_ in REOPEN[group]:
        sp = named_spec(group, name, k, reps[name][k])
        out += [(sp, "cadical", NAMED_CAP, None, True), (dict(sp), "xor", NAMED_CAP, "open", True)]
    tail = TAIL[group]
    for k in m60.tail_order(reps[tail]):
        rep = reps[tail][k]
        if rep["rank_x1"] == 0 and drop_rank0(group):
            continue
        out.append((tail_spec(tail, k, rep), "cadical", SPLIT_CAP, None, False))
    return out


def planned_tail(group):
    by = GATE[TAIL[group]]["by_rank"]
    return by["1"] + by["2"] + (0 if drop_rank0(group) else by["0"])


# ---------- check ----------

def probe93(name, k, rep):
    """The Lemma 93 instance is the plain one plus exactly lemma93_units negative unit clauses on
    A_(v_2), ..., A_(v_(kd-1)) at X_1's columns, in both arms; returns ({arm: ok}, {arm: counts})."""
    ok, counts = {}, {}
    for arm in ("cadical", "xor"):
        base = m60.split_spec(name, k, rep)
        sp = m63.spec93(name, k, rep)
        c0, _, h0, u0 = m.build(base, arm)
        c1, names, h1, u1 = m.build(sp, arm)
        extra = c1.clauses[len(c0.clauses):]
        a_vars = {names[0][i][r][c] for i in range(2, sp["d"] - sp["p"]) for r in range(T)
                  for c in m63.x1_cols(sp)}
        counts[arm] = [c1.nv, len(c1.clauses), h1, u1, len(extra)]
        ok[arm] = (c1.nv == c0.nv and c1.clauses[:len(c0.clauses)] == c0.clauses
                   and len(extra) == m63.lemma93_units(sp) == u1 - u0
                   and h1 == h0 == m.HAND_HINTS["B5"]
                   and all(len(cl) == 1 and cl[0] < 0 and -cl[0] in a_vars for cl in extra)
                   and len({-cl[0] for cl in extra}) == len(extra) and m.units_consistent(c1)
                   and len(getattr(c1, "xors", ())) == len(getattr(c0, "xors", ())))
    return ok, counts


def check(group, out_dir):
    install()
    st = m60.check(group, out_dir)
    graded = st["graded"]
    reps = m60.load_reps(out_dir)
    rows = REOPEN[group]
    want_rank = (lambda rk: rk in (1, 2)) if group == "a" else (lambda rk: rk == 0)
    graded["m67_named"] = (len(rows) == (5 if group == "a" else 7)
                           and all(want_rank(r[3]) for r in rows)
                           and len({r[1] for r in rows}) == len(rows)
                           and m63.rows_match(reps, rows))
    if group == "a":
        total, before = M_BEFORE[C2]
        graded["m67_c2_counts"] = (
            m63.M62_TAIL[C2] == (1827, 1802) and before + len(rows) == total
            and len(m63.TAIL_OPEN["b"]) + len(m63.TAIL_PLAIN["b"]) == 1827 - 1802
            and all(r[0] == C2 and r[3] == 0 for r in m63.TAIL_OPEN["b"])
            and all(r[0] == C2 for r in rows) and SWEEP[C2] == "UNSAT")
    p = plan(group, reps)
    tail_specs = [e[0] for e in p if not e[4]]
    graded["m67_tail_plan"] = (
        len(tail_specs) == planned_tail(group) == len({s["name"] for s in tail_specs})
        and all(s["parent"] == TAIL[group] for s in tail_specs)
        and all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail_specs)
        and (not drop_rank0(group) or all(s["rank_x1"] > 0 for s in tail_specs))
        and [s["rank_x1"] for s in tail_specs] == sorted((s["rank_x1"] for s in tail_specs),
                                                        reverse=True))
    if group == "b":
        k0 = next(k for k in m60.tail_order(reps[O21]) if reps[O21][k]["rank_x1"] == 0)
        ok, counts = probe93(O21, k0, reps[O21][k0])
        for arm, v in ok.items():
            graded["m67_probe93_" + arm] = v
        st["m67_probe93"] = counts
    st["m67_plan"] = {"named": len(rows), "tail": len(tail_specs),
                      "tail_lemma93": sum(1 for s in tail_specs if s.get("lemma93"))}
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- solving (m60.run_solve with m63's child) ----------

def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    entries = plan(group, m60.load_reps(out_dir))
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
            res = m63.solve_one(spec, arm, budget, out_dir)
        if not named:
            done_shared += 1
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m67-predictions.md) ----------

def speed(new):
    """m63's speed rule over its 13 controls. new: {name: (status, wall)} of this group's CaDiCaL
    arm. Ratios only where m62 and m63 both decided in CaDiCaL; an instance m62 decided and m63
    did not counts as slower by its lower bound."""
    times = dict(M63A_CTRL)
    times.update(new)
    ratios, undecided = {}, {}
    for n, (s62, t62) in M62_CTRL.items():
        if n not in times or s62 != "UNSAT":
            continue
        s, t = times[n]
        if s == "UNSAT":
            ratios[n] = round(t / t62, 3)
        else:
            undecided[n] = round(t / t62, 3)
    slower2 = sorted(n for n, r in list(ratios.items()) + list(undecided.items()) if r > 2)
    med = round(statistics.median(ratios.values()), 3) if ratios else None
    if med is None:
        rule = None
    elif med < 0.5 and not slower2:
        rule = "adopt"
    elif med <= 1 and not slower2:
        rule = "keep_for_open"
    else:
        rule = "fact_only"
    return {"controls": sum(1 for n in M62_CTRL if n in times), "ratios": ratios,
            "undecided": undecided, "median": med, "slower_2x": slower2, "rule": rule}


def grade(group, out_dir):
    install()
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
        reps = m60.load_reps(out_dir)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
        return {"group": group, "graded": graded, "ungraded": ungraded, "rows": {},
                "any_sat_7": False}
    rows, status, specs = {}, {}, {}
    for spec, arm, _, _, named in plan(group, reps):
        specs[spec["name"]] = (spec, named)
        path = os.path.join(out_dir, m.tag_of(spec, arm) + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows.setdefault(spec["name"], {})[arm] = [s, r.get("wall_seconds"), r.get("budget_seconds")]
        if s == "SAT":
            tag = m.tag_of(spec, arm)
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    for n in specs:
        a = rows.get(n, {})
        vals = [v[0] for v in a.values()]
        status[n] = ("UNSAT" if "UNSAT" in vals else "SAT" if "SAT" in vals
                     else "SKIPPED" if vals and all(v == "SKIPPED" for v in vals)
                     else "open" if vals else "missing")
    named = [n for n, (_, nm) in specs.items() if nm]
    tail = [n for n, (_, nm) in specs.items() if not nm]
    by_rank = {}
    for n in tail:
        key = str(specs[n][0]["rank_x1"])
        by_rank.setdefault(key, {})
        by_rank[key][status[n]] = by_rank[key].get(status[n], 0) + 1
    t_unsat = sum(status[n] == "UNSAT" for n in tail)
    out = {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows,
           "named": {n: status[n] for n in named},
           "named_unsat": sum(status[n] == "UNSAT" for n in named),
           "tail": {"name": TAIL[group], "planned": len(tail), "unsat": t_unsat,
                    "open": [n for n in tail if status[n] != "UNSAT"],
                    "skipped": sum(status[n] in ("SKIPPED", "missing") for n in tail),
                    "by_rank": by_rank, "rank0_dropped_by_sweep": drop_rank0(group),
                    "empty": len(tail) == planned_tail(group) and t_unsat == len(tail)},
           "any_sat_7": any(s == "SAT" for s in status.values())}
    if group == "a":
        total, before = M_BEFORE[C2]
        here = out["named_unsat"]
        out["c2"] = {"name": C2, "total": total, "unsat": before + here,
                     "empty": before + here == total}
    else:
        new = {n: tuple(rows[n]["cadical"][:2]) for n in named
               if n in rows and "cadical" in rows[n]}
        out["speed"] = speed(new)
    out["b5_closed"] = (([C2] if out.get("c2", {}).get("empty") else [])
                        + ([TAIL[group]] if out["tail"]["empty"] else []))
    return out


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
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade group {args.group} all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} named_unsat {out.get('named_unsat')} "
              f"tail {json.dumps({k: v for k, v in out.get('tail', {}).items() if k != 'open'})} "
              f"open {out.get('tail', {}).get('open')} c2 {json.dumps(out.get('c2'))} "
              f"speed {json.dumps(out.get('speed'))} b5_closed {out.get('b5_closed')}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.group, args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
