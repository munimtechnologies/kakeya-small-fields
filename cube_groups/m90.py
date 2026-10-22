# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m90: the 32 split instances of (B6) that job m88a-v2 left open in o005_c003, re-run under
m79's rule (cube_groups/m90-predictions.md; notes/a75.md). Re-runs only: no class is split here.

What came back on 2026-10-22: m88a-v2's checks held (24 graded, all true) and nothing was SAT. Its
split of o005_c003 (d = 2, 1961 instances, sweep open) left 32 open at 10 to 20 s: 16 of rank 0 on
X_1 (with Lemma 93 (b)) and 16 of rank 1, none SKIPPED. 32 is more than 30, so under
m88-predictions.md's rule they are re-run in two jobs of 16, split by place in m66's order.

Group a (job m90a): the first 16 of o005_c003 in m66's order (a0015 to a0846: 11 of rank 1, 5 of
  rank 0).
Group b (job m90b): the last 16 (a0927 to a1960: 11 of rank 0, 5 of rank 1).
Each: CaDiCaL for at most 300 s, then, if open, CryptoMiniSat with native XOR for 300 s.
The class is empty only when both groups close all of theirs; each group's grade reports its part.

This file is m89.py with new lists (its plan, check and grade copied unchanged), and everything
but the lists, the plan and the check is m69.py's, imported unchanged: the instances (m57.py's encoding and hints,
the unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of m66.py, the
child process and the status of each entry. m69.check needs at least one tail class, so this file
has m89's own check: m57.py's 14 checks as m69.check runs them, then the re-runs as m87.py checks
its 45 (their class against m66's run, each root recomputed by m66.py against the one recorded,
Lemma 93 on every rank-0 one, hint and unit counts in both arms).

Parts:
    check   as above. Writes m90_reps.json and check.json.
    solve   m69.py's solve with this plan.
    grade   m69.py's grade, and which of the group's re-runs closed.

Usage: python m90.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import time

import m69 as b
import m66
import m57 as m

T = 7
# The 32 that m88a-v2 left open (UNKNOWN at 10 to 20 s), copied from its out/<name>__cadical.json:
# (class, k, rank on X_1, m66 index, orbit size, A_(v_1)).
OPEN_PREV = {
    "a": (
        ("r3b_t7_B6_o005_c003", 15, 1, 18, 32, 98304),
        ("r3b_t7_B6_o005_c003", 33, 1, 36, 32, 774),
        ("r3b_t7_B6_o005_c003", 42, 1, 45, 32, 1610613510),
        ("r3b_t7_B6_o005_c003", 51, 1, 54, 32, 99078),
        ("r3b_t7_B6_o005_c003", 60, 1, 63, 32, 1610711814),
        ("r3b_t7_B6_o005_c003", 118, 1, 384, 8, 132104),
        ("r3b_t7_B6_o005_c003", 175, 1, 575, 32, 5905679110),
        ("r3b_t7_B6_o005_c003", 240, 0, 1024, 4, 262144),
        ("r3b_t7_B6_o005_c003", 350, 0, 1536, 4, 4295229440),
        ("r3b_t7_B6_o005_c003", 379, 1, 1581, 32, 5905842950),
        ("r3b_t7_B6_o005_c003", 554, 1, 2587, 32, 5905680400),
        ("r3b_t7_B6_o005_c003", 625, 0, 3072, 4, 264208),
        ("r3b_t7_B6_o005_c003", 714, 1, 3593, 32, 5905844240),
        ("r3b_t7_B6_o005_c003", 767, 0, 4096, 4, 8589934592),
        ("r3b_t7_B6_o005_c003", 817, 0, 5120, 2, 8590196736),
        ("r3b_t7_B6_o005_c003", 846, 1, 5659, 32, 14495875072),
    ),
    "b": (
        ("r3b_t7_B6_o005_c003", 927, 0, 7168, 4, 8590198800),
        ("r3b_t7_B6_o005_c003", 1141, 0, 20480, 4, 8589938720),
        ("r3b_t7_B6_o005_c003", 1150, 0, 21504, 2, 8590200864),
        ("r3b_t7_B6_o005_c003", 1156, 1, 22043, 32, 14495879200),
        ("r3b_t7_B6_o005_c003", 1521, 0, 36864, 4, 25769803776),
        ("r3b_t7_B6_o005_c003", 1534, 0, 37376, 4, 30064771072),
        ("r3b_t7_B6_o005_c003", 1564, 0, 38400, 4, 30065033216),
        ("r3b_t7_B6_o005_c003", 1570, 1, 38427, 32, 31675744256),
        ("r3b_t7_B6_o005_c003", 1599, 1, 39451, 32, 31675484176),
        ("r3b_t7_B6_o005_c003", 1605, 0, 39936, 4, 25770067984),
        ("r3b_t7_B6_o005_c003", 1801, 1, 50715, 32, 23085813792),
        ("r3b_t7_B6_o005_c003", 1811, 1, 51739, 32, 23085553712),
        ("r3b_t7_B6_o005_c003", 1885, 0, 65536, 4, 1048576),
        ("r3b_t7_B6_o005_c003", 1921, 0, 69632, 2, 8590983168),
        ("r3b_t7_B6_o005_c003", 1926, 0, 72704, 4, 8591247376),
        ("r3b_t7_B6_o005_c003", 1960, 0, 94208, 2, 8591511584),
    ),
}
NAMED_CLASSES = ("r3b_t7_B6_o005_c003",)
NAMED_COUNT = {"a": 16, "b": 16}
# Re-runs per class and per rank on X_1 in each group.
NAMED_PER_CLASS = {"a": {"r3b_t7_B6_o005_c003": 16}, "b": {"r3b_t7_B6_o005_c003": 16}}
NAMED_RANKS = {"a": {0: 5, 1: 11, 2: 0}, "b": {0: 11, 1: 5, 2: 0}}
# m88a-v2's split of the class (out/grade.json "classes", 2026-10-22): (planned, UNSAT).
BEFORE = {"r3b_t7_B6_o005_c003": (1961, 1929)}
# m66's run for the class (m87.py's / m88.py's GATE, which m88a-v2's check confirmed).
NAMED_GATE = {
    "r3b_t7_B6_o005_c003": {"d": 2, "order": 512, "valid": 176126, "orbits": 1961,
                            "by_rank": {"0": 135, "1": 944, "2": 882}},
}
# Classes of (B6) closed by the second-matrix split and its re-runs (jobs m69a to m89b): m89.py's
# 41 and o003_c001, o005_c001 (m89a, m89b). The class re-run here may not be among them.
CLOSED_SPLIT = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011",
                "r3b_t7_B6_o009_c008", "r3b_t7_B6_o011_c002", "r3b_t7_B6_o004_c001",
                "r3b_t7_B6_o006_c001", "r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000",
                "r3b_t7_B6_o008_c004", "r3b_t7_B6_o003_c004", "r3b_t7_B6_o012_c009",
                "r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003", "r3b_t7_B6_o012_c004",
                "r3b_t7_B6_o008_c002", "r3b_t7_B6_o009_c003", "r3b_t7_B6_o007_c001",
                "r3b_t7_B6_o010_c002", "r3b_t7_B6_o007_c004", "r3b_t7_B6_o007_c007",
                "r3b_t7_B6_o009_c000", "r3b_t7_B6_o009_c002", "r3b_t7_B6_o009_c009",
                "r3b_t7_B6_o012_c001", "r3b_t7_B6_o009_c001", "r3b_t7_B6_o009_c004",
                "r3b_t7_B6_o008_c000", "r3b_t7_B6_o008_c001", "r3b_t7_B6_o008_c003",
                "r3b_t7_B6_o009_c005", "r3b_t7_B6_o009_c006", "r3b_t7_B6_o010_c003",
                "r3b_t7_B6_o010_c005", "r3b_t7_B6_o010_c004", "r3b_t7_B6_o010_c006",
                "r3b_t7_B6_o009_c007", "r3b_t7_B6_o010_c000", "r3b_t7_B6_o010_c007",
                "r3b_t7_B6_o010_c008", "r3b_t7_B6_o005_c002", "r3b_t7_B6_o003_c001",
                "r3b_t7_B6_o005_c001")
REPS_FILE = "m90_reps.json"

_plan69 = b.plan


def named_name(name, k, rank_x1):
    """m69's name of the split instance of a class at root k."""
    pi, ci = m.pair_cls(name)
    return f"{'r3l' if rank_x1 == 0 else 'r3s'}_t7_B6_o{pi:03d}_c{ci:03d}_a{k:04d}"


def named_rows(group):
    return list(OPEN_PREV[group])


def named_specs(group, reps):
    """The group's re-runs as they ran before: m69's split instance at root k, with Lemma 93 (b)
    when of rank 0."""
    return [b.split_spec(name, k, reps[name][k], rank_x1 == 0)
            for name, k, rank_x1, _, _, _ in named_rows(group)]


def plan(group, reps):
    """The re-runs only, each CaDiCaL, then XOR if still open, at the full cap."""
    out = []
    for sp in named_specs(group, reps):
        out += [(dict(sp), "cadical", b.NAMED_CAP, None, True),
                (dict(sp), "xor", b.NAMED_CAP, "open", True)]
    return out


def install():
    """m69's lists become empty (no tail, no m69 named entry) and its plan this file's; m57.build
    keeps Lemma 93 (b)."""
    b.install()
    b.NAMED = {"a": (), "b": ()}
    b.TAILS = {"a": (), "b": ()}
    b.SWEEP, b.GATE, b.REPS_FILE = {}, {}, REPS_FILE
    b.plan = plan


install()


# ---------- check ----------

def class_ok(r, gate):
    """m69's graded split_ condition: m66's record of a class against its run."""
    s = r["structure"]
    return ("error" not in r and s["rank_au"] == 3 and s["ker_is_x1"] and s["image_is_r"]
            and s["d"] == s["d_hand"] == gate["d"] and r["group_checked"]
            and r["order"] == r["order_hand"] == gate["order"]
            and r["valid"] == r["valid_hand"] == gate["valid"] and r["action_closed"]
            and r["tables_match"] and r["sizes_ok"] and r["orbits"] == gate["orbits"]
            and r["orbits_by_rank_x1"] == gate["by_rank"])


def reps_ok(name, rr, gate):
    """m69's graded split_reps_ condition: every root admissible, of its rank, with its index."""
    au, rb = m66.classes()[name], b.r_of(name)
    mp = m66.Maps(rb)
    return (len(rr) == gate["orbits"]
            and [x["index"] for x in rr] == sorted(x["index"] for x in rr)
            and all(mp.index(tuple(x["cols"])) == x["index"]
                    and m66.cols_of_mask(x["a1"]) == tuple(x["cols"])
                    and b.admissible_b6(x["a1"], au, rb, gate["d"])
                    and b.rank_on(x["a1"], b.X1) == x["rank_x1"] == mp.rank_x1(x["index"])
                    for x in rr)
            and b.distinct_with_au([x["a1"] for x in rr], au))


def lists_ok():
    """Both groups together are exactly the open instances of m88a-v2's split, once each."""
    rows = OPEN_PREV["a"] + OPEN_PREV["b"]
    per = {}
    for row in rows:
        per[row[0]] = per.get(row[0], 0) + 1
    return (len({(r[0], r[1]) for r in rows}) == len(rows)
            and set(NAMED_GATE) == set(BEFORE) == set(NAMED_CLASSES)
            and per == {n: total - unsat for n, (total, unsat) in BEFORE.items()}
            and not set(NAMED_CLASSES) & set(CLOSED_SPLIT)
            and all(sum(NAMED_PER_CLASS[g].values()) == NAMED_COUNT[g]
                    == sum(NAMED_RANKS[g].values()) for g in ("a", "b")))


def check_named(group, out_dir, st):
    graded, probes = st["graded"], st["probes"]
    reps = {}
    rng = random.Random(90)
    names = sorted({row[0] for row in named_rows(group)})
    for name in names:
        gate = NAMED_GATE[name]
        tag = name[10:]
        r, rr = b.class_reps(name, rng)
        st["split"][tag] = r
        graded["named_split_" + tag] = class_ok(r, gate)
        graded["named_split_reps_" + tag] = reps_ok(name, rr, gate)
        reps[name] = rr
    with open(os.path.join(out_dir, REPS_FILE), "w") as f:
        json.dump(reps, f)
    named = named_specs(group, reps)
    rows = named_rows(group)
    by_class = {}
    for sp in named:
        by_class[sp["parent"]] = by_class.get(sp["parent"], 0) + 1
    graded["named_list"] = (
        lists_ok() and len(named) == NAMED_COUNT[group]
        and len({sp["name"] for sp in named}) == len(named)
        and by_class == NAMED_PER_CLASS[group]
        and all(sp["rank_x1"] in (0, 1, 2) for sp in named)
        and all(sum(sp["rank_x1"] == rk for sp in named) == c
                for rk, c in NAMED_RANKS[group].items()))
    graded["named_maps"] = all(
        sp["name"] == named_name(name, k, rk) and sp["parent"] == name
        and sp["m66_index"] == index and sp["size"] == size and sp["a1"] == a1
        and sp["rank_x1"] == rk == b.rank_on(a1, b.X1)
        and bool(sp.get("lemma93")) == (rk == 0)
        and b.admissible_b6(a1, sp["au"], b.r_of(name), NAMED_GATE[name]["d"])
        for sp, (name, k, rk, index, size, a1) in zip(named, rows))
    p = plan(group, reps)
    graded["plan"] = (len(p) == 2 * len(named) and all(e[4] for e in p)
                      and [e[1] for e in p] == ["cadical", "xor"] * len(named)
                      and [e[3] for e in p] == [None, "open"] * len(named)
                      and all(e[2] == b.NAMED_CAP for e in p))
    first_l = next(sp for sp in named if sp.get("lemma93"))
    for arm in ("cadical", "xor"):
        c, _, h, u = m.build(dict(first_l), arm)
        probes["named_l_" + arm] = [c.nv, len(c.clauses), h, u]
        graded["probe_named_l_" + arm] = (h == m.HAND_HINTS["B6"] and u == T * T + 21
                                          and m.units_consistent(c))
    first_s = next((sp for sp in named if not sp.get("lemma93")), None)
    if first_s is not None:
        for arm in ("cadical", "xor"):
            c, _, h, u = m.build(dict(first_s), arm)
            probes["named_s_" + arm] = [c.nv, len(c.clauses), h, u]
            graded["probe_named_s_" + arm] = (h == m.HAND_HINTS["B6"] and u == T * T
                                              and m.units_consistent(c))
    ok, counts = b.probe93(first_l)
    for arm, v in ok.items():
        graded["probe93_named_" + arm] = v and b.lemma93_units(first_l) == 21
    probes["lemma93_named"] = counts
    st["plan"]["named"] = len(named)


def check(group, out_dir):
    """m57.py's own check as m69.check runs it, then the group's re-runs."""
    install()
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}, "split": {}, "probes": {},
          "plan": {}, "graded": graded}
    check_named(group, out_dir, st)
    st["seconds"] = round(time.time() - start, 1)
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m90-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
    if "named" not in out:
        return out
    named_cls = {}
    for name in NAMED_CLASSES:
        mine = [named_name(n, k, rk) for n, k, rk, _, _, _ in named_rows(group) if n == name]
        if not mine:
            continue
        here = sum(out["named"].get(x) == "UNSAT" for x in mine)
        named_cls[name] = {"total": BEFORE[name][0], "unsat_before": BEFORE[name][1],
                           "rerun_here": len(mine), "unsat_here": here,
                           "open": [x for x in mine if out["named"].get(x) != "UNSAT"]}
    out["named_classes"] = named_cls
    out["named_open"] = [n for n, s in out["named"].items() if s != "UNSAT"]
    walls = [min(v[1] for v in out["rows"][n].values() if v[0] == "UNSAT")
             for n, s in out["named"].items() if s == "UNSAT"]
    out["named_max_unsat_wall"] = max(walls) if walls else None
    out["named_unsat_by_arm"] = {arm: sum(1 for n, s in out["named"].items() if s == "UNSAT"
                                          and out["rows"][n].get(arm, [None])[0] == "UNSAT")
                                 for arm in ("cadical", "xor")}
    return out


def summary_line(out):
    named = {n[10:]: c for n, c in out.get("named_classes", {}).items()}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} named_unsat {out.get('named_unsat')} "
            f"named_unsat_by_arm {json.dumps(out.get('named_unsat_by_arm'))} "
            f"named_open {out.get('named_open')} named_max_unsat_wall "
            f"{out.get('named_max_unsat_wall')} named_classes {json.dumps(named, sort_keys=True)}")


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
        b.run_solve(args.group, args.group_minutes * 60, args.out_dir)
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
