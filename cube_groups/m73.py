# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m73: the 19 split instances of (B6) that job m71a left open, re-run under m71's rule for 1 to
30 open in a class, and the second-matrix splits of five more classes with d = 1 whose rank-0 sweep
was UNSAT (Proposition 33, notes/a52.md), at t = 7 and dim V = 9 (cube_groups/m71-predictions.md,
m73-predictions.md; notes/a61.md).

What came back on 2026-10-21: m71a's check held (37 graded, all true) and nothing was SAT. All 21
re-runs of o004_c001 and o006_c001 were UNSAT by CaDiCaL within 300 s (at most 239.5 s; the XOR arm
was never needed), so both classes are empty (Corollaries 74 and 75). The splits of o008_c002 and
o010_c002 (d = 1, sweep open) closed every instance of rank 1 and 2 on X_1 and left 13 and 6 of
rank 0 (with Lemma 93 (b)) open at 10 s; the median UNSAT wall time was 1.17 and 1.12 s.

Group a (job m73a): the 13 of o008_c002, then the splits of o009_c003 and o007_c001 (their
  instances of rank 1 and 2: 1200 + 1344).
Group b (job m73b): the 6 of o010_c002, then the splits of o007_c004, o007_c007 and o009_c000
  (1344 + 1344 + 1888).
Each of the 19: CaDiCaL for at most 300 s, then, if open, CryptoMiniSat with native XOR for 300 s.
Instances not reached are SKIPPED and stay open.

Everything else is m69.py's, imported unchanged: the instances (m57.py's encoding and hints, the
unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of m66.py, the plan
of the tails, the shared budget (10 to 20 s per split instance), the child process and the grading
of the split classes. This file sets m69's lists, puts the 19 in front of m69's plan, and checks
them as m72.py checks its 80: their classes against m66's run, each root recomputed by m66.py
against the one m71a ran (index, map, rank on X_1, orbit size), Lemma 93 on every one, and hint and
unit counts in both arms.

Parts:
    check   m69.py's check of the tail classes, then the group's re-runs as above. Writes m73_reps.json.
    solve   m69.py's solve with this plan.
    grade   m69.py's grade, and whether o008_c002 or o010_c002 is now empty.

Usage: python m73.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random

import m69 as b
import m66
import m57 as m

T = 7
# The 19 that m71a left open (UNKNOWN at 10 s), copied from its out/<name>__cadical.json:
# (class, k, rank on X_1, m66 index, orbit size, A_(v_1)).
OPEN_M71 = (
    ("r3b_t7_B6_o008_c002", 34, 0, 512, 4, 549755813888),
    ("r3b_t7_B6_o008_c002", 103, 0, 1536, 8, 554050781184),
    ("r3b_t7_B6_o008_c002", 129, 0, 2048, 4, 2048),
    ("r3b_t7_B6_o008_c002", 151, 0, 2560, 4, 549755815936),
    ("r3b_t7_B6_o008_c002", 214, 0, 4608, 8, 1649267441664),
    ("r3b_t7_B6_o008_c002", 680, 0, 13824, 8, 1662152343552),
    ("r3b_t7_B6_o008_c002", 757, 0, 16384, 8, 4096),
    ("r3b_t7_B6_o008_c002", 769, 0, 16896, 8, 549755817984),
    ("r3b_t7_B6_o008_c002", 902, 0, 26112, 8, 562640719872),
    ("r3b_t7_B6_o008_c002", 953, 0, 32768, 4, 2199023255552),
    ("r3b_t7_B6_o008_c002", 965, 0, 35328, 4, 2748779071488),
    ("r3b_t7_B6_o008_c002", 1015, 0, 131072, 2, 8192),
    ("r3b_t7_B6_o008_c002", 1016, 0, 133632, 4, 549755824128),
    ("r3b_t7_B6_o010_c002", 34, 0, 512, 4, 549755813888),
    ("r3b_t7_B6_o010_c002", 103, 0, 1536, 8, 554050781200),
    ("r3b_t7_B6_o010_c002", 151, 0, 2560, 4, 549755815936),
    ("r3b_t7_B6_o010_c002", 757, 0, 16384, 8, 4096),
    ("r3b_t7_B6_o010_c002", 769, 0, 16896, 8, 549755817984),
    ("r3b_t7_B6_o010_c002", 1015, 0, 131072, 2, 8192),
)
NAMED_CLASSES = {"a": ("r3b_t7_B6_o008_c002",), "b": ("r3b_t7_B6_o010_c002",)}
NAMED_COUNT = {"a": 13, "b": 6}
# m71a's split of the two classes (out/grade.json "classes", 2026-10-21): (planned, UNSAT).
M71 = {"r3b_t7_B6_o008_c002": (1021, 1008), "r3b_t7_B6_o010_c002": (1021, 1015)}
# m66's run for the two (m71.py's GATE, which m71a's check confirmed).
NAMED_GATE = {
    "r3b_t7_B6_o008_c002": {"d": 1, "order": 768, "valid": 176126, "orbits": 1021,
                            "by_rank": {"0": 69, "1": 476, "2": 476}},
    "r3b_t7_B6_o010_c002": {"d": 1, "order": 768, "valid": 176126, "orbits": 1021,
                            "by_rank": {"0": 69, "1": 476, "2": 476}},
}
TAILS = {"a": ("r3b_t7_B6_o009_c003", "r3b_t7_B6_o007_c001"),
         "b": ("r3b_t7_B6_o007_c004", "r3b_t7_B6_o007_c007", "r3b_t7_B6_o009_c000")}
# Job m64a's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {"r3b_t7_B6_o009_c003": "UNSAT", "r3b_t7_B6_o007_c001": "UNSAT",
         "r3b_t7_B6_o007_c004": "UNSAT", "r3b_t7_B6_o007_c007": "UNSAT",
         "r3b_t7_B6_o009_c000": "UNSAT"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o009_c003": {"d": 1, "order": 576, "valid": 176126, "orbits": 1287,
                            "by_rank": {"0": 87, "1": 600, "2": 600}},
    "r3b_t7_B6_o007_c001": {"d": 1, "order": 1344, "valid": 176126, "orbits": 1599,
                            "by_rank": {"0": 255, "1": 896, "2": 448}},
    "r3b_t7_B6_o007_c004": {"d": 1, "order": 1344, "valid": 176126, "orbits": 1599,
                            "by_rank": {"0": 255, "1": 896, "2": 448}},
    "r3b_t7_B6_o007_c007": {"d": 1, "order": 1344, "valid": 176126, "orbits": 1599,
                            "by_rank": {"0": 255, "1": 896, "2": 448}},
    "r3b_t7_B6_o009_c000": {"d": 1, "order": 384, "valid": 176126, "orbits": 2023,
                            "by_rank": {"0": 135, "1": 944, "2": 944}},
}
# Classes of (B6) closed by the second-matrix split (jobs m69a, m69b, m70a, m71a), and the classes
# split by m72 or re-run here: none may be split as a tail.
CLOSED_SPLIT = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011",
                "r3b_t7_B6_o009_c008", "r3b_t7_B6_o011_c002", "r3b_t7_B6_o004_c001",
                "r3b_t7_B6_o006_c001")
SPLIT_ELSEWHERE = ("r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000", "r3b_t7_B6_o008_c004",
                   "r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003", "r3b_t7_B6_o003_c004",
                   "r3b_t7_B6_o012_c009", "r3b_t7_B6_o012_c004") + tuple(M71)
REPS_FILE = "m73_reps.json"

_plan69 = b.plan


def named_name(name, k, rank_x1):
    """m69's name of the split instance of a class at root k."""
    pi, ci = m.pair_cls(name)
    return f"{'r3l' if rank_x1 == 0 else 'r3s'}_t7_B6_o{pi:03d}_c{ci:03d}_a{k:04d}"


def named_rows(group):
    return [row for row in OPEN_M71 if row[0] in NAMED_CLASSES[group]]


def named_specs(group, reps):
    """The group's re-runs as m71a ran them: m69's split instance at root k, with Lemma 93 (b) when
    of rank 0."""
    return [b.split_spec(name, k, reps[name][k], rank_x1 == 0)
            for name, k, rank_x1, _, _, _ in named_rows(group)]


def plan(group, reps):
    """The re-runs (each CaDiCaL, then XOR if still open, at the full cap), then m69's plan of the
    tails."""
    out = []
    for sp in named_specs(group, reps):
        out += [(dict(sp), "cadical", b.NAMED_CAP, None, True),
                (dict(sp), "xor", b.NAMED_CAP, "open", True)]
    return out + _plan69(group, reps)


def install():
    """m69's lists become this job's and its plan this file's; m57.build keeps Lemma 93 (b)."""
    b.install()
    b.NAMED = {"a": (), "b": ()}
    b.TAILS, b.SWEEP, b.GATE, b.REPS_FILE = TAILS, SWEEP, GATE, REPS_FILE
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


def check_named(group, out_dir, st):
    graded, probes = st["graded"], st["probes"]
    reps = b.load_reps(out_dir)
    rng = random.Random(73)
    for name in NAMED_CLASSES[group]:
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
        len(named) == NAMED_COUNT[group] and len({sp["name"] for sp in named}) == len(named)
        and set(NAMED_GATE) == set(M71) == set(NAMED_CLASSES["a"]) | set(NAMED_CLASSES["b"])
        and by_class == {n: M71[n][0] - M71[n][1] for n in NAMED_CLASSES[group]}
        and all(sp["rank_x1"] == 0 for sp in named))
    graded["named_maps"] = all(
        sp["name"] == named_name(name, k, rk) and sp["parent"] == name
        and sp["m66_index"] == index and sp["size"] == size and sp["a1"] == a1
        and sp["rank_x1"] == rk == b.rank_on(a1, b.X1)
        and bool(sp.get("lemma93")) == (rk == 0)
        and b.admissible_b6(a1, sp["au"], b.r_of(name), NAMED_GATE[name]["d"])
        for sp, (name, k, rk, index, size, a1) in zip(named, rows))
    first_l = next(sp for sp in named if sp.get("lemma93"))
    for arm in ("cadical", "xor"):
        c, _, h, u = m.build(dict(first_l), arm)
        probes["named_l_" + arm] = [c.nv, len(c.clauses), h, u]
        graded["probe_named_l_" + arm] = (h == m.HAND_HINTS["B6"] and u == T * T + 21
                                          and m.units_consistent(c))
    ok, counts = b.probe93(first_l)
    for arm, v in ok.items():
        graded["probe93_named_" + arm] = v and b.lemma93_units(first_l) == 21
    probes["lemma93_named"] = counts
    st["plan"]["named"] = len(named)


def check(group, out_dir):
    install()
    b.plan = _plan69
    try:
        st = b.check(group, out_dir)
    finally:
        b.plan = plan
    graded = st["graded"]
    graded["not_split_before"] = not set(TAILS[group]) & (set(CLOSED_SPLIT) | set(SPLIT_ELSEWHERE))
    check_named(group, out_dir, st)
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m73-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
    if "named" not in out:
        return out
    named_cls = {}
    for name in NAMED_CLASSES[group]:
        total, before = M71[name]
        mine = [named_name(n, k, rk) for n, k, rk, _, _, _ in OPEN_M71 if n == name]
        here = sum(out["named"].get(x) == "UNSAT" for x in mine)
        named_cls[name] = {"total": total, "unsat": before + here,
                           "empty": before + here == total,
                           "open": [x for x in mine if out["named"].get(x) != "UNSAT"]}
    out["named_classes"] = named_cls
    out["b6_closed"] = out["b6_closed"] + [n for n, c in named_cls.items() if c["empty"]]
    out["named_open"] = [n for n, s in out["named"].items() if s != "UNSAT"]
    walls = [min(v[1] for v in out["rows"][n].values() if v[0] == "UNSAT")
             for n, s in out["named"].items() if s == "UNSAT"]
    out["named_max_unsat_wall"] = max(walls) if walls else None
    out["named_unsat_by_arm"] = {arm: sum(1 for n, s in out["named"].items() if s == "UNSAT"
                                          and out["rows"][n].get(arm, [None])[0] == "UNSAT")
                                 for arm in ("cadical", "xor")}
    return out


def summary_line(out):
    cls = {n[10:]: {k: v for k, v in c.items() if k != "open"} for n, c in out.get("classes", {}).items()}
    opened = {n[10:]: c["open"][:30] for n, c in out.get("classes", {}).items()}
    named = {n[10:]: c for n, c in out.get("named_classes", {}).items()}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} named_unsat {out.get('named_unsat')} "
            f"named_unsat_by_arm {json.dumps(out.get('named_unsat_by_arm'))} "
            f"named_open {out.get('named_open')} named_max_unsat_wall "
            f"{out.get('named_max_unsat_wall')} named_classes {json.dumps(named, sort_keys=True)} "
            f"b6_closed {out.get('b6_closed')} classes {json.dumps(cls, sort_keys=True)} "
            f"open {json.dumps(opened, sort_keys=True)}")


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
