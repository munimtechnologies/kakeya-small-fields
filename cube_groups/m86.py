# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m86: the 49 split instances of (B6) that jobs m84a, m84b and m85a left open in their tails,
re-run under m79's rule for 1 to 30 open in a class, and the second-matrix splits of two more
classes whose rank-0 sweep was open (Proposition 33, notes/a52.md): the last class with d = 1 and
the first of the six with d = 2 still open, at t = 7 and dim V = 9 (cube_groups/m86-predictions.md;
notes/a71.md).

What came back on 2026-10-22: the checks of m84a, m84b and m85a held (24, 24 and 32 graded, all
true) and nothing was SAT. m85a's 12 re-runs of o010_c004 were all UNSAT in CaDiCaL (slowest
71.2 s), so o010_c004 is empty. The splits of o009_c007 and o010_c000 (m84) and o010_c007 (m85a
tail), d = 1 with the sweep open, left 14, 22 and 13 instances open at 10 to 20 s, all of rank 0
(with Lemma 93 (b)); every instance of rank 1 and 2 was UNSAT. The median UNSAT wall was 1.02 s in
all three.

Group a (job m86a): the 14 of o009_c007, then the split of o010_c001
  (d = 1, |G| = 192, 3839: 255 of rank 0 with Lemma 93 (b), 1792 of rank 1, 1792 of rank 2).
Group b (job m86b): the 22 of o010_c000 and the 13 of o010_c007, then the split of o005_c002
  (d = 2, |G| = 1024, 1069: 75 of rank 0 with Lemma 93 (b), 520 of rank 1, 474 of rank 2).
Each of the 49: CaDiCaL for at most 300 s, then, if open, CryptoMiniSat with native XOR for 300 s.
One tail class per group, as in m72, m82, m83 and m85, because the re-runs come first; instances
not reached are SKIPPED and stay open.

Everything else is m69.py's, imported unchanged, as in m85.py: the instances (m57.py's encoding
and hints, the unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of
m66.py, the plan of the tails, the shared budget (10 to 20 s per split instance), the child process
and the grading of the split classes. This file sets m69's lists, puts the 49 in front of m69's
plan, and checks them as m85.py checks its 24: their classes against m66's run, each root
recomputed by m66.py against the one recorded (index, map, rank on X_1, orbit size), Lemma 93 on
every rank-0 one, and hint and unit counts in both arms.

Parts:
    check   m69.py's check of the tail class, then the group's re-runs as above. Writes m86_reps.json.
    solve   m69.py's solve with this plan.
    grade   m69.py's grade, and whether o009_c007, o010_c000 and o010_c007 are now empty.

Usage: python m86.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random

import m69 as b
import m66
import m57 as m

T = 7
# The 49 that m84a, m84b and m85a left open (UNKNOWN at 10 to 20 s), copied from their
# out/<name>__cadical.json: (class, k, rank on X_1, m66 index, orbit size, A_(v_1)).
OPEN_PREV = (
    ("r3b_t7_B6_o009_c007", 128, 0, 1536, 2, 554050781184),
    ("r3b_t7_B6_o009_c007", 1520, 0, 18944, 2, 549755820080),
    ("r3b_t7_B6_o009_c007", 1578, 0, 19968, 2, 554050787376),
    ("r3b_t7_B6_o009_c007", 1984, 0, 27136, 2, 558345754672),
    ("r3b_t7_B6_o009_c007", 2274, 0, 32256, 2, 1662152349744),
    ("r3b_t7_B6_o009_c007", 2303, 0, 32768, 2, 2199023255552),
    ("r3b_t7_B6_o009_c007", 2947, 0, 51200, 2, 2199023261744),
    ("r3b_t7_B6_o009_c007", 2974, 0, 52736, 2, 2753074042928),
    ("r3b_t7_B6_o009_c007", 3556, 0, 147968, 2, 549755826272),
    ("r3b_t7_B6_o009_c007", 3586, 0, 151040, 2, 554050795632),
    ("r3b_t7_B6_o009_c007", 3711, 0, 163840, 2, 2199023263808),
    ("r3b_t7_B6_o009_c007", 3783, 0, 176128, 2, 3307124826176),
    ("r3b_t7_B6_o009_c007", 3807, 0, 180224, 2, 2199023267936),
    ("r3b_t7_B6_o009_c007", 3814, 0, 183808, 2, 2753074051184),
    ("r3b_t7_B6_o010_c000", 42, 0, 512, 2, 549755813888),
    ("r3b_t7_B6_o010_c000", 128, 0, 1536, 2, 554050781200),
    ("r3b_t7_B6_o010_c000", 214, 0, 2560, 2, 549755815936),
    ("r3b_t7_B6_o010_c000", 300, 0, 3584, 2, 554050783248),
    ("r3b_t7_B6_o010_c000", 386, 0, 4608, 2, 1649267441664),
    ("r3b_t7_B6_o010_c000", 687, 0, 8192, 2, 8589934624),
    ("r3b_t7_B6_o010_c000", 716, 0, 8704, 2, 558345748512),
    ("r3b_t7_B6_o010_c000", 745, 0, 9216, 2, 12884901936),
    ("r3b_t7_B6_o010_c000", 832, 0, 10752, 2, 558345750560),
    ("r3b_t7_B6_o010_c000", 919, 0, 12288, 2, 1108101562400),
    ("r3b_t7_B6_o010_c000", 1006, 0, 13824, 2, 1662152343600),
    ("r3b_t7_B6_o010_c000", 1710, 0, 23040, 2, 1649267447808),
    ("r3b_t7_B6_o010_c000", 1839, 0, 24576, 2, 8589938720),
    ("r3b_t7_B6_o010_c000", 1868, 0, 25088, 2, 558345752608),
    ("r3b_t7_B6_o010_c000", 1984, 0, 27136, 2, 558345754656),
    ("r3b_t7_B6_o010_c000", 2013, 0, 27648, 2, 12884908080),
    ("r3b_t7_B6_o010_c000", 2071, 0, 28672, 2, 1108101566496),
    ("r3b_t7_B6_o010_c000", 2322, 0, 33280, 2, 2748779069440),
    ("r3b_t7_B6_o010_c000", 2474, 0, 37376, 2, 3848290697216),
    ("r3b_t7_B6_o010_c000", 2616, 0, 41472, 2, 2757369004064),
    ("r3b_t7_B6_o010_c000", 3385, 0, 74752, 2, 30064771184),
    ("r3b_t7_B6_o010_c000", 3410, 0, 77312, 2, 579820587120),
    ("r3b_t7_B6_o010_c007", 28, 0, 512, 2, 549755813888),
    ("r3b_t7_B6_o010_c007", 57, 0, 1024, 4, 4294967312),
    ("r3b_t7_B6_o010_c007", 158, 0, 3072, 4, 4294969360),
    ("r3b_t7_B6_o010_c007", 201, 0, 4096, 4, 1099511627776),
    ("r3b_t7_B6_o010_c007", 249, 0, 5632, 2, 1653562408976),
    ("r3b_t7_B6_o010_c007", 316, 0, 7680, 2, 1653562411024),
    ("r3b_t7_B6_o010_c007", 335, 0, 8192, 4, 8589934624),
    ("r3b_t7_B6_o010_c007", 807, 0, 20480, 4, 1099511631872),
    ("r3b_t7_B6_o010_c007", 894, 0, 22016, 4, 1653562413072),
    ("r3b_t7_B6_o010_c007", 923, 0, 24576, 4, 8589938720),
    ("r3b_t7_B6_o010_c007", 1293, 0, 36864, 4, 3298534883328),
    ("r3b_t7_B6_o010_c007", 1321, 0, 39936, 2, 3302829852688),
    ("r3b_t7_B6_o010_c007", 1693, 0, 66560, 4, 21474836560),
)
NAMED_CLASSES = {"a": ("r3b_t7_B6_o009_c007",),
                 "b": ("r3b_t7_B6_o010_c000", "r3b_t7_B6_o010_c007")}
NAMED_COUNT = {"a": 14, "b": 35}
# Re-runs per rank on X_1 in each group.
NAMED_RANKS = {"a": {0: 14, 1: 0, 2: 0}, "b": {0: 35, 1: 0, 2: 0}}
# The earlier split of the three classes (m84a, m84b and m85a out/grade.json "classes",
# 2026-10-22): (planned, UNSAT).
BEFORE = {"r3b_t7_B6_o009_c007": (3839, 3825), "r3b_t7_B6_o010_c000": (3839, 3817),
          "r3b_t7_B6_o010_c007": (2023, 2010)}
# m66's run for the three (m84.py's and m85.py's GATE, which their checks confirmed).
NAMED_GATE = {
    "r3b_t7_B6_o009_c007": {"d": 1, "order": 192, "valid": 176126, "orbits": 3839,
                            "by_rank": {"0": 255, "1": 1792, "2": 1792}},
    "r3b_t7_B6_o010_c000": {"d": 1, "order": 192, "valid": 176126, "orbits": 3839,
                            "by_rank": {"0": 255, "1": 1792, "2": 1792}},
    "r3b_t7_B6_o010_c007": {"d": 1, "order": 384, "valid": 176126, "orbits": 2023,
                            "by_rank": {"0": 135, "1": 944, "2": 944}},
}
TAILS = {"a": ("r3b_t7_B6_o010_c001",), "b": ("r3b_t7_B6_o005_c002",)}
# Job m64a's sweep instance of each class (logs/run-03-python.stdout.txt): UNKNOWN at 150 s.
SWEEP = {"r3b_t7_B6_o010_c001": "open", "r3b_t7_B6_o005_c002": "open"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o010_c001": {"d": 1, "order": 192, "valid": 176126, "orbits": 3839,
                            "by_rank": {"0": 255, "1": 1792, "2": 1792}},
    "r3b_t7_B6_o005_c002": {"d": 2, "order": 1024, "valid": 176126, "orbits": 1069,
                            "by_rank": {"0": 75, "1": 520, "2": 474}},
}
# Classes of (B6) closed by the second-matrix split (jobs m69a to m85a), and the classes re-run here
# or split or re-run by m85b: none may be split as a tail.
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
                "r3b_t7_B6_o010_c005", "r3b_t7_B6_o010_c004")
SPLIT_ELSEWHERE = ("r3b_t7_B6_o010_c006", "r3b_t7_B6_o010_c008") + tuple(BEFORE)
REPS_FILE = "m86_reps.json"

_plan69 = b.plan


def named_name(name, k, rank_x1):
    """m69's name of the split instance of a class at root k."""
    pi, ci = m.pair_cls(name)
    return f"{'r3l' if rank_x1 == 0 else 'r3s'}_t7_B6_o{pi:03d}_c{ci:03d}_a{k:04d}"


def named_rows(group):
    return [row for row in OPEN_PREV if row[0] in NAMED_CLASSES[group]]


def named_specs(group, reps):
    """The group's re-runs as they ran before: m69's split instance at root k, with Lemma 93 (b)
    when of rank 0."""
    return [b.split_spec(name, k, reps[name][k], rank_x1 == 0)
            for name, k, rank_x1, _, _, _ in named_rows(group)]


def plan(group, reps):
    """The re-runs (each CaDiCaL, then XOR if still open, at the full cap), then m69's plan of the
    tail."""
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
    rng = random.Random(86)
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
        and set(NAMED_GATE) == set(BEFORE) == set(NAMED_CLASSES["a"]) | set(NAMED_CLASSES["b"])
        and by_class == {n: BEFORE[n][0] - BEFORE[n][1] for n in NAMED_CLASSES[group]}
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


# ---------- grading (pre-registered in m86-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
    if "named" not in out:
        return out
    named_cls = {}
    for name in NAMED_CLASSES[group]:
        total, before = BEFORE[name]
        mine = [named_name(n, k, rk) for n, k, rk, _, _, _ in OPEN_PREV if n == name]
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
