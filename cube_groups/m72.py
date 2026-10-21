# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m72: the 80 split instances of (B6) that job m70 left open, re-run under m70's rule for 1 to
30 open in a class, and the second-matrix splits of o012_c009 and o012_c004 (d = 0; Proposition 33,
notes/a52.md), at t = 7 and dim V = 9 (cube_groups/m70-predictions.md, m72-predictions.md;
notes/a60.md).

What came back on 2026-10-21: m70a's and m70b's checks held (37 and 30 graded, all true) and nothing
was SAT. All 27 re-runs of o002_c001 of (B5) were UNSAT (26 by CaDiCaL within 300 s, 1 by XOR), so
that class is empty (Corollary 72), and all 924 split instances of o011_c002 of (B6) (d = 0, sweep
UNSAT) were UNSAT, so that class is empty (Corollary 73). The other six classes split (d = 1 or 2,
sweep open) closed every instance of rank 1 and 2 on X_1 and left 80 of rank 0 (with Lemma 93 (b))
open at 10 to 20 s: o004_c000 10, o006_c000 7, o008_c004 12, o003_c002 20, o003_c003 17,
o003_c004 14. The median UNSAT wall time was 1.02 to 1.12 s.

Group a (job m72a): the 43 of o004_c000, o006_c000, o008_c004 and o003_c004, then the split of
  o012_c009 (sweep UNSAT: its 1200 instances of rank 1 and 2).
Group b (job m72b): the 37 of o003_c002 and o003_c003, then the split of o012_c004 (1840).
Each of the 80: CaDiCaL for at most 300 s, then, if open, CryptoMiniSat with native XOR for 300 s.
One tail class per group, not four or five, because the re-runs may take most of the 150 minutes;
instances not reached are SKIPPED and stay open.

Everything else is m69.py's, imported unchanged: the instances (m57.py's encoding and hints, the
unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of m66.py, the plan
of the tails, the shared budget (10 to 20 s per split instance), the child process and the grading
of the split classes. This file sets m69's lists, puts the 80 in front of m69's plan, and checks
them as m71.py checks its 21: their classes against m66's run, each root recomputed by m66.py
against the one m70 ran (index, map, rank on X_1, orbit size), Lemma 93 on every one, and hint and
unit counts in both arms.

Parts:
    check   m69.py's check of the tail class, then the group's re-runs as above. Writes m72_reps.json.
    solve   m69.py's solve with this plan.
    grade   m69.py's grade, and which of the six classes are now empty.

Usage: python m72.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random

import m69 as b
import m66
import m57 as m

T = 7
# The 80 that m70 left open (UNKNOWN at 10 s, o006_c000 at 20 s), copied from its
# out/<name>__cadical.json: (class, k, rank on X_1, m66 index, orbit size, A_(v_1)).
OPEN_M70 = (
    ("r3b_t7_B6_o004_c000", 31, 0, 512, 2, 4294967296),
    ("r3b_t7_B6_o004_c000", 58, 0, 1024, 6, 262144),
    ("r3b_t7_B6_o004_c000", 133, 0, 1536, 6, 4295229440),
    ("r3b_t7_B6_o004_c000", 199, 0, 4096, 6, 8589934592),
    ("r3b_t7_B6_o004_c000", 238, 0, 4608, 6, 12884901888),
    ("r3b_t7_B6_o004_c000", 402, 0, 8192, 12, 524288),
    ("r3b_t7_B6_o004_c000", 430, 0, 9216, 12, 786432),
    ("r3b_t7_B6_o004_c000", 514, 0, 12288, 12, 8590458880),
    ("r3b_t7_B6_o004_c000", 523, 0, 12800, 12, 12885426176),
    ("r3b_t7_B6_o004_c000", 617, 0, 23040, 6, 12884908032),
    ("r3b_t7_B6_o006_c000", 31, 0, 512, 2, 4294967312),
    ("r3b_t7_B6_o006_c000", 133, 0, 1536, 6, 4295229456),
    ("r3b_t7_B6_o006_c000", 238, 0, 4608, 6, 12884901936),
    ("r3b_t7_B6_o006_c000", 402, 0, 8192, 12, 524288),
    ("r3b_t7_B6_o006_c000", 430, 0, 9216, 12, 786432),
    ("r3b_t7_B6_o006_c000", 514, 0, 12288, 12, 8590458912),
    ("r3b_t7_B6_o006_c000", 617, 0, 23040, 6, 12884908080),
    ("r3b_t7_B6_o008_c004", 15, 0, 512, 6, 549755813888),
    ("r3b_t7_B6_o008_c004", 44, 0, 1024, 12, 4294967296),
    ("r3b_t7_B6_o008_c004", 141, 0, 3072, 12, 4294969344),
    ("r3b_t7_B6_o008_c004", 184, 0, 5120, 2, 1103806595072),
    ("r3b_t7_B6_o008_c004", 194, 0, 5632, 6, 1653562408960),
    ("r3b_t7_B6_o008_c004", 242, 0, 7168, 6, 1103806597120),
    ("r3b_t7_B6_o008_c004", 261, 0, 7680, 6, 1653562411008),
    ("r3b_t7_B6_o008_c004", 447, 0, 32768, 6, 2199023255552),
    ("r3b_t7_B6_o008_c004", 458, 0, 33280, 6, 2748779069440),
    ("r3b_t7_B6_o008_c004", 529, 0, 36864, 12, 3298534883328),
    ("r3b_t7_B6_o008_c004", 536, 0, 37888, 6, 3302829850624),
    ("r3b_t7_B6_o008_c004", 558, 0, 40448, 6, 3852585666560),
    ("r3b_t7_B6_o003_c004", 128, 0, 2048, 2, 16),
    ("r3b_t7_B6_o003_c004", 147, 0, 2560, 4, 4294967312),
    ("r3b_t7_B6_o003_c004", 167, 0, 3072, 2, 2064),
    ("r3b_t7_B6_o003_c004", 183, 0, 4096, 4, 8589934592),
    ("r3b_t7_B6_o003_c004", 202, 0, 4608, 4, 12884901888),
    ("r3b_t7_B6_o003_c004", 259, 0, 6144, 4, 8589934608),
    ("r3b_t7_B6_o003_c004", 297, 0, 7168, 4, 8589936656),
    ("r3b_t7_B6_o003_c004", 404, 0, 18432, 2, 48),
    ("r3b_t7_B6_o003_c004", 421, 0, 20480, 4, 8589934624),
    ("r3b_t7_B6_o003_c004", 450, 0, 27648, 2, 6192),
    ("r3b_t7_B6_o003_c004", 567, 0, 36864, 4, 25769803776),
    ("r3b_t7_B6_o003_c004", 576, 0, 37376, 4, 30064771072),
    ("r3b_t7_B6_o003_c004", 755, 0, 137216, 4, 8589934672),
    ("r3b_t7_B6_o003_c004", 814, 0, 166400, 4, 21474836560),
    ("r3b_t7_B6_o003_c002", 77, 0, 1024, 4, 2048),
    ("r3b_t7_B6_o003_c002", 111, 0, 1536, 4, 4294969344),
    ("r3b_t7_B6_o003_c002", 208, 0, 3072, 4, 2064),
    ("r3b_t7_B6_o003_c002", 237, 0, 3584, 4, 4294969360),
    ("r3b_t7_B6_o003_c002", 259, 0, 4096, 4, 8589934592),
    ("r3b_t7_B6_o003_c002", 278, 0, 5120, 2, 8589936640),
    ("r3b_t7_B6_o003_c002", 325, 0, 7168, 4, 8589936656),
    ("r3b_t7_B6_o003_c002", 346, 0, 8192, 2, 4096),
    ("r3b_t7_B6_o003_c002", 430, 0, 20480, 4, 8589934624),
    ("r3b_t7_B6_o003_c002", 435, 0, 21504, 2, 8589936672),
    ("r3b_t7_B6_o003_c002", 581, 0, 36864, 4, 25769803776),
    ("r3b_t7_B6_o003_c002", 590, 0, 37376, 4, 30064771072),
    ("r3b_t7_B6_o003_c002", 597, 0, 37888, 4, 25769805824),
    ("r3b_t7_B6_o003_c002", 635, 0, 40448, 4, 30064773136),
    ("r3b_t7_B6_o003_c002", 698, 0, 46080, 4, 25769809920),
    ("r3b_t7_B6_o003_c002", 791, 0, 65536, 2, 8192),
    ("r3b_t7_B6_o003_c002", 797, 0, 66560, 4, 10240),
    ("r3b_t7_B6_o003_c002", 814, 0, 70656, 2, 8589944832),
    ("r3b_t7_B6_o003_c002", 820, 0, 73728, 2, 12288),
    ("r3b_t7_B6_o003_c002", 846, 0, 95232, 2, 8589948960),
    ("r3b_t7_B6_o003_c003", 77, 0, 1024, 4, 2048),
    ("r3b_t7_B6_o003_c003", 114, 0, 1536, 4, 4294969344),
    ("r3b_t7_B6_o003_c003", 208, 0, 3072, 4, 2064),
    ("r3b_t7_B6_o003_c003", 237, 0, 3584, 4, 4294969360),
    ("r3b_t7_B6_o003_c003", 259, 0, 4096, 4, 8589934592),
    ("r3b_t7_B6_o003_c003", 278, 0, 5120, 2, 8589936640),
    ("r3b_t7_B6_o003_c003", 325, 0, 7168, 4, 8589936656),
    ("r3b_t7_B6_o003_c003", 430, 0, 20480, 4, 8589934624),
    ("r3b_t7_B6_o003_c003", 435, 0, 21504, 2, 8589936672),
    ("r3b_t7_B6_o003_c003", 581, 0, 36864, 4, 25769803776),
    ("r3b_t7_B6_o003_c003", 588, 0, 37376, 4, 30064771072),
    ("r3b_t7_B6_o003_c003", 604, 0, 38400, 4, 30064773120),
    ("r3b_t7_B6_o003_c003", 626, 0, 39936, 4, 25769805840),
    ("r3b_t7_B6_o003_c003", 791, 0, 65536, 4, 8192),
    ("r3b_t7_B6_o003_c003", 813, 0, 69632, 2, 8589942784),
    ("r3b_t7_B6_o003_c003", 818, 0, 72704, 4, 8589944848),
    ("r3b_t7_B6_o003_c003", 846, 0, 94208, 2, 8589946912),
)
NAMED_CLASSES = {"a": ("r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000", "r3b_t7_B6_o008_c004",
                       "r3b_t7_B6_o003_c004"),
                 "b": ("r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003")}
NAMED_COUNT = {"a": 43, "b": 37}
# m70's split of the six classes (out/grade.json "classes", 2026-10-21): (planned, UNSAT).
M70 = {"r3b_t7_B6_o004_c000": (674, 664), "r3b_t7_B6_o006_c000": (674, 667),
       "r3b_t7_B6_o008_c004": (747, 735), "r3b_t7_B6_o003_c004": (847, 833),
       "r3b_t7_B6_o003_c002": (847, 827), "r3b_t7_B6_o003_c003": (847, 830)}
# m66's run for the six (m70.py's GATE, which m70's checks confirmed).
NAMED_GATE = {
    "r3b_t7_B6_o004_c000": {"d": 2, "order": 1536, "valid": 176126, "orbits": 674,
                            "by_rank": {"0": 51, "1": 324, "2": 299}},
    "r3b_t7_B6_o006_c000": {"d": 2, "order": 1536, "valid": 176126, "orbits": 674,
                            "by_rank": {"0": 51, "1": 324, "2": 299}},
    "r3b_t7_B6_o008_c004": {"d": 1, "order": 1152, "valid": 176126, "orbits": 747,
                            "by_rank": {"0": 51, "1": 348, "2": 348}},
    "r3b_t7_B6_o003_c002": {"d": 2, "order": 3072, "valid": 176126, "orbits": 847,
                            "by_rank": {"0": 135, "1": 472, "2": 240}},
    "r3b_t7_B6_o003_c003": {"d": 2, "order": 3072, "valid": 176126, "orbits": 847,
                            "by_rank": {"0": 135, "1": 472, "2": 240}},
    "r3b_t7_B6_o003_c004": {"d": 2, "order": 3072, "valid": 176126, "orbits": 847,
                            "by_rank": {"0": 135, "1": 472, "2": 240}},
}
TAILS = {"a": ("r3b_t7_B6_o012_c009",), "b": ("r3b_t7_B6_o012_c004",)}
# Job m64a's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {"r3b_t7_B6_o012_c009": "UNSAT", "r3b_t7_B6_o012_c004": "UNSAT"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o012_c009": {"d": 0, "order": 504, "valid": 176128, "orbits": 1288,
                            "by_rank": {"0": 88, "1": 600, "2": 600}},
    "r3b_t7_B6_o012_c004": {"d": 0, "order": 336, "valid": 176128, "orbits": 1976,
                            "by_rank": {"0": 136, "1": 920, "2": 920}},
}
# Classes of (B6) closed by the second-matrix split (jobs m69a, m69b, m70a), and the classes split
# by m71 or re-run here: none may be split as a tail.
CLOSED_SPLIT = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011",
                "r3b_t7_B6_o009_c008", "r3b_t7_B6_o011_c002")
SPLIT_ELSEWHERE = ("r3b_t7_B6_o004_c001", "r3b_t7_B6_o006_c001", "r3b_t7_B6_o008_c002",
                   "r3b_t7_B6_o010_c002") + tuple(M70)
REPS_FILE = "m72_reps.json"

_plan69 = b.plan


def named_name(name, k, rank_x1):
    """m69's name of the split instance of a class at root k."""
    pi, ci = m.pair_cls(name)
    return f"{'r3l' if rank_x1 == 0 else 'r3s'}_t7_B6_o{pi:03d}_c{ci:03d}_a{k:04d}"


def named_rows(group):
    return [row for row in OPEN_M70 if row[0] in NAMED_CLASSES[group]]


def named_specs(group, reps):
    """The group's re-runs as m70 ran them: m69's split instance at root k, with Lemma 93 (b) when
    of rank 0."""
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
    rng = random.Random(72)
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
        and set(NAMED_GATE) == set(M70) == set(NAMED_CLASSES["a"]) | set(NAMED_CLASSES["b"])
        and by_class == {n: M70[n][0] - M70[n][1] for n in NAMED_CLASSES[group]}
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


# ---------- grading (pre-registered in m72-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
    if "named" not in out:
        return out
    named_cls = {}
    for name in NAMED_CLASSES[group]:
        total, before = M70[name]
        mine = [named_name(n, k, rk) for n, k, rk, _, _, _ in OPEN_M70 if n == name]
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
