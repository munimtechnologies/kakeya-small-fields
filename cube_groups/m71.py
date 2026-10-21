# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m71: the 21 split instances of (B6) that job m69b left open, re-run under m69's rule for 1 to
30 open in a class, and the second-matrix splits of o008_c002 and o010_c002 (Proposition 33,
notes/a52.md), at t = 7 and dim V = 9 (cube_groups/m69-predictions.md, m71-predictions.md;
notes/a59.md).

What came back on 2026-10-21: m69b's check held (27 graded, all true) and nothing was SAT. All 696
split instances of o009_c008 (d = 1, sweep UNSAT) were UNSAT, so that class is empty (Corollary 71).
o004_c001 and o006_c001 (d = 2, sweep open) closed 574 and 579 of their 587 at 10 to 20 s and left
13 and 8 open: 11 and 7 of rank 0 on X_1 (with Lemma 93 (b)), 2 and 1 of rank 1. The median UNSAT
wall time was 1.22 to 1.42 s, so by m69's pace rule the next (B6) jobs keep 4 or 5 classes per
group. Job m70a was stopped by its host 4 minutes into its solve part (exit 143) before any split
instance finished; it is re-run unchanged as m70a-v2.

Group a (job m71a): the 21, rank 1 first, each CaDiCaL for at most 300 s, then, if open,
  CryptoMiniSat with native XOR for 300 s; then the splits of o008_c002 and o010_c002 (d = 1, sweep
  open: all 1021 each, the 69 of rank 0 with Lemma 93 (b)). Two classes, not four or five, because
  the 21 re-runs may take up to 210 minutes at worst.

Everything else is m69.py's, imported unchanged: the instances (m57.py's encoding and hints, the
unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of m66.py, the plan
of the tails, the shared budget (10 to 20 s per split instance), the child process and the grading
of the split classes. This file sets m69's lists, puts the 21 in front of m69's plan, and checks
them: their two classes against m66's run as m69's check does, each root recomputed by m66.py
against the one m69b ran (index, map, rank on X_1, orbit size), Lemma 93 exactly on the rank-0
ones, and hint and unit counts in both arms.

Parts:
    check   m69.py's check of the two tail classes, then the 21 as above. Writes m71_reps.json.
    solve   m69.py's solve with this plan.
    grade   m69.py's grade, and whether o004_c001 and o006_c001 are now empty.

Usage: python m71.py --part check|solve|grade [--group a] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random

import m69 as b
import m66
import m57 as m

T = 7
# The 21 that m69b left open (UNKNOWN at 10 to 20 s), copied from its out/<name>__cadical.json:
# (class, k, rank on X_1, m66 index, orbit size, A_(v_1)), rank 1 first.
OPEN_M69B = (
    ("r3b_t7_B6_o004_c001", 22, 1, 36, 64, 768),
    ("r3b_t7_B6_o004_c001", 223, 1, 1581, 128, 5905842944),
    ("r3b_t7_B6_o006_c001", 223, 1, 1581, 128, 5905842966),
    ("r3b_t7_B6_o004_c001", 152, 0, 1024, 8, 262144),
    ("r3b_t7_B6_o004_c001", 210, 0, 1536, 16, 4295229440),
    ("r3b_t7_B6_o004_c001", 259, 0, 2048, 8, 2048),
    ("r3b_t7_B6_o004_c001", 320, 0, 3072, 8, 264192),
    ("r3b_t7_B6_o004_c001", 334, 0, 4096, 8, 8589934592),
    ("r3b_t7_B6_o004_c001", 354, 0, 5120, 8, 8590196736),
    ("r3b_t7_B6_o004_c001", 426, 0, 8192, 2, 524288),
    ("r3b_t7_B6_o004_c001", 446, 0, 13312, 8, 8590721024),
    ("r3b_t7_B6_o004_c001", 457, 0, 16384, 4, 4096),
    ("r3b_t7_B6_o004_c001", 545, 0, 36864, 8, 25769803776),
    ("r3b_t7_B6_o004_c001", 583, 0, 65536, 4, 1048576),
    ("r3b_t7_B6_o006_c001", 152, 0, 1024, 8, 262144),
    ("r3b_t7_B6_o006_c001", 210, 0, 1536, 16, 4295229456),
    ("r3b_t7_B6_o006_c001", 320, 0, 3072, 8, 264192),
    ("r3b_t7_B6_o006_c001", 334, 0, 4096, 8, 8589934624),
    ("r3b_t7_B6_o006_c001", 354, 0, 5120, 8, 8590196768),
    ("r3b_t7_B6_o006_c001", 426, 0, 8192, 2, 524288),
    ("r3b_t7_B6_o006_c001", 545, 0, 36864, 8, 25769803872),
)
# m69b's split of the two classes (out/grade.json "classes", 2026-10-21): (planned, UNSAT).
M69B = {"r3b_t7_B6_o004_c001": (587, 574), "r3b_t7_B6_o006_c001": (587, 579)}
# m66's run for the two (m69.py's GATE, which m69b's check confirmed).
NAMED_GATE = {
    "r3b_t7_B6_o004_c001": {"d": 2, "order": 2048, "valid": 176126, "orbits": 587,
                            "by_rank": {"0": 42, "1": 286, "2": 259}},
    "r3b_t7_B6_o006_c001": {"d": 2, "order": 2048, "valid": 176126, "orbits": 587,
                            "by_rank": {"0": 42, "1": 286, "2": 259}},
}
TAILS = {"a": ("r3b_t7_B6_o008_c002", "r3b_t7_B6_o010_c002"), "b": ()}
# Job m64a's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {"r3b_t7_B6_o008_c002": "open", "r3b_t7_B6_o010_c002": "open"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o008_c002": {"d": 1, "order": 768, "valid": 176126, "orbits": 1021,
                            "by_rank": {"0": 69, "1": 476, "2": 476}},
    "r3b_t7_B6_o010_c002": {"d": 1, "order": 768, "valid": 176126, "orbits": 1021,
                            "by_rank": {"0": 69, "1": 476, "2": 476}},
}
# Classes of (B6) closed by jobs m69a and m69b, and the classes split by m69b or in m70's lists:
# none may be split here.
CLOSED_M69 = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011",
              "r3b_t7_B6_o009_c008")
SPLIT_ELSEWHERE = ("r3b_t7_B6_o004_c001", "r3b_t7_B6_o006_c001", "r3b_t7_B6_o011_c002",
                   "r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000", "r3b_t7_B6_o008_c004",
                   "r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003", "r3b_t7_B6_o003_c004")
REPS_FILE = "m71_reps.json"

_plan69 = b.plan


def named_name(name, k, rank_x1):
    """m69's name of the split instance of a class at root k."""
    pi, ci = m.pair_cls(name)
    return f"{'r3l' if rank_x1 == 0 else 'r3s'}_t7_B6_o{pi:03d}_c{ci:03d}_a{k:04d}"


def named_specs(group, reps):
    """The 21 as m69b ran them: m69's split instance at root k, with Lemma 93 (b) when of rank 0."""
    if group != "a":
        return []
    return [b.split_spec(name, k, reps[name][k], rank_x1 == 0)
            for name, k, rank_x1, _, _, _ in OPEN_M69B]


def plan(group, reps):
    """The 21 (each CaDiCaL, then XOR if still open, at the full cap), then m69's plan of the
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
    if group != "a":
        return
    graded, probes = st["graded"], st["probes"]
    reps = b.load_reps(out_dir)
    rng = random.Random(71)
    for name, gate in NAMED_GATE.items():
        tag = name[10:]
        r, rr = b.class_reps(name, rng)
        st["split"][tag] = r
        graded["named_split_" + tag] = class_ok(r, gate)
        graded["named_split_reps_" + tag] = reps_ok(name, rr, gate)
        reps[name] = rr
    with open(os.path.join(out_dir, REPS_FILE), "w") as f:
        json.dump(reps, f)
    named = named_specs(group, reps)
    by_class = {}
    for sp in named:
        by_class[sp["parent"]] = by_class.get(sp["parent"], 0) + 1
    graded["named_list"] = (
        len(named) == 21 and len({sp["name"] for sp in named}) == 21
        and set(NAMED_GATE) == set(M69B)
        and by_class == {n: total - unsat for n, (total, unsat) in M69B.items()}
        and [sp["rank_x1"] for sp in named] == sorted((sp["rank_x1"] for sp in named),
                                                       reverse=True)
        and sum(sp["rank_x1"] == 0 for sp in named) == 18)
    graded["named_maps"] = all(
        sp["name"] == named_name(name, k, rk) and sp["parent"] == name
        and sp["m66_index"] == index and sp["size"] == size and sp["a1"] == a1
        and sp["rank_x1"] == rk == b.rank_on(a1, b.X1)
        and bool(sp.get("lemma93")) == (rk == 0)
        and b.admissible_b6(a1, sp["au"], b.r_of(name), NAMED_GATE[name]["d"])
        for sp, (name, k, rk, index, size, a1) in zip(named, OPEN_M69B))
    first_s = next(sp for sp in named if not sp.get("lemma93"))
    first_l = next(sp for sp in named if sp.get("lemma93"))
    for arm in ("cadical", "xor"):
        for tag, sp, units in (("s", first_s, T * T), ("l", first_l, T * T + 21)):
            c, _, h, u = m.build(dict(sp), arm)
            probes[f"named_{tag}_{arm}"] = [c.nv, len(c.clauses), h, u]
            graded[f"probe_named_{tag}_{arm}"] = (h == m.HAND_HINTS["B6"] and u == units
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
    graded["not_split_before"] = not set(TAILS[group]) & (set(CLOSED_M69) | set(SPLIT_ELSEWHERE))
    check_named(group, out_dir, st)
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m71-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
    if "named" not in out:
        return out
    named_cls = {}
    for name, (total, before) in M69B.items():
        mine = [named_name(n, k, rk) for n, k, rk, _, _, _ in OPEN_M69B if n == name]
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
    return out


def summary_line(out):
    cls = {n[10:]: {k: v for k, v in c.items() if k != "open"} for n, c in out.get("classes", {}).items()}
    opened = {n[10:]: c["open"][:30] for n, c in out.get("classes", {}).items()}
    named = {n[10:]: c for n, c in out.get("named_classes", {}).items()}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} named_unsat {out.get('named_unsat')} "
            f"named_open {out.get('named_open')} named_max_unsat_wall "
            f"{out.get('named_max_unsat_wall')} named_classes {json.dumps(named, sort_keys=True)} "
            f"b6_closed {out.get('b6_closed')} classes {json.dumps(cls, sort_keys=True)} "
            f"open {json.dumps(opened, sort_keys=True)}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group", choices=["a"], default="a")
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
