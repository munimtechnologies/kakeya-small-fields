# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m70: the next second-matrix splits of (B6) at t = 7 and dim V = 9 (Proposition 33,
notes/a52.md), and the 27 split instances of (B5) that job m67b left open, under the rules that jobs
m67 and m69 wrote down before they ran (cube_groups/m67-predictions.md, m69-predictions.md;
notes/a58.md).

What came back on 2026-10-21: m69a closed a561, so o020_c000 of (B5) is empty, and all 1534 split
instances of o011_c003, o011_c004 and o012_c011 of (B6) (d = 0) were UNSAT, so those three classes
are empty; the median UNSAT wall time was 1.22 to 1.27 s. By m69's pace rule (at most 3 s) the next
(B6) jobs take 4 or 5 classes per group, smallest first by planned count. m67b left 27 of the 1908
split instances of r3b_t7_B5_o002_c001 open at 10 to 20 s (10 of rank 1, 17 of rank 0 with Lemma
93); by m67's rule for 1 to 30 open they are re-run with 5 minutes of CaDiCaL, then 5 of XOR.

Group a (job m70a): the 27 of o002_c001 as m67b ran them (rank 1 first), each CaDiCaL for at most
  300 s, then, if open, CryptoMiniSat with native XOR for 300 s; then the splits of o011_c002
  (d = 0, sweep UNSAT: 462 + 462 of rank 1 and 2), o004_c000 and o006_c000 (d = 2, sweep open: all
  674 each, the 51 of rank 0 with Lemma 93 (b)). Three classes, not four or five, because the 27
  re-runs may take up to 270 minutes at worst.
Group b (job m70b): the splits of o008_c004 (d = 1, sweep open: 747), o003_c002, o003_c003 and
  o003_c004 (d = 2, sweep open: 847 each, the 135 of rank 0 with Lemma 93 (b)).

Everything else is m69.py's, imported unchanged: the instances (m57.py's encoding and hints, the
unit clauses fixing A_(v_1), Lemma 93 (b) on the rank-0 ones), the orbit roots of m66.py, the plan,
the shared budget (10 to 20 s per split instance), the child process and the grading of the split
classes. This file sets m69's lists to the ones above and adds the checks of the 27 named instances.

Parts:
    check   m69.py's check of the group's split classes (with m66's structure, |G|, |Adm| and orbit
            counts against m66's run), then, in group a, the 27: the class o002_c001 (kernel X_1,
            image R, rank 3, d = 3), each A_(v_1) admissible for Proposition 32 (a) with its
            recorded rank on X_1, Lemma 93 exactly on the rank-0 ones, 27 distinct maps with their
            sums with A_u, hint and unit counts in both arms, and the first Lemma 93 instance
            against the plain one (42 unit clauses). Writes m70_reps.json.
    solve   m69.py's solve with these lists.
    grade   m69.py's grade, and in group a whether o002_c001 of (B5) is now empty.

Usage: python m70.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os

import m69 as b
import m57 as m
import sat_aniso as sa

T = 7
O002 = "r3b_t7_B5_o002_c001"
O002_AU = 34089040
O002_X1 = (8, 4, 2, 1)
O002_R = (8, 4, 3)
# m67b's split of o002_c001 (out/grade.json "tail", 2026-10-21): (instances, UNSAT).
M67B_TAIL = (1908, 1881)
# The 27 it left open (UNKNOWN at 10 to 20 s), copied from out/<name>__cadical.json:
# (k, rank on X_1, m55 index, orbit size, A_(v_1)).
OPEN_M67B = (
    (291, 1, 4315, 64, 96698368), (379, 1, 4671, 64, 113345286), (504, 1, 8246, 64, 623366),
    (510, 1, 8557, 64, 29886222), (770, 1, 41325, 64, 29886286), (877, 1, 135743, 64, 114393862),
    (1145, 1, 524613, 128, 17200841994), (1243, 1, 527173, 128, 17234398490),
    (1499, 1, 1057133, 256, 2199053141774), (1661, 1, 2101796, 256, 281475077374726),
    (183, 0, 1024, 2, 262144), (220, 0, 2560, 4, 33556496), (497, 0, 8192, 8, 524288),
    (546, 0, 10752, 4, 34080784), (642, 0, 23040, 8, 100669488), (652, 0, 32768, 2, 64),
    (782, 0, 43520, 4, 34080848), (817, 0, 131072, 2, 1048576), (841, 0, 132096, 2, 1310720),
    (925, 0, 163840, 2, 1048640), (946, 0, 166400, 4, 34605136), (980, 0, 262144, 4, 134217728),
    (1006, 0, 262656, 4, 167772160), (1044, 0, 270336, 4, 134742016),
    (1046, 0, 271360, 4, 135004160), (1065, 0, 294912, 4, 134217792),
    (1441, 0, 1051136, 32, 2199056812048),
)


def named_spec(k, rank_x1, index, size, a1):
    """m67's instance r3s_ (or r3l_ with Lemma 93 (b) when of rank 0) of o002_c001 at root k."""
    sp = m.b5_spec(O002, O002_AU)
    sp.update({"name": f"{'r3l' if rank_x1 == 0 else 'r3s'}_t7_B5_o002_c001_a{k}", "a1": a1,
               "rank_x1": rank_x1, "m55_index": index, "size": size, "parent": O002})
    if rank_x1 == 0:
        sp["lemma93"] = True
    return sp


NAMED = {"a": tuple(named_spec(*row) for row in OPEN_M67B), "b": ()}
TAILS = {"a": ("r3b_t7_B6_o011_c002", "r3b_t7_B6_o004_c000", "r3b_t7_B6_o006_c000"),
         "b": ("r3b_t7_B6_o008_c004", "r3b_t7_B6_o003_c002", "r3b_t7_B6_o003_c003",
               "r3b_t7_B6_o003_c004")}
# Job m64a's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {"r3b_t7_B6_o011_c002": "UNSAT", "r3b_t7_B6_o004_c000": "open",
         "r3b_t7_B6_o006_c000": "open", "r3b_t7_B6_o008_c004": "open",
         "r3b_t7_B6_o003_c002": "open", "r3b_t7_B6_o003_c003": "open",
         "r3b_t7_B6_o003_c004": "open"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o011_c002": {"d": 0, "order": 672, "valid": 176128, "orbits": 994,
                            "by_rank": {"0": 70, "1": 462, "2": 462}},
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
# Classes of (B6) closed by job m69a: none may be split again.
CLOSED_M69A = ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011")
REPS_FILE = "m70_reps.json"


def install():
    """m69's lists become this job's; m57.build keeps m69's Lemma 93 (b)."""
    b.install()
    b.NAMED, b.TAILS, b.SWEEP, b.GATE, b.REPS_FILE = NAMED, TAILS, SWEEP, GATE, REPS_FILE


install()


# ---------- check ----------

def probe93(sp, kind):
    """m69.probe93 for an instance of (B5) or (B6): the Lemma 93 instance is the plain one plus
    exactly lemma93_units negative unit clauses on A_(v_2), ..., A_(v_(kd-1)) at X_1's columns."""
    ok, counts = {}, {}
    base = {k: v for k, v in sp.items() if k != "lemma93"}
    base["name"] = sp["name"].replace("r3l_", "r3s_", 1)
    for arm in ("cadical", "xor"):
        c0, _, h0, u0 = m.build(base, arm)
        c1, names, h1, u1 = m.build(sp, arm)
        extra = c1.clauses[len(c0.clauses):]
        a_vars = {names[0][i][r][c] for i in range(2, sp["d"] - sp["p"]) for r in range(T)
                  for c in b.x1_cols(sp)}
        counts[arm] = [c1.nv, len(c1.clauses), h1, u1, len(extra)]
        ok[arm] = (c1.nv == c0.nv and c1.clauses[:len(c0.clauses)] == c0.clauses
                   and len(extra) == b.lemma93_units(sp) == u1 - u0
                   and h1 == h0 == m.HAND_HINTS[kind]
                   and all(len(cl) == 1 and cl[0] < 0 and -cl[0] in a_vars for cl in extra)
                   and len({-cl[0] for cl in extra}) == len(extra) and m.units_consistent(c1)
                   and len(getattr(c1, "xors", ())) == len(getattr(c0, "xors", ())))
    return ok, counts


def check_named(group, graded, probes):
    named = NAMED[group]
    if not named:
        return
    x1, rb = O002_X1, O002_R
    by_rank = {}
    for sp in named:
        by_rank[str(sp["rank_x1"])] = by_rank.get(str(sp["rank_x1"]), 0) + 1
    graded["named_list"] = (len(named) == M67B_TAIL[0] - M67B_TAIL[1] == 27
                            and by_rank == {"1": 10, "0": 17}
                            and len({sp["name"] for sp in named}) == len(named)
                            and [sp["rank_x1"] for sp in named]
                            == sorted((sp["rank_x1"] for sp in named), reverse=True))
    graded["named_class"] = (m.kernel(O002_AU, T) == x1 and m.column_space(O002_AU, T) == rb
                             and sa.rank_f2(m.cols_of(O002_AU, T)) == 3
                             and m.meet_d(named[0]) == 3)
    graded["named_maps"] = (
        all(sp["au"] == O002_AU and tuple(sp["x1"]) == x1 and tuple(sp["r"]) == rb
            and sp["parent"] == O002 and b.admissible_b5(sp["a1"], O002_AU, x1, rb)
            and b.rank_on(sp["a1"], x1) == sp["rank_x1"]
            and bool(sp.get("lemma93")) == (sp["rank_x1"] == 0)
            and sp["name"].startswith(("r3l_" if sp["rank_x1"] == 0 else "r3s_")
                                      + "t7_B5_o002_c001_a")
            for sp in named)
        and b.distinct_with_au([sp["a1"] for sp in named], O002_AU))
    first_s = next(sp for sp in named if not sp.get("lemma93"))
    first_l = next(sp for sp in named if sp.get("lemma93"))
    for arm in ("cadical", "xor"):
        for tag, sp, units in (("s", first_s, T * T), ("l", first_l, T * T + 42)):
            c, _, h, u = m.build(dict(sp), arm)
            probes[f"named_{tag}_{arm}"] = [c.nv, len(c.clauses), h, u]
            graded[f"probe_named_{tag}_{arm}"] = (h == m.HAND_HINTS["B5"] and u == units
                                                  and m.units_consistent(c))
    ok, counts = probe93(first_l, "B5")
    for arm, v in ok.items():
        graded["probe93_named_" + arm] = v and b.lemma93_units(first_l) == 42
    probes["lemma93_named"] = counts


def check(group, out_dir):
    install()
    b.NAMED = {"a": (), "b": ()}
    try:
        st = b.check(group, out_dir)
    finally:
        b.NAMED = NAMED
    graded = st["graded"]
    graded["not_closed_before"] = not set(TAILS[group]) & set(CLOSED_M69A)
    check_named(group, graded, st["probes"])
    st["plan"]["named"] = len(NAMED[group])
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- grading (pre-registered in m70-predictions.md) ----------

def grade(group, out_dir):
    install()
    out = b.grade(group, out_dir)
    out.pop("o020", None)
    out.pop("b5_closed", None)
    if group == "a" and "named" in out:
        total, before = M67B_TAIL
        here = out["named_unsat"]
        out["o002"] = {"name": O002, "total": total, "unsat": before + here,
                       "empty": before + here == total}
        out["b5_closed"] = [O002] if out["o002"]["empty"] else []
        out["named_open"] = [n for n, s in out["named"].items() if s != "UNSAT"]
        walls = [min(v[1] for v in out["rows"][n].values() if v[0] == "UNSAT")
                 for n, s in out["named"].items() if s == "UNSAT"]
        out["named_max_unsat_wall"] = max(walls) if walls else None
    return out


def summary_line(out):
    cls = {n[10:]: {k: v for k, v in c.items() if k != "open"} for n, c in out.get("classes", {}).items()}
    opened = {n[10:]: c["open"][:30] for n, c in out.get("classes", {}).items()}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} named_unsat {out.get('named_unsat')} "
            f"named_open {out.get('named_open')} named_max_unsat_wall "
            f"{out.get('named_max_unsat_wall')} o002 {json.dumps(out.get('o002'))} "
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
