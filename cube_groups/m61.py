# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m61: the next passes over (B6) at t = 7 and dim V = 9, under rules that jobs m58 and m59
wrote down before they ran (cube_groups/m58-predictions.md, m59-predictions.md; notes/a50.md).

m59a closed both open instances of the kind-graph class (so that class is empty, Corollary 62) and
301 of the 308 instances of the kind-L class (pair orbit 0, split by the second matrix A_(h_1) as
Proposition 30 splits it) at 25 s of CaDiCaL each. m58b's XOR pass over the 51 open classes of (B6)
with d = dim(X_1 n R) <= 2 closed 0 of 51 at about 176 s each.

Group a (job m61a):
  (1) the 7 kind-L instances m59a left UNKNOWN (all rank 0 on X_1): CaDiCaL for 5 minutes, then, if
      still open, CryptoMiniSat with native XOR for 5 minutes (m59's rule for 1 to 30 open). If all
      7 close, all 308 instances are UNSAT and the kind-L class is empty.
  (2) the 7 classes with d = 2 of job m47's list: CaDiCaL for 15 minutes each (m58's rule for 9 or
      fewer of 51: m47's plan, never run, for the 28 classes of m47's list).
Group b (job m61b): the 16 classes with d = 1 of m47's list, CaDiCaL for 15 minutes each.

A class entry runs only if its full 15 minutes fit in what is left of the group's time; otherwise it
is SKIPPED and goes to the next job unchanged. The 5 classes with d = 0 of m47's list, and the 23 of
m45's list (whose rule is the second-matrix split, counted by hand first), are not in this job.

Instances are m57.py's (m42.py's encoding and hints, m53.py's unit clauses for A_(v_1), m50.py's
XOR encoding), imported unchanged. A kind-L instance is m59's: A_u = 266304 (e_4 -> e_2,
e_5 -> e_1, e_6 -> e_0) and A_(h_1) as m59a ran it (copied below from m59a's out files). A class
instance is m58's: A_u fixed to the class representative of m47's list (copied from m58.py).

Parts:
    check   graded: m57.py's own check; the 7 kind-L maps are admissible (Proposition 30 (a)), of
            rank 0 on X_1, have m59's index, and with their sums with A_u are 14 different maps;
            every class representative has kernel X_1, the image R of its pair, rank 3 and the hand
            value of d, 7 / 16 / 5 with d = 2 / 1 / 0, none closed earlier, none in m45's list;
            hint and unit counts of one instance of each kind in both arms.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; statuses by kind and d.

Usage: python m61.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m57 as m
import sat_aniso as sa

T, D, P = 7, 9, 6
X1 = (8, 4, 2, 1)
L_CAP = 300.0
CLASS_CAP = 900.0

# The kind-L class (pair orbit 0), as m59.py: A_u = e_4 -> e_2, e_5 -> e_1, e_6 -> e_0,
# R = span(e_0, e_1, e_2); the 7 instances m59a left UNKNOWN at 25 s: (m59 order k, m59 index, rank
# on X_1, A_(h_1), class size), copied from m59a's out/r3l_t7_B6_o000_aKKK__cadical.json.
L_AU = 266304
L_R = (4, 2, 1)
L_OPEN = ((31, 512, 0, 262144, 12), (115, 2560, 0, 262160, 12), (155, 8704, 0, 266240, 2),
          (160, 10752, 0, 266256, 6), (182, 33280, 0, 1310720, 12), (288, 41472, 0, 1314816, 6),
          (307, 61952, 0, 1839136, 6))
L_TOTAL, L_UNSAT_BEFORE = 308, 301

# (B6), copied from m58.py: the image R of each pair orbit, d by hand, the 28 classes of job m47's
# list (m42b's representatives) and the classes closed before, and m45's list (names only).
B6_PAIR_R = {0: (4, 2, 1), 1: (8, 4, 2), 2: (8, 4, 3), 3: (16, 2, 1), 4: (16, 4, 2),
             5: (16, 4, 3), 6: (17, 4, 2), 7: (32, 16, 1), 8: (32, 16, 2), 9: (32, 16, 3),
             10: (32, 17, 2), 11: (64, 32, 16), 12: (64, 32, 17)}
HAND_D_PAIR = {0: 3, 1: 3, 2: 3, 3: 2, 4: 2, 5: 2, 6: 2, 7: 1, 8: 1, 9: 1, 10: 1, 11: 0, 12: 0}
OPEN_M47 = {
    "r3b_t7_B6_o003_c000": 4294971456,
    "r3b_t7_B6_o003_c001": 4294971472,
    "r3b_t7_B6_o003_c002": 8589936704,
    "r3b_t7_B6_o003_c003": 8589936720,
    "r3b_t7_B6_o003_c004": 8589942800,
    "r3b_t7_B6_o005_c000": 4295499840,
    "r3b_t7_B6_o005_c001": 4295501904,
    "r3b_t7_B6_o007_c001": 558345748560,
    "r3b_t7_B6_o007_c002": 558345748592,
    "r3b_t7_B6_o007_c003": 562640715840,
    "r3b_t7_B6_o007_c006": 571230650400,
    "r3b_t7_B6_o007_c007": 571230650416,
    "r3b_t7_B6_o007_c009": 1103806595152,
    "r3b_t7_B6_o008_c004": 1103806603264,
    "r3b_t7_B6_o009_c000": 558345756736,
    "r3b_t7_B6_o009_c001": 558345758800,
    "r3b_t7_B6_o009_c002": 558345762928,
    "r3b_t7_B6_o009_c003": 562640724032,
    "r3b_t7_B6_o009_c005": 566935687200,
    "r3b_t7_B6_o010_c004": 1103806603280,
    "r3b_t7_B6_o010_c006": 1125281433696,
    "r3b_t7_B6_o010_c007": 1653562417168,
    "r3b_t7_B6_o010_c008": 1679332214896,
    "r3b_t7_B6_o011_c002": 71494025609216,
    "r3b_t7_B6_o011_c003": 72043781423104,
    "r3b_t7_B6_o012_c004": 72035191488576,
    "r3b_t7_B6_o012_c009": 144040318205968,
    "r3b_t7_B6_o012_c011": 283128539119632,
}
CLOSED_KNOWN = ("r3b_t7_B6_o007_c000", "r3b_t7_B6_o007_c008", "r3b_t7_B6_o011_c000",
                "r3b_t7_B6_o011_c001", "r3b_t7_B6_o011_c005", "r3b_t7_B6_o007_c005",
                "r3b_t7_B6_o012_c003", "r3b_t7_B6_o012_c005", "r3b_t7_B6_o012_c006",
                "r3b_t7_B6_o012_c008", "r3b_t7_B6_o001_c000")
OPEN_M45_NAMES = (
    "r3b_t7_B6_o004_c000", "r3b_t7_B6_o004_c001", "r3b_t7_B6_o005_c002", "r3b_t7_B6_o005_c003",
    "r3b_t7_B6_o006_c000", "r3b_t7_B6_o006_c001", "r3b_t7_B6_o007_c004", "r3b_t7_B6_o008_c000",
    "r3b_t7_B6_o008_c001", "r3b_t7_B6_o008_c002", "r3b_t7_B6_o008_c003", "r3b_t7_B6_o009_c004",
    "r3b_t7_B6_o009_c006", "r3b_t7_B6_o009_c007", "r3b_t7_B6_o009_c008", "r3b_t7_B6_o009_c009",
    "r3b_t7_B6_o010_c000", "r3b_t7_B6_o010_c001", "r3b_t7_B6_o010_c002", "r3b_t7_B6_o010_c003",
    "r3b_t7_B6_o010_c005", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c001")
HAND_D_M47 = {"2": 7, "1": 16, "0": 5}
GROUP_D = {"a": 2, "b": 1}


def l_index(a1):
    """m59's LMaps index of a map with image in R = span(e_2, e_1, e_0): bits 3 (j - 1) to
    3 (j - 1) + 2 hold the coordinates of A e_j in the basis (e_2, e_1, e_0)."""
    idx = 0
    for j in range(1, T):
        col = m.column(a1, j)
        coord = sum(1 << i for i, v in enumerate(L_R) if col & v)
        idx |= coord << (3 * (j - 1))
    return idx


def admissible_l(a1):
    """Adm of Proposition 30 (a) for pair orbit 0 (m59.admissible_l): kills x0, image inside R,
    rank on X_1 at most 2, not 0, not A_u."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(L_R, v) for v in cols) and m.rank_on_x1(a1) <= 2
            and a1 != 0 and a1 != L_AU)


def l_spec(k, index, rank_x1, a1, size):
    """As m59.l_spec."""
    return {"name": f"r3l_t7_B6_o000_a{k:03d}", "kind": "main", "t": T, "d": D, "p": P, "pair": 0,
            "x1": list(X1), "r": list(L_R), "au": L_AU, "a1": a1, "rank_x1": rank_x1,
            "m59_index": index, "size": size}


def b6_spec(name, au):
    """As m58.b6_spec, for m47's list."""
    pi, ci = m.pair_cls(name)
    return {"name": name, "kind": "main", "t": T, "d": D, "p": P, "pair": pi, "cls": ci,
            "x1": list(X1), "r": list(B6_PAIR_R[pi]), "au": au, "source": "m47"}


def classes_with_d(d):
    return [b6_spec(n, au) for n, au in sorted(OPEN_M47.items())
            if HAND_D_PAIR[m.pair_cls(n)[0]] == d]


def plan(group):
    """[(spec, arm, cap seconds, condition)]; condition "open" runs the entry only if the same
    instance is still undecided, "full" only if the whole cap fits in what is left."""
    out = []
    if group == "a":
        for row in L_OPEN:
            sp = l_spec(*row)
            out += [(sp, "cadical", L_CAP, None), (dict(sp), "xor", L_CAP, "open")]
    return out + [(sp, "cadical", CLASS_CAP, "full") for sp in classes_with_d(GROUP_D[group])]


# ---------- check ----------

def check(out_dir):
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}}
    # Kind L.
    graded["l_au"] = (m.kernel(L_AU, T) == X1 and m.column_space(L_AU, T) == L_R
                      and m.dim_meet(X1, L_R) == 3 and m.in_span(L_R, 1))
    maps = [a1 for _, _, _, a1, _ in L_OPEN]
    graded["l_open"] = (len(L_OPEN) == L_TOTAL - L_UNSAT_BEFORE
                        and all(admissible_l(a1) and m.rank_on_x1(a1) == rk and l_index(a1) == idx
                                for _, idx, rk, a1, _ in L_OPEN)
                        and len(set(maps) | {a ^ L_AU for a in maps}) == 2 * len(maps))
    # (B6) classes of m47's list.
    specs = [b6_spec(n, au) for n, au in sorted(OPEN_M47.items())]
    graded["m47_list"] = (len(OPEN_M47) == 28 and not set(OPEN_M47) & set(CLOSED_KNOWN)
                          and not set(OPEN_M47) & set(OPEN_M45_NAMES) and len(OPEN_M45_NAMES) == 23
                          and all(n == "r3b_t7_B6_o%03d_c%03d" % m.pair_cls(n) for n in OPEN_M47))
    graded["m47_reps"] = all(m.kernel(s["au"], T) == X1
                             and m.column_space(s["au"], T) == tuple(s["r"])
                             and sa.rank_f2(m.cols_of(s["au"], T)) == 3 for s in specs)
    by_d = {}
    for s in specs:
        dk = str(m.meet_d(s))
        by_d[dk] = by_d.get(dk, 0) + 1
    st["m47_by_d"] = by_d
    graded["m47_hand_d"] = by_d == HAND_D_M47 and all(
        m.meet_d(s) == HAND_D_PAIR[s["pair"]] for s in specs)
    per_pair = {}
    for s in specs:
        per_pair.setdefault(s["pair"], set()).add(s["au"])
    graded["m47_distinct"] = sum(len(v) for v in per_pair.values()) == len(specs)
    # Hints and units, both arms.
    probes = {}
    for arm in ("cadical", "xor"):
        cl, _, hl, ul = m.build(l_spec(*L_OPEN[0]), arm)
        cb, _, hb, ub = m.build(specs[0], arm)
        probes[arm] = [cl.nv, len(cl.clauses), hl, ul, cb.nv, len(cb.clauses), hb, ub]
        graded["probe_" + arm] = (hl == m.HAND_HINTS["B6"] and ul == T * T and hb == hl and ub == 0
                                  and m.units_consistent(cl) and m.units_consistent(cb)
                                  and (arm == "cadical" or len(cl.xors) > 0))
    st["probes"] = probes
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- solving ----------

def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    counts, decided = {}, set()
    for spec, arm, cap, cond in plan(group):
        if cond == "open" and spec["name"] in decided:
            continue
        left = group_seconds - (time.time() - start)
        if left < 5 or (cond == "full" and left < cap):
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = m.solve_one(spec, arm, min(cap, left), out_dir)
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m61-predictions.md) ----------

def grade(group, out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    rows, by_key, status, arm_of = {}, {}, {}, {}
    for spec, arm, _, cond in plan(group):
        tag = m.tag_of(spec, arm)
        path = os.path.join(out_dir, tag + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows[tag] = [s, r.get("wall_seconds"), r.get("budget_seconds")]
        if s in ("SAT", "UNSAT"):
            status[spec["name"]] = s
            arm_of[spec["name"]] = arm
        else:
            status.setdefault(spec["name"], s)
        if s == "SAT":
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
        if cond == "open":
            continue
        key = "kind_l_cadical" if spec["pair"] == 0 else f"m47_d{m.meet_d(spec)}"
        by_key.setdefault(key, {})
        by_key[key][s] = by_key[key].get(s, 0) + 1
    out = {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows, "by": by_key,
           "any_sat_7": any(v[0] == "SAT" for v in rows.values())}
    if group == "a":
        names = [l_spec(*row)["name"] for row in L_OPEN]
        out["l_reopen"] = {n: [status.get(n), arm_of.get(n)] for n in names}
        out["l_unsat_of_308"] = L_UNSAT_BEFORE + sum(status.get(n) == "UNSAT" for n in names)
        out["l_open"] = [n for n in names if status.get(n) != "UNSAT"]
        out["kind_l_empty"] = out["l_unsat_of_308"] == L_TOTAL
    cnames = [sp["name"] for sp in classes_with_d(GROUP_D[group])]
    out["m47"] = {n: status.get(n) for n in cnames}
    out["b6_unsat"] = [n for n in cnames if status.get(n) == "UNSAT"]
    out["b6_skipped"] = [n for n in cnames if status.get(n) == "SKIPPED"]
    out["b6_open"] = [n for n in cnames if status.get(n) not in ("UNSAT", "SKIPPED")]
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
              f"any_sat_7 {out['any_sat_7']} l_unsat_of_308 {out.get('l_unsat_of_308')} "
              f"b6_unsat {len(out['b6_unsat'])} b6_skipped {len(out['b6_skipped'])} "
              f"by {json.dumps(out['by'], sort_keys=True)}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
