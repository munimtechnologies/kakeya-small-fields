# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m58: two passes over (B6) at t = 7 and dim V = 9 under rules that jobs m54 and m57 wrote down
before they ran (cube_groups/m54-predictions.md, m57-predictions.md; notes/a47.md).

Group a (job m58a), the kind-graph class of (B6) with d = 3 (pair orbit 2):
  (1) r3g_t7_B6_o002_a025, the one instance of m54's batch a that stayed UNKNOWN at 95 s (rank 0
      on X_1): CaDiCaL for 10 minutes (m54's rule for 80 to 89 of 89 UNSAT), then, if still open,
      CryptoMiniSat with native XOR for 10 minutes;
  (2) a host control: r3g_t7_B6_o002_a085 (rank 0 on X_1, UNSAT in 6.5 s in m54a), reported only;
  (3) m54's batch b, the representatives 89 to 177 of Proposition 30 in m54's order, as m54a's run
      recorded them in m42's coordinates (out/m54_reps.json, all 178 checked there: admissible,
      356 different maps with their sums with A_u, ranks on X_1 as m52), CaDiCaL, at most 95 s
      each, as m54b was staged to run.
  If a025 and all 89 are UNSAT, all 178 instances are, and the kind-graph class is empty.

Group b (job m58b): the 51 open classes of (B6) with d = dim(X_1 n R) <= 2, CryptoMiniSat with
native XOR, at most 3 minutes each. m57b's XOR pass closed 18 of 21 classes of (B5) with d <= 2
that CaDiCaL had left open at 10 to 15 minutes (every one in under 108 s), so by m57's rule the XOR
arm is the second pass for open classes with d <= 2, the (B6) ones next. The 51 are the 23 classes
job m45 left open with d <= 2 (CaDiCaL at about 624 s, and m49's control) and the 28 of job m47's
list (m42b's half; CaDiCaL at about 250 s only) other than o001_c000, the kind-P class that m53
and m57b closed.

Instances are m57.py's (m42.py's encoding and hints, m53.py's unit clauses for A_(v_1), m50.py's
XOR encoding), unchanged; m57.py is imported, not copied.

Parts:
    check   graded: m57.py's own check (B5 lists, a07, hints, XOR against CNF on random small
            systems, the planted control at t = 6 in both arms); kind graph: A_u has kernel X_1,
            image R, d = 3, dim(R n P) = 2, x0 not in R; a025 and the 89 of batch b are admissible
            with the recorded rank on X_1, 16 / 64 / 9 by rank, and they and their sums with A_u
            are 180 different maps; m58's instance for m54's a088 has m54's size (48587 variables,
            286218 clauses); (B6): every one of the 51 representatives has kernel X_1, the image R
            of its pair and rank 3, d = 2 / 1 / 0 for 13 / 31 / 7 of them by the hand table of the
            pairs, none is a class closed earlier, and the (B6) instance has 79 hints in both arms.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; statuses by rank on X_1 (a) or by d and source (b).

Usage: python m58.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m57 as m
import sat_aniso as sa

T, D, P = 7, 9, 6
MIN_BUDGET = 20.0

# (B6): X_1 = span(e_0, ..., e_3); the image R of each of the 13 pair orbits as m42a numbered them
# (m45.py's PAIR_R). d = 3 for pairs 0 to 2, 2 for 3 to 6, 1 for 7 to 10, 0 for 11 and 12.
X1 = (8, 4, 2, 1)
B6_PAIR_R = {0: (4, 2, 1), 1: (8, 4, 2), 2: (8, 4, 3), 3: (16, 2, 1), 4: (16, 4, 2),
             5: (16, 4, 3), 6: (17, 4, 2), 7: (32, 16, 1), 8: (32, 16, 2), 9: (32, 16, 3),
             10: (32, 17, 2), 11: (64, 32, 16), 12: (64, 32, 17)}
HAND_D_PAIR = {0: 3, 1: 3, 2: 3, 3: 2, 4: 2, 5: 2, 6: 2, 7: 1, 8: 1, 9: 1, 10: 1, 11: 0, 12: 0}

# The 23 classes job m45 left open with d <= 2 (m45.py's OPEN without o000_c000 and o002_c000,
# d = 3, and without the five m45 closed: o007_c005, o012_c003, o012_c005, o012_c006, o012_c008).
OPEN_M45 = {
    "r3b_t7_B6_o004_c000": 4295499776,
    "r3b_t7_B6_o004_c001": 8590204928,
    "r3b_t7_B6_o005_c002": 8590204992,
    "r3b_t7_B6_o005_c003": 8590207056,
    "r3b_t7_B6_o006_c000": 4295499792,
    "r3b_t7_B6_o006_c001": 8590204960,
    "r3b_t7_B6_o007_c004": 562640715856,
    "r3b_t7_B6_o008_c000": 558345756672,
    "r3b_t7_B6_o008_c001": 562640723968,
    "r3b_t7_B6_o008_c002": 566935687168,
    "r3b_t7_B6_o008_c003": 571230654464,
    "r3b_t7_B6_o009_c004": 562640726096,
    "r3b_t7_B6_o009_c006": 571230654496,
    "r3b_t7_B6_o009_c007": 571230656560,
    "r3b_t7_B6_o009_c008": 1103806603328,
    "r3b_t7_B6_o009_c009": 1103806605392,
    "r3b_t7_B6_o010_c000": 558345756704,
    "r3b_t7_B6_o010_c001": 562640724016,
    "r3b_t7_B6_o010_c002": 566935687232,
    "r3b_t7_B6_o010_c003": 571230654544,
    "r3b_t7_B6_o010_c005": 1116691499072,
    "r3b_t7_B6_o011_c004": 72048076390400,
    "r3b_t7_B6_o012_c001": 71489730642000,
}
# The 28 classes of job m47's list (m47.py's OPEN, m42b's 29 UNKNOWN, without o001_c000).
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
# Classes of (B6) closed before (m42b's 5 UNSAT as m47.py lists them, m45b's one, m45a's four):
# none may be in the lists above.
CLOSED_KNOWN = ("r3b_t7_B6_o007_c000", "r3b_t7_B6_o007_c008", "r3b_t7_B6_o011_c000",
                "r3b_t7_B6_o011_c001", "r3b_t7_B6_o011_c005", "r3b_t7_B6_o007_c005",
                "r3b_t7_B6_o012_c003", "r3b_t7_B6_o012_c005", "r3b_t7_B6_o012_c006",
                "r3b_t7_B6_o012_c008", "r3b_t7_B6_o001_c000")
HAND_D_B = {"2": 13, "1": 31, "0": 7}

# The kind-graph class (pair orbit 2): m42b's representative A_u = e_4 -> e_3, e_5 -> e_2,
# e_6 -> e_0 + e_1, and m54's batch b: (m52 index, rank on X_1, A_(h_1) in m42's coordinates), the
# entries 89 to 177 of m54a's out/m54_reps.json in order.
GRAPH_AU = 34086976
GRAPH_R = (8, 4, 3)
GRAPH_B = (
    (1064, 1, 8651268), (1069, 1, 25429516), (1072, 1, 328196), (1280, 1, 262402),
    (1284, 1, 263434), (1344, 1, 4456706), (1349, 1, 21234954), (2048, 0, 2064),
    (2049, 1, 16779280), (2050, 1, 133136), (2056, 1, 8390672), (2057, 1, 25167888),
    (2058, 2, 8521744), (2059, 2, 25298960), (2064, 1, 67600), (2065, 2, 16844816),
    (2067, 2, 16975888), (2112, 1, 4196368), (2113, 1, 20973584), (2114, 2, 4327440),
    (2115, 2, 21104656), (2120, 1, 12584976), (2121, 1, 29362192), (2128, 2, 4261904),
    (2136, 2, 12650512), (2139, 2, 29558800), (2176, 1, 34832), (2178, 1, 165904),
    (2560, 0, 33556496), (2562, 1, 33687568), (2576, 1, 33622032), (2688, 1, 33589264),
    (5120, 0, 67371008), (5125, 1, 84149256), (5126, 1, 67503112), (5165, 1, 92538380),
    (5440, 1, 71565570), (5445, 1, 88343818), (5480, 1, 79954694), (5485, 1, 96732942),
    (5632, 0, 100925440), (5636, 1, 100926472), (5637, 1, 117703688), (5638, 1, 101057544),
    (5639, 1, 117834760), (5888, 1, 100925698), (5892, 1, 100926730), (5952, 1, 105120002),
    (5997, 1, 130287374), (6144, 0, 67110928), (6146, 1, 67242000), (6147, 1, 84019216),
    (6160, 1, 67176464), (6162, 1, 67307536), (6168, 1, 75565072), (6171, 1, 92473360),
    (6272, 1, 67143696), (6290, 1, 67340304), (6336, 1, 71338000), (6339, 1, 88246288),
    (6360, 1, 79792144), (6363, 1, 96700432), (6656, 0, 100665360), (7680, 0, 100927504),
    (8704, 0, 34078720), (8709, 1, 50856968), (8710, 1, 34210824), (9024, 1, 38273282),
    (9029, 1, 55051530), (9064, 1, 46662406), (10240, 0, 526352), (11776, 0, 34342928),
    (32768, 0, 134217728), (32770, 1, 134348800), (32771, 1, 151126016), (32896, 1, 134250496),
    (33792, 0, 134479872), (34304, 0, 168034304), (34308, 1, 168035336), (34336, 1, 168034820),
    (34352, 1, 168100356), (34358, 1, 168232460), (34560, 1, 168034562), (35328, 0, 167774224),
    (35330, 1, 167905296), (35344, 1, 167839760), (35456, 1, 167806992), (44032, 0, 135006224),
    (48128, 0, 202115088),
)
FIRST_B = 89
HAND_RANK_B = {"0": 16, "1": 64, "2": 9}
# m54a's open instance, its host control and the size of its instance a088.
A025 = (25, 512, 0, 33554432)
A085 = (85, 1024, 0, 262144)
A088 = {"k": 88, "index": 1056, "rank_x1": 1, "a1": 262660, "vars": 48587, "clauses": 286218}
M54A_UNSAT = 88


def graph_spec(k, index, rank_x1, a1):
    return {"name": f"r3g_t7_B6_o002_a{k:03d}", "kind": "main", "t": T, "d": D, "p": P, "pair": 2,
            "x1": list(X1), "r": list(GRAPH_R), "au": GRAPH_AU, "a1": a1, "rank_x1": rank_x1,
            "m52_index": index}


def batch_b_specs():
    return [graph_spec(FIRST_B + i, *row) for i, row in enumerate(GRAPH_B)]


def open_b6():
    out = dict(OPEN_M45)
    out.update(OPEN_M47)
    return out


def b6_spec(name, au):
    pi, ci = m.pair_cls(name)
    return {"name": name, "kind": "main", "t": T, "d": D, "p": P, "pair": pi, "cls": ci,
            "x1": list(X1), "r": list(B6_PAIR_R[pi]), "au": au,
            "source": "m45" if name in OPEN_M45 else "m47"}


def admissible_graph(a1):
    """a1 is in Adm of Proposition 30 (a) for pair orbit 2 (m54.admissible): kills x0 = e_0, image
    inside R, rank on X_1 at most 2, not 0, not A_u."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(GRAPH_R, v) for v in cols) and m.rank_on_x1(a1) <= 2
            and a1 != 0 and a1 != GRAPH_AU)


def plan(group):
    """[(spec, arm, cap seconds, condition, named)]; condition "a025_open" runs the entry only if
    a025 is still undecided; a named entry gets its full cap, the others a share of what is left."""
    if group == "a":
        a025, a085 = graph_spec(*A025), graph_spec(*A085)
        out = [(a025, "cadical", 600.0, None, True), (dict(a025), "xor", 600.0, "a025_open", True),
               (a085, "cadical", 60.0, None, True)]
        return out + [(sp, "cadical", 95.0, None, False) for sp in batch_b_specs()]
    return [(b6_spec(n, au), "xor", 180.0, None, False) for n, au in sorted(open_b6().items())]


# ---------- check ----------

def check(out_dir):
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}}
    # Kind graph.
    graded["graph_au"] = (m.kernel(GRAPH_AU, T) == X1 and m.column_space(GRAPH_AU, T) == GRAPH_R
                          and m.dim_meet(X1, GRAPH_R) == 3
                          and m.dim_meet(GRAPH_R, m.p_basis(P)) == 2 and not m.in_span(GRAPH_R, 1))
    reps = batch_b_specs()
    a025 = graph_spec(*A025)
    graded["graph_reps"] = (len(reps) == 89 and all(admissible_graph(s["a1"]) for s in [a025] + reps)
                            and all(m.rank_on_x1(s["a1"]) == s["rank_x1"] for s in [a025] + reps))
    by_rank = {}
    for s in reps:
        by_rank[str(s["rank_x1"])] = by_rank.get(str(s["rank_x1"]), 0) + 1
    st["batch_b_by_rank_x1"] = by_rank
    graded["graph_rank_counts"] = by_rank == HAND_RANK_B
    maps = [s["a1"] for s in [a025] + reps]
    graded["graph_distinct"] = (len(set(maps) | {a ^ GRAPH_AU for a in maps}) == 2 * len(maps)
                                and [s["m52_index"] for s in reps]
                                == sorted(s["m52_index"] for s in reps))
    cnf, _, hints, units = m.build(graph_spec(A088["k"], A088["index"], A088["rank_x1"],
                                              A088["a1"]), "cadical")
    st["a088_size"] = [cnf.nv, len(cnf.clauses), hints, units]
    graded["graph_size_as_m54"] = (cnf.nv == A088["vars"] and len(cnf.clauses) == A088["clauses"]
                                   and hints == m.HAND_HINTS["B6"] and units == T * T
                                   and m.units_consistent(cnf))
    # (B6) with d <= 2.
    specs = [b6_spec(n, au) for n, au in sorted(open_b6().items())]
    graded["b6_lists"] = (len(OPEN_M45) == 23 and len(OPEN_M47) == 28
                          and not set(OPEN_M45) & set(OPEN_M47)
                          and not set(open_b6()) & set(CLOSED_KNOWN)
                          and all(n == "r3b_t7_B6_o%03d_c%03d" % m.pair_cls(n) for n in open_b6()))
    graded["b6_reps"] = all(m.kernel(s["au"], T) == X1
                            and m.column_space(s["au"], T) == tuple(s["r"])
                            and sa.rank_f2(m.cols_of(s["au"], T)) == 3 for s in specs)
    by_d = {}
    for s in specs:
        dk = str(m.meet_d(s))
        by_d[dk] = by_d.get(dk, 0) + 1
    st["b6_by_d"] = by_d
    graded["b6_hand_d"] = by_d == HAND_D_B and all(
        m.meet_d(s) == HAND_D_PAIR[s["pair"]] for s in specs)
    per_pair = {}
    for s in specs:
        per_pair.setdefault(s["pair"], set()).add(s["au"])
    graded["b6_distinct"] = sum(len(v) for v in per_pair.values()) == len(specs)
    for arm in ("cadical", "xor"):
        c, _, h, u = m.build(specs[0], arm)
        graded[f"b6_hints_{arm}"] = h == m.HAND_HINTS["B6"] and u == 0 and m.units_consistent(c)
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- solving ----------

def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    entries = plan(group)
    shared = sum(1 for e in entries if not e[4])
    counts, a025_open, done_shared = {}, True, 0
    for spec, arm, cap, cond, named in entries:
        if cond == "a025_open" and not a025_open:
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
        if spec["name"] == graph_spec(*A025)["name"] and res["status"] in ("SAT", "UNSAT"):
            a025_open = False
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m58-predictions.md) ----------

def grade(group, out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    rows, by_key = {}, {}
    for spec, arm, _, _, named in plan(group):
        tag = m.tag_of(spec, arm)
        path = os.path.join(out_dir, tag + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows[tag] = [s, r.get("wall_seconds")]
        if s == "SAT":
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
        if named:
            continue
        key = (f"rank_x1_{spec['rank_x1']}" if group == "a"
               else f"d{m.meet_d(spec)}_{spec['source']}")
        by_key.setdefault(key, {})
        by_key[key][s] = by_key[key].get(s, 0) + 1
    out = {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows, "by": by_key,
           "any_sat_7": any(s == "SAT" for s, _ in rows.values())}
    if group == "a":
        name = graph_spec(*A025)["name"]
        a025 = [rows.get(f"{name}__{arm}", [None])[0] for arm in ("cadical", "xor")]
        batch_b = [rows.get(m.tag_of(sp, "cadical"), [None])[0] for sp in batch_b_specs()]
        out["a025"] = a025
        out["host_control_a085"] = rows.get(m.tag_of(graph_spec(*A085), "cadical"))
        out["batch_b_unsat"] = sum(s == "UNSAT" for s in batch_b)
        out["graph_unsat_of_178"] = M54A_UNSAT + out["batch_b_unsat"] + ("UNSAT" in a025)
        out["kind_graph_empty"] = out["graph_unsat_of_178"] == 178
        out["batch_b_open"] = [sp["name"] for sp, s in zip(batch_b_specs(), batch_b)
                               if s != "UNSAT"]
    else:
        out["b6_unsat"] = sorted(t.split("__")[0] for t, (s, _) in rows.items() if s == "UNSAT")
        out["b6_open"] = sorted(t.split("__")[0] for t, (s, _) in rows.items() if s != "UNSAT")
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
              f"any_sat_7 {out['any_sat_7']} by {json.dumps(out['by'], sort_keys=True)} "
              f"a025 {out.get('a025')} graph_unsat_of_178 {out.get('graph_unsat_of_178')} "
              f"b6_unsat {len(out.get('b6_unsat', []))}", flush=True)
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
