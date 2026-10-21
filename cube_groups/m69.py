# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m69: the first second-matrix splits of (B6) at t = 7 and dim V = 9 (Proposition 33,
notes/a52.md), under the rules that jobs m64 and m66 wrote down before they ran
(cube_groups/m64-predictions.md, m66-predictions.md; notes/a57.md), and the one split instance of
(B5) that job m67a left open.

What came back on 2026-10-21: m64a's rank-0 sweep (every element of N = ker phi of rank 0 on X_1)
was UNSAT for 21 of the 51 classes of (B6) with d <= 2, among them all 7 with d = 0 and 10 of the 27
open ones with d = 1, and open at 150 s for the other 30, all 13 with d = 2 among them. m64's rule:
a class whose sweep is UNSAT needs only its split instances of rank 1 and 2 on X_1 (Lemma 93 (a));
for the others the rank-0 instances carry Lemma 93 (b)'s unit clauses. m66 counted the split
exactly (88545 instances for the 51 classes; its rule: smallest classes first). m67a closed
1614 of the 1615 split instances of r3b_t7_B5_o020_c000; a561 (rank 1) stayed open.

Group a (job m69a): a561 as m67a ran it (CaDiCaL for at most 300 s, then, if open, CryptoMiniSat
  with native XOR for 300 s), then the splits of o011_c003, o011_c004 and o012_c011 (d = 0, sweep
  UNSAT): their instances of rank 1 and 2, 512 + 512 + 510.
Group b (job m69b): the splits of o009_c008 (d = 1, sweep UNSAT: 696 of rank 1 and 2), then
  o004_c001 and o006_c001 (d = 2, sweep open: all 587 each, the 42 of rank 0 with Lemma 93 (b)).
Split instances: CaDiCaL, a share of what is left, at least 10 s and at most 20 s, class by class,
the most rank on X_1 first. 150 minutes per group; instances not reached are SKIPPED (open).

A split instance is m57.py's (m42.py's encoding and hints, m53.py's unit clauses fixing A_(v_1),
m50.py's XOR encoding), imported unchanged, with A_u the class representative of m58.py's lists and
A_(v_1) the orbit root of m66.py, which recomputes the orbits deterministically: a root is the
smallest index in its orbit, so the roots do not depend on the generators drawn. In (B6) N is
span(u, v_1, v_2) (kd = 3), so Lemma 93 (b) adds A_(v_2) = 0 on X_1's three columns other than x0:
21 unit clauses (m63.py's clauses, copied below so that this job does not import the (B5) chain).

Parts:
    check   graded: m57.py's own check; for each class split, m66's structure, |G| against
            Proposition 33 (c), |Adm| against (a), closed action, orbit sizes, and its counts of
            classes by rank on X_1 against m66's run; every root admissible, of its rank, with its
            m66 index, and distinct with its sum with A_u; the split plan (count per class, ranks,
            which carry Lemma 93, order); hint and unit counts of the first instance in both arms;
            the Lemma 93 instance of the first rank-0 entry against the plain one in both arms;
            a561's A_u and admissibility and its hint and unit counts. Writes m69_reps.json.
    solve   the group's plan in order, each instance in this file's own child process.
    grade   graded checks and every SAT verified; status and time of every instance; which split
            classes are now empty; in group a whether o020_c000 of (B5) is.

Usage: python m69.py --part check|solve|grade|child [--group a|b] [--group-minutes 150]
                     [--out-dir DIR]
"""
import argparse
import json
import os
import random
import statistics
import subprocess
import sys
import time

import m66
import m58
import m57 as m
import sat_aniso as sa

T, D, P = 7, 9, 6
X1 = (8, 4, 2, 1)
NAMED_CAP = 300.0
SPLIT_CAP = 20.0
MIN_BUDGET = 10.0
REPS_FILE = "m69_reps.json"

# m67a's open instance, copied from its out/r3s_t7_B5_o020_c000_a561__cadical.json (2026-10-21):
# UNKNOWN, 86.0 s wall on an 11.4 s budget. Rank 1 on X_1, so Lemma 93 (b) adds nothing to it.
A561 = {"name": "r3s_t7_B5_o020_c000_a561", "kind": "main", "t": T, "d": D, "p": 5, "pair": 20,
        "cls": 0, "x1": [64, 4, 2, 1], "r": [4, 2, 1], "au": 133152, "a1": 794632, "rank_x1": 1,
        "m55_index": 70400, "size": 12, "parent": "r3b_t7_B5_o020_c000"}
NAMED = {"a": (A561,), "b": ()}
# m67a's split of o020_c000 without its rank-0 instances (grade.json "tail"): (instances, UNSAT).
M67A_TAIL = (1615, 1614)
O20 = "r3b_t7_B5_o020_c000"

TAILS = {"a": ("r3b_t7_B6_o011_c003", "r3b_t7_B6_o011_c004", "r3b_t7_B6_o012_c011"),
         "b": ("r3b_t7_B6_o009_c008", "r3b_t7_B6_o004_c001", "r3b_t7_B6_o006_c001")}
# Job m64a's sweep instance of each class (out/grade.json "status", 2026-10-21).
SWEEP = {"r3b_t7_B6_o011_c003": "UNSAT", "r3b_t7_B6_o011_c004": "UNSAT",
         "r3b_t7_B6_o012_c011": "UNSAT", "r3b_t7_B6_o009_c008": "UNSAT",
         "r3b_t7_B6_o004_c001": "open", "r3b_t7_B6_o006_c001": "open"}
# m66's run (m66-prop33count-v1 out/count.json) for every class split here.
GATE = {
    "r3b_t7_B6_o011_c003": {"d": 0, "order": 1176, "valid": 176128, "orbits": 552,
                            "by_rank": {"0": 40, "1": 256, "2": 256}},
    "r3b_t7_B6_o011_c004": {"d": 0, "order": 1176, "valid": 176128, "orbits": 552,
                            "by_rank": {"0": 40, "1": 256, "2": 256}},
    "r3b_t7_B6_o012_c011": {"d": 0, "order": 1344, "valid": 176128, "orbits": 553,
                            "by_rank": {"0": 43, "1": 255, "2": 255}},
    "r3b_t7_B6_o009_c008": {"d": 1, "order": 1152, "valid": 176126, "orbits": 747,
                            "by_rank": {"0": 51, "1": 348, "2": 348}},
    "r3b_t7_B6_o004_c001": {"d": 2, "order": 2048, "valid": 176126, "orbits": 587,
                            "by_rank": {"0": 42, "1": 286, "2": 259}},
    "r3b_t7_B6_o006_c001": {"d": 2, "order": 2048, "valid": 176126, "orbits": 587,
                            "by_rank": {"0": 42, "1": 286, "2": 259}},
}
# The 4 classes of (B6) with d = 1 that job m61b closed; with m58's CLOSED_KNOWN none may be split.
CLOSED_M61B = ("r3b_t7_B6_o007_c002", "r3b_t7_B6_o007_c003", "r3b_t7_B6_o007_c006",
               "r3b_t7_B6_o007_c009")

_base_build_plain = m.build_plain


# ---------- Lemma 93 (b), as m63.py ----------

def x1_cols(spec):
    """The columns at X_1's basis vectors other than x0 = e_0."""
    return [v.bit_length() - 1 for v in spec["x1"] if v != 1]


def lemma93_units(spec):
    return spec["t"] * len(x1_cols(spec)) * (spec["d"] - spec["p"] - 2)


def add_lemma93(cnf, names, spec):
    """Lemma 93 (b): A_(v_i) = 0 on X_1 for 2 <= i < kd. Returns the number of clauses added."""
    A = names[0]
    n = 0
    for i in range(2, spec["d"] - spec["p"]):
        for r in range(spec["t"]):
            for c in x1_cols(spec):
                cnf.clauses.append([-A[i][r][c]])
                n += 1
    return n


def build_plain69(spec):
    cnf, names, hints, units = _base_build_plain(spec)
    if spec.get("lemma93"):
        units += add_lemma93(cnf, names, spec)
    return cnf, names, hints, units


def install():
    """m57.build (and so m57.child) builds with the clauses of Lemma 93 (b) when a spec asks."""
    m.build_plain = build_plain69


install()


# ---------- maps and instances ----------

def mask_of(cols):
    """The t^2-bit mask (entry (r, c) at bit 7 r + c) of a matrix given by its columns (as m60)."""
    return sum(((cols[c] >> r) & 1) << (T * r + c) for c in range(T) for r in range(T))


def rank_on(a1, x1):
    """The rank of A on X_1, X_1 spanned by unit vectors: the rank of A's columns at them."""
    return len(m.rref([m.column(a1, v.bit_length() - 1) for v in x1]))


def admissible_b6(a1, au, rb, d):
    """Adm of Proposition 33 (a): kills x0, image in R, rank on X_1 at most 2, and when d >= 1 not
    0 and not A_u."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(rb, v) for v in cols) and rank_on(a1, X1) <= 2
            and (d == 0 or a1 not in (0, au)))


def admissible_b5(a1, au, x1, rb):
    """Adm of Proposition 32 (a), as m60.admissible: kills x0, maps H0 = span(e_0, ..., e_5) into
    R, rank on X_1 at most 2, rank at most 3, rank of A + A_u at most 3, not 0, not A_u."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(rb, cols[c]) for c in range(1, 6))
            and rank_on(a1, x1) <= 2 and sa.rank_f2(m.cols_of(a1, T)) <= 3
            and sa.rank_f2(m.cols_of(a1 ^ au, T)) <= 3 and a1 != 0 and a1 != au)


def distinct_with_au(maps, au):
    return len(set(maps) | {a ^ au for a in maps}) == 2 * len(maps)


def r_of(name):
    return tuple(m58.B6_PAIR_R[m66.pair_of(name)])


def class_reps(name, rng):
    """m66's count of the class: (its record without the roots, [rep]) with rep = {index, cols,
    a1, rank_x1, size} in m66's order (by index)."""
    r = m66.count_class(name, m66.classes()[name], rng)
    mp = m66.Maps(r_of(name))
    reps = [{"index": i, "cols": list(mp.cols(i)), "a1": mask_of(mp.cols(i)), "rank_x1": rk,
             "size": s} for i, rk, s in r.get("reps", [])]
    return {k: v for k, v in r.items() if k != "reps"}, reps


def split_spec(name, k, rep, lemma93=False):
    """m58's instance of the class with A_(v_1) fixed to the k-th root; r3l_ when it carries
    Lemma 93 (b)."""
    pi, ci = m.pair_cls(name)
    sp = m58.b6_spec(name, m66.classes()[name])
    sp.update({"name": f"{'r3l' if lemma93 else 'r3s'}_t7_B6_o{pi:03d}_c{ci:03d}_a{k:04d}",
               "a1": rep["a1"], "rank_x1": rep["rank_x1"], "m66_index": rep["index"],
               "size": rep["size"], "parent": name})
    if lemma93:
        sp["lemma93"] = True
    return sp


def drop_rank0(name):
    return SWEEP[name] == "UNSAT"


def planned(name):
    by = GATE[name]["by_rank"]
    return by["1"] + by["2"] + (0 if drop_rank0(name) else by["0"])


def tail_order(reps):
    """Indices of a class's representatives, the most rank on X_1 first, then by m66 order."""
    return sorted(range(len(reps)), key=lambda k: (-reps[k]["rank_x1"], k))


def plan(group, reps):
    """[(spec, arm, cap seconds, condition, named)]; condition "open" runs the entry only if the
    same instance is still undecided; a named entry gets its full cap, the others a share of what
    is left."""
    out = []
    for sp in NAMED[group]:
        out += [(dict(sp), "cadical", NAMED_CAP, None, True),
                (dict(sp), "xor", NAMED_CAP, "open", True)]
    for name in TAILS[group]:
        for k in tail_order(reps[name]):
            rep = reps[name][k]
            if rep["rank_x1"] == 0 and drop_rank0(name):
                continue
            out.append((split_spec(name, k, rep, rep["rank_x1"] == 0), "cadical", SPLIT_CAP,
                        None, False))
    return out


def load_reps(out_dir):
    with open(os.path.join(out_dir, REPS_FILE)) as f:
        return json.load(f)


# ---------- check ----------

def probe93(sp):
    """The Lemma 93 instance is the plain one plus exactly lemma93_units negative unit clauses on
    A_(v_2), ..., A_(v_(kd-1)) at X_1's columns, in both arms; returns ({arm: ok}, {arm: counts})."""
    ok, counts = {}, {}
    base = {k: v for k, v in sp.items() if k != "lemma93"}
    base["name"] = sp["name"].replace("r3l_", "r3s_", 1)
    for arm in ("cadical", "xor"):
        c0, _, h0, u0 = m.build(base, arm)
        c1, names, h1, u1 = m.build(sp, arm)
        extra = c1.clauses[len(c0.clauses):]
        a_vars = {names[0][i][r][c] for i in range(2, sp["d"] - sp["p"]) for r in range(T)
                  for c in x1_cols(sp)}
        counts[arm] = [c1.nv, len(c1.clauses), h1, u1, len(extra)]
        ok[arm] = (c1.nv == c0.nv and c1.clauses[:len(c0.clauses)] == c0.clauses
                   and len(extra) == lemma93_units(sp) == u1 - u0
                   and h1 == h0 == m.HAND_HINTS["B6"]
                   and all(len(cl) == 1 and cl[0] < 0 and -cl[0] in a_vars for cl in extra)
                   and len({-cl[0] for cl in extra}) == len(extra) and m.units_consistent(c1)
                   and len(getattr(c1, "xors", ())) == len(getattr(c0, "xors", ())))
    return ok, counts


def check(group, out_dir):
    install()
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}, "split": {}}
    cl = m66.classes()
    names = TAILS[group]
    graded["lists"] = (set(GATE) == set(SWEEP) == set(TAILS["a"]) | set(TAILS["b"])
                       and not set(TAILS["a"]) & set(TAILS["b"]) and set(names) <= set(cl)
                       and not set(names) & (set(m58.CLOSED_KNOWN) | set(CLOSED_M61B))
                       and all(m58.HAND_D_PAIR[m66.pair_of(n)] == GATE[n]["d"] for n in names)
                       and all(sum(GATE[n]["by_rank"].values()) == GATE[n]["orbits"]
                               for n in names))
    rng, reps = random.Random(69), {}
    for name in names:
        tag = name[10:]
        gate = GATE[name]
        r, rr = class_reps(name, rng)
        st["split"][tag] = r
        s = r["structure"]
        graded["split_" + tag] = (
            "error" not in r and s["rank_au"] == 3 and s["ker_is_x1"] and s["image_is_r"]
            and s["d"] == s["d_hand"] == gate["d"] and r["group_checked"]
            and r["order"] == r["order_hand"] == gate["order"]
            and r["valid"] == r["valid_hand"] == gate["valid"] and r["action_closed"]
            and r["tables_match"] and r["sizes_ok"] and r["orbits"] == gate["orbits"]
            and r["orbits_by_rank_x1"] == gate["by_rank"])
        au, rb = cl[name], r_of(name)
        mp = m66.Maps(rb)
        graded["split_reps_" + tag] = (
            len(rr) == gate["orbits"]
            and [x["index"] for x in rr] == sorted(x["index"] for x in rr)
            and all(mp.index(tuple(x["cols"])) == x["index"]
                    and m66.cols_of_mask(x["a1"]) == tuple(x["cols"])
                    and admissible_b6(x["a1"], au, rb, gate["d"])
                    and rank_on(x["a1"], X1) == x["rank_x1"] == mp.rank_x1(x["index"])
                    for x in rr)
            and distinct_with_au([x["a1"] for x in rr], au))
        reps[name] = rr
    p = plan(group, reps)
    tail_specs = [e[0] for e in p if not e[4]]
    per = {n: [s for s in tail_specs if s["parent"] == n] for n in names}
    graded["plan"] = (
        all(len(per[n]) == planned(n) for n in names) and len(tail_specs) == sum(map(len, per.values()))
        and len({s["name"] for s in tail_specs}) == len(tail_specs)
        and all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail_specs)
        and all(s["rank_x1"] > 0 for n in names if drop_rank0(n) for s in per[n])
        and all([s["rank_x1"] for s in per[n]] == sorted((s["rank_x1"] for s in per[n]),
                                                          reverse=True) for n in names)
        and [s["parent"] for s in tail_specs] == [n for n in names for _ in per[n]])
    probes = {}
    for arm in ("cadical", "xor"):
        sp = tail_specs[0]
        c, _, h, u = m.build(sp, arm)
        probes["first_" + arm] = [c.nv, len(c.clauses), h, u, len(getattr(c, "xors", ()))]
        graded["probe_first_" + arm] = (h == m.HAND_HINTS["B6"] and u == T * T
                                        and not sp.get("lemma93") and m.units_consistent(c)
                                        and (arm == "cadical" or len(c.xors) > 0))
    l93 = [s for s in tail_specs if s.get("lemma93")]
    graded["lemma93_where_planned"] = bool(l93) == any(not drop_rank0(n) for n in names)
    if l93:
        ok, counts = probe93(l93[0])
        for arm, v in ok.items():
            graded["probe93_" + arm] = v and lemma93_units(l93[0]) == T * 3
        probes["lemma93"] = counts
    for sp in NAMED[group]:
        au, x1, rb = sp["au"], tuple(sp["x1"]), tuple(sp["r"])
        graded["named_" + sp["name"]] = (
            m.kernel(au, T) == x1 and m.column_space(au, T) == rb and sa.rank_f2(m.cols_of(au, T)) == 3
            and admissible_b5(sp["a1"], au, x1, rb) and rank_on(sp["a1"], x1) == sp["rank_x1"] == 1
            and sp["name"].startswith(sp["parent"].replace("r3b_", "r3s_", 1) + "_a"))
        for arm in ("cadical", "xor"):
            c, _, h, u = m.build(dict(sp), arm)
            probes["named_" + arm] = [c.nv, len(c.clauses), h, u]
            graded["probe_named_" + arm] = (h == m.HAND_HINTS["B5"] and u == T * T
                                            and m.units_consistent(c))
    st["probes"] = probes
    st["plan"] = {"named": len(NAMED[group]), "tail": len(tail_specs), "lemma93": len(l93),
                  "per_class": {n: len(per[n]) for n in names}}
    with open(os.path.join(out_dir, REPS_FILE), "w") as f:
        json.dump(reps, f)
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


# ---------- solving ----------

def solve_one(spec, arm, budget, out_dir):
    """m57.solve_one with this file as the child, so that the child builds with Lemma 93."""
    tag = m.tag_of(spec, arm)
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--arm", arm, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({k: v for k, v in spec.items() if k != "kind"})
    res.update({"kind": spec["kind"], "arm": arm, "wall_seconds": round(time.time() - start, 2),
                "budget_seconds": round(budget, 1)})
    if res["status"] == "SAT":
        m.verify(spec, res)
    with open(os.path.join(out_dir, tag + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {tag}: {res['status']} {res['wall_seconds']} s", flush=True)
    return res


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
            res = solve_one(spec, arm, budget, out_dir)
        if not named:
            done_shared += 1
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m69-predictions.md) ----------

def grade(group, out_dir):
    install()
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
        reps = load_reps(out_dir)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
        return {"group": group, "graded": graded, "ungraded": ungraded, "rows": {},
                "any_sat_7": False}
    rows, specs = {}, {}
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
    status = {}
    for n in specs:
        vals = [v[0] for v in rows.get(n, {}).values()]
        status[n] = ("UNSAT" if "UNSAT" in vals else "SAT" if "SAT" in vals
                     else "SKIPPED" if vals and all(v == "SKIPPED" for v in vals)
                     else "open" if vals else "missing")
    named = [n for n, (_, nm) in specs.items() if nm]
    classes = {}
    for name in TAILS[group]:
        mine = [n for n, (sp, nm) in specs.items() if not nm and sp["parent"] == name]
        by_rank, walls = {}, []
        for n in mine:
            key = str(specs[n][0]["rank_x1"])
            by_rank.setdefault(key, {})
            by_rank[key][status[n]] = by_rank[key].get(status[n], 0) + 1
            if status[n] == "UNSAT":
                walls.append(rows[n]["cadical"][1])
        unsat = sum(status[n] == "UNSAT" for n in mine)
        classes[name] = {
            "planned": len(mine), "unsat": unsat,
            "open": [n for n in mine if status[n] != "UNSAT"],
            "skipped": sum(status[n] in ("SKIPPED", "missing") for n in mine),
            "by_rank": by_rank, "rank0_dropped_by_sweep": drop_rank0(name),
            "median_unsat_wall": round(statistics.median(walls), 2) if walls else None,
            "max_unsat_wall": max(walls) if walls else None,
            "empty": len(mine) == planned(name) and unsat == len(mine)}
    out = {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows,
           "named": {n: status[n] for n in named},
           "named_unsat": sum(status[n] == "UNSAT" for n in named), "classes": classes,
           "b6_closed": [n for n, c in classes.items() if c["empty"]],
           "any_sat_7": any(s == "SAT" for s in status.values())}
    if group == "a":
        total, before = M67A_TAIL
        here = sum(status[n] == "UNSAT" for n in named)
        out["o020"] = {"name": O20, "total": total, "unsat": before + here,
                       "empty": before + here == total}
        out["b5_closed"] = [O20] if out["o020"]["empty"] else []
    return out


def summary_line(out):
    cls = {n[10:]: {k: v for k, v in c.items() if k != "open"} for n, c in out.get("classes", {}).items()}
    opened = {n[10:]: c["open"][:30] for n, c in out.get("classes", {}).items()}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} "
            f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
            f"any_sat_7 {out['any_sat_7']} named {json.dumps(out.get('named'))} "
            f"b6_closed {out.get('b6_closed')} o020 {json.dumps(out.get('o020'))} "
            f"classes {json.dumps(cls, sort_keys=True)} open {json.dumps(opened, sort_keys=True)}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade", "child"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--arm")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    install()
    if args.part == "child":
        m.child(json.loads(args.spec), args.arm, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group, args.group_minutes * 60, args.out_dir)
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
