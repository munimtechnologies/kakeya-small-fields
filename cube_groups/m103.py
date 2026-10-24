# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m103: which cases of the rank-0 split of (B7)_8 (t = 8, dim V = 11) the solver refutes, by
the number of subspaces of Q = X / X_1 that the commuting space T(N) leaves invariant
(notes/a95.md, cube_groups/m103-predictions.md).

What came back on 2026-10-24 (job m102, notes/a95.md): every graded check held, all t1 instances
(dim T(N) = 1) were UNKNOWN at 120 s, and the pilot of o000_c000 decided 30 of its 68 cases (UNSAT)
within 45 s. Read by hand, the split is clean: the 21 cases whose T(N) leaves at most 4 subspaces
of Q invariant were all UNSAT, the 17 with 8 or 10 invariant subspaces were all UNKNOWN, and those
with 6 were mixed (9 of 30). In o011_c000 (d = 0) only 1 of 54 was decided.

This job checks that reading by machine and tests it on new cases:

    check   the 16 subspaces of F_2^3; for each of the 255 + 183 spaces of Lemma 107 its type and
            its number of invariant subspaces against the hand table of Lemma 108; the same
            numbers for m102's pilot cases (statuses copied below from job m102's output)
    run     "control" job m102's positive controls of the shard again (m102.control_list);
            shard a: "d3" every t2 / t3 case of the other two d = 3 classes (o001_c000,
            o002_c000); "rest" the 27 cases of o000_c000 that m102's pilot skipped; "deep" four
            cases of o000_c000 with 8 or 10 invariant subspaces at a larger cap.
            shard b: "low" every case of o011_c005 and the cases with at most 4 invariant
            subspaces of o004_c000 (d = 2) and o007_c008 (d = 1); "o011" the cases with at most 4
            invariant subspaces of o011_c000 at a larger cap
    grade   the graded checks of m103-predictions.md and the tables by class, count and type

Usage: python m103.py --part check|run|grade --shard a|b [--which PART] [--cap-seconds S]
       [--minutes M] [--out-dir D]
"""
import argparse
import functools
import itertools
import json
import os
import time

import m100
import m102
import sat_aniso as sa

Q, I3, GL3 = m102.Q, m102.I3, m102.GL3

# the GL_3-orbit of span(I, M) has the size of the similarity class of M (Lemma 107 (a))
NAMES2 = {21: "nil1", 24: "irr", 28: "proj", 42: "nil3", 56: "x(x2+x+1)", 84: "x2(x+1)"}
# Lemma 108 (by hand): the number of subspaces of F_2^3 invariant under each type
HAND_INV2 = {"nil1": 8, "irr": 2, "proj": 10, "nil3": 4, "x(x2+x+1)": 4, "x2(x+1)": 6}
HAND_INV3 = {"F8": 2, "F2xF4": 4, "F2^3": 8, "F2xF2[x]/x2": 6, "F2[x]/x3": 4, "rad2_image": 6,
             "rad2_kernel": 6}
HAND_SIZE3 = {"F8": 8, "F2xF4": 28, "F2^3": 28, "F2xF2[x]/x2": 84, "F2[x]/x3": 21, "rad2_image": 7,
              "rad2_kernel": 7}

# job m102's pilots (compete-results m102a-b7-tsplit-v1 and m102b-b7-tsplit-v1, run-05), 45 s each
M102_PILOT = {
    "r3b_t8_B7_o000_c000": {
        "UNSAT": ["t3_m001_128", "t3_m001_176", "t3_m002_004", "t3_m002_128", "t3_m002_132",
                  "t3_m004_034", "t3_m005_130", "t3_m005_178", "t3_m006_161", "t3_m006_163",
                  "t3_m011_017", "t3_m015_049", "t3_m064_128", "t3_m064_136", "t3_m064_144",
                  "t3_m065_184", "t3_m072_145", "t3_m072_161", "t3_m072_169", "t3_m075_145",
                  "t3_m078_161", "t3_m094_187", "t3_m098_140", "t3_m106_157",
                  "t2_m011", "t2_m012", "t2_m015", "t2_m066", "t2_m069", "t2_m071"],
        "UNKNOWN": ["t3_m001_016", "t3_m001_032", "t3_m001_048", "t3_m001_144", "t3_m001_160",
                    "t3_m002_017", "t3_m002_021", "t3_m002_145", "t3_m002_149", "t3_m004_032",
                    "t3_m004_048", "t3_m005_048", "t3_m005_146", "t3_m005_162", "t3_m006_049",
                    "t3_m006_144", "t3_m065_144", "t3_m065_168", "t3_m079_161", "t3_m121_151",
                    "t2_m001", "t2_m002", "t2_m004", "t2_m005", "t2_m006", "t2_m010", "t2_m013",
                    "t2_m014", "t2_m017", "t2_m020", "t2_m021", "t2_m023", "t2_m064", "t2_m065",
                    "t2_m067", "t2_m068", "t2_m070", "t2_m072"]},
    "r3b_t8_B7_o011_c000": {
        "UNSAT": ["t3_m004_034"],
        "UNKNOWN": ["t3_m001_016", "t3_m001_032", "t3_m001_048", "t3_m001_128", "t3_m001_144",
                    "t3_m001_160", "t3_m001_176", "t3_m002_004", "t3_m002_021", "t3_m002_128",
                    "t3_m002_132", "t3_m004_016", "t3_m004_018", "t3_m004_032", "t3_m004_048",
                    "t3_m005_016", "t3_m005_032", "t3_m005_048", "t3_m005_130", "t3_m005_178",
                    "t3_m007_018", "t3_m007_130", "t3_m007_179", "t3_m008_032", "t3_m008_096",
                    "t3_m016_068", "t3_m016_069", "t3_m021_040", "t3_m021_047", "t3_m024_100",
                    "t3_m024_109", "t3_m040_084", "t3_m040_092", "t3_m084_130", "t3_m084_170",
                    "t3_m086_130", "t3_m094_187",
                    "t2_m001", "t2_m002", "t2_m004", "t2_m005", "t2_m007", "t2_m008", "t2_m010",
                    "t2_m011", "t2_m012", "t2_m013", "t2_m014", "t2_m015", "t2_m016", "t2_m020",
                    "t2_m021", "t2_m022"]}}
PILOT_PAIRS = {"r3b_t8_B7_o000_c000": (0, 0), "r3b_t8_B7_o011_c000": (11, 0)}
DEEP = ["t3_m001_016", "t3_m005_048", "t2_m001", "t2_m002"]
# (pair, class, which cases): "all" or "le4" (at most 4 invariant subspaces)
PARTS = {("a", "d3"): [(1, 0, "all"), (2, 0, "all")],
         ("a", "rest"): [(0, 0, "rest")],
         ("a", "deep"): [(0, 0, "deep")],
         ("b", "low"): [(11, 5, "all"), (4, 0, "le4"), (7, 8, "le4")],
         ("b", "o011"): [(11, 0, "le4")]}


# ---------- types and invariant subspaces ----------

def mm(a, b):
    return m102.mm3(a, b)


def span_of(gens):
    s = {0}
    for g in gens:
        s |= {x ^ g for x in s}
    return tuple(sorted(s))


def subspaces():
    """The 16 subspaces of F_2^3, each as a frozenset of vectors."""
    subs = {frozenset(span_of(gens)) for k in range(Q + 1)
            for gens in itertools.combinations(range(1, 1 << Q), k)}
    return sorted(subs, key=lambda u: (len(u), sorted(u)))


SUBS = subspaces()


def inv_count(space):
    """The number of subspaces of Q invariant under every matrix of space."""
    return sum(1 for u in SUBS if all(sa.mat_apply(m, x, Q) in u for m in space for x in u))


@functools.lru_cache(maxsize=None)
def orbit_size(space):
    return len({m102.conj_space(g, space) for g in GL3})


def alg_type(space):
    """The type of span(I) (scalar), of span(I, M) (by the size of its GL_3-orbit) or of a
    3-dimensional commutative subalgebra (by its idempotents and nilpotents)."""
    if len(space) == 2:
        return "scalar"
    if len(space) == 4:
        return NAMES2.get(orbit_size(space), "other")
    idem = sum(1 for e in space if mm(e, e) == e)
    nil = [n for n in space if mm(n, mm(n, n)) == 0]
    simple = {(2, 1): "F8", (4, 1): "F2xF4", (8, 1): "F2^3", (4, 2): "F2xF2[x]/x2"}
    key = (idem, len(nil))
    if key in simple:
        return simple[key]
    if key != (2, 4):
        return "other"
    if any(mm(n, n) != 0 for n in nil):
        return "F2[x]/x3"
    images = {frozenset(sa.mat_apply(n, x, Q) for x in range(1 << Q)) for n in nil if n}
    return "rad2_image" if len(images) == 1 else "rad2_kernel"


def space_of(case):
    m2, m3 = case["maps"]
    if case["kind"] == "t1":
        return span_of([I3])
    if case["kind"] == "t2":
        return span_of([I3, m3])
    return span_of([I3, m2, m3])


def describe(case):
    s = space_of(case)
    return inv_count(s), alg_type(s)


# ---------- the cases of each part ----------

def selected(shard, which):
    """[(spec, case)] for one part, in m102's order (t3 cases, then t2)."""
    out = []
    for pi, ci, how in PARTS[(shard, which)]:
        spec = m100.spec_of(pi, ci)
        cases = m102.class_cases(spec)[1:]
        if how == "le4":
            cases = [c for c in cases if describe(c)[0] <= 4]
        elif how == "rest":
            seen = {lab for labs in M102_PILOT[spec["name"]].values() for lab in labs}
            cases = [c for c in cases if m102.case_label(c) not in seen]
        elif how == "deep":
            by_label = {m102.case_label(c): c for c in cases}
            cases = [by_label[lab] for lab in DEEP]
        out += [(spec, c) for c in cases]
    return out


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


# ---------- the parts ----------

def run_check(shard, out_dir):
    g = {}
    sizes = {}
    for u in SUBS:
        sizes[len(u)] = sizes.get(len(u), 0) + 1
    g["subspaces_16"] = len(SUBS) == 16 and sizes == {1: 1, 2: 7, 4: 7, 8: 1}
    two, three = m102.t_spaces()
    t2 = [(alg_type(s), inv_count(s), orbit_size(s)) for s in two]
    t3 = [(alg_type(s), inv_count(s), orbit_size(s)) for s in three]
    g["inv_dim2"] = all(name in HAND_INV2 and inv == HAND_INV2[name] for name, inv, _ in t2)
    g["inv_dim3"] = all(name in HAND_INV3 and inv == HAND_INV3[name] for name, inv, _ in t3)
    count3 = {}
    for name, _, _ in t3:
        count3[name] = count3.get(name, 0) + 1
    g["types_dim3"] = (count3 == HAND_SIZE3
                       and all(size == HAND_SIZE3.get(name) for name, _, size in t3))
    g["scalar_16"] = inv_count(span_of([I3])) == 16
    cross, labels_ok = {}, True
    for name, st in M102_PILOT.items():
        spec = m100.spec_of(*PILOT_PAIRS[name])
        cases = {m102.case_label(c): c for c in m102.class_cases(spec)}
        tab = {}
        for status, labels in st.items():
            for lab in labels:
                if lab not in cases:
                    labels_ok = False
                    continue
                inv, typ = describe(cases[lab])
                tally(tab, f"inv{inv} {typ}", status)
                tally(tab, f"inv{inv}", status)
        cross[name] = tab
    g["m102_labels_found"] = labels_ok
    o000 = cross["r3b_t8_B7_o000_c000"]
    le4 = [v for k, v in o000.items() if " " not in k and int(k[3:]) <= 4]
    ge8 = [v for k, v in o000.items() if " " not in k and int(k[3:]) >= 8]
    g["o000_le4_all_unsat"] = bool(le4) and all(set(v) == {"UNSAT"} for v in le4)
    g["o000_ge8_all_unknown"] = bool(ge8) and all(set(v) == {"UNKNOWN"} for v in ge8)
    plan = {}
    for (sh, which) in PARTS:
        if sh != shard:
            continue
        rows = selected(shard, which)
        plan[which] = {}
        for spec, case in rows:
            tally(plan[which], spec["name"], f"inv{describe(case)[0]}")
    info = {"graded": g, "m102_cross": cross, "plan": plan,
            "dim2": sorted({(n, i, s) for n, i, s in t2}),
            "dim3": sorted({(n, i, s) for n, i, s in t3})}
    with open(os.path.join(out_dir, f"m103{shard}_check.json"), "w") as f:
        json.dump(info, f, indent=1)
    bad = sorted(k for k, v in g.items() if not v)
    sizes_plan = {w: sum(sum(v.values()) for v in p.values()) for w, p in plan.items()}
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} plan "
          f"{json.dumps(sizes_plan, sort_keys=True)} m102_o000 "
          f"{json.dumps({k: v for k, v in o000.items() if ' ' not in k}, sort_keys=True)}",
          flush=True)


def append_row(out_dir, shard, row):
    rows = m100.load(out_dir, f"m103{shard}_rows.json") or []
    rows.append(row)
    with open(os.path.join(out_dir, f"m103{shard}_rows.json"), "w") as f:
        json.dump(rows, f, indent=1)


def run_part(shard, which, cap, minutes, out_dir):
    if which == "control":
        items = [(m100.spec_of(pi, ci), case, mode)
                 for (pi, ci), case, mode in m102.control_list(shard)]
    else:
        items = [(spec, case, "sweep") for spec, case in selected(shard, which)]
    start = time.time()
    tab, skipped = {}, 0
    for spec, case, mode in items:
        if time.time() - start > minutes * 60:
            skipped += 1
            continue
        row = m102.solve_one(spec, case, mode, cap, out_dir, which)
        row["inv"], row["type"] = describe(case)
        append_row(out_dir, shard, row)
        tally(tab, f"{spec['name'][10:]} inv{row['inv']}", row["status"])
    print(f"SUMMARY run {shard} {which} skipped {skipped} {json.dumps(tab, sort_keys=True)} "
          f"cap {cap}", flush=True)


def grade(shard, out_dir):
    g = {}
    chk = m100.load(out_dir, f"m103{shard}_check.json")
    if chk is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    rows = m100.load(out_dir, f"m103{shard}_rows.json") or []
    g["rows_present"] = bool(rows)
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    ctrl = [r for r in rows if r["part"] == "control"]
    g["controls_sat"] = bool(ctrl) and all(r["status"] == "SAT" and r.get("verified") for r in ctrl)
    for r in rows:
        if r["status"] == "SAT":
            g["verified_" + r["instance"] + "_" + r["mode"]] = bool(r.get("verified"))
    by_inv, by_type = {}, {}
    for r in rows:
        tally(by_inv, f"{r['part']} {r['name'][10:]} inv{r['inv']}", r["status"])
        tally(by_type, f"{r['part']} inv{r['inv']} {r['type']}", r["status"])
    return {"graded": g, "by_inv": by_inv, "by_type": by_type,
            "rows": {r["instance"]: [r["status"], r["wall_seconds"], r["inv"], r["type"]]
                     for r in rows},
            "unsat": sorted(r["instance"] for r in rows if r["status"] == "UNSAT")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "run", "grade"], default="check")
    ap.add_argument("--shard", choices=["a", "b"], default="a")
    ap.add_argument("--which", choices=sorted({w for _, w in PARTS} | {"control"}))
    ap.add_argument("--cap-seconds", type=float, default=60.0)
    ap.add_argument("--minutes", type=float, default=30.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "run":
        run_part(args.shard, args.which, args.cap_seconds, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        with open(os.path.join(args.out_dir, f"m103{args.shard}_grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} "
              f"failed {bad[:12]} by_inv {json.dumps(out['by_inv'], sort_keys=True)} "
              f"unsat {len(out['unsat'])}", flush=True)


if __name__ == "__main__":
    main()
