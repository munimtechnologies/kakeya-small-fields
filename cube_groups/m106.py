# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m106: which anisotropy clauses the refutations in the rank-0 case of (B7)_8 (t = 8,
dim V = 11) really need, and whether anisotropy on N alone decides the cases the full CNF left
undecided (notes/a98.md, cube_groups/m106-predictions.md).

What came back on 2026-10-25 (jobs m105a-e, notes/a98.md): of the 1,078 k <= 4 cases of the twelve
d = 2 classes, 1,050 were UNSAT within 45 s and 28 UNKNOWN; none SAT, none skipped. In job m105e,
the six core cases (one per type with k <= 4) were UNSAT at every one of the eleven levels,
including W = N (anisotropy on 15 vectors only) and W = span(h_5, h_6, h_7) (7 vectors, without
N), and four k = 6 cases were UNSAT at "out3" and "in4". The positive control (o000_c000, t2 with
M = J, W = N) was SAT with a verified model.

A CNF that keeps every condition of a case but asks sigma(h) != 0 only for h in a set S of vectors
of V is implied by the full CNF, so UNSAT for some S means UNSAT for the case.

Parts:

    check     shard a: the 28 UNKNOWN cases of jobs m105a-d rebuilt (each k <= 4, d = 2); shard b:
              the k <= 4 cases of o007_c008 (d = 1), o011_c000 and o011_c005 (d = 0), 37 + 30 + 6;
              shard e: the six core and four k = 6 cases, the vector sets N and span(h_5, h_6, h_7)
    run       shard a: each of the 28 with anisotropy on N ("n", 90 s), with none ("none", 30 s), then
              m102's sweep CNF (full anisotropy, 120 s: the rule of m105-predictions.md)
              shard b: two positive controls at "n", then the 73 cases at "n" (60 s)
              shard e: the control at "none" and "n"; then for each core case and each k = 6 case:
              "none", and a deletion-minimal set of vectors S inside N and inside span(h_5, h_6,
              h_7) with the CNF still UNSAT (60 s per solve)
    grade     the graded checks of m106-predictions.md

Usage: python m106.py --part check|run|grade --shard a|b|e [--cap-seconds S] [--minutes M]
       [--out-dir D]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import m100
import m101
import m102
import m103
import m104
import m105
import sat_aniso as sa

T, D, KD = m102.T, m102.D, m102.KD
# the basis of V in the normal form: u, v_1, v_2, v_3 span N, h_j has index 3 + j
BASIS = ("u", "v1", "v2", "v3", "h1", "h2", "h3", "h4", "h5", "h6", "h7")
# jobs m105a-d (compete-results/m105{a..d}-b7-d2-v1, m105*_grade.json): UNKNOWN at 45 s
UNKNOWN_D2 = (
    "r3b_t8_B7_o004_c001_t3_m002_132", "r3b_t8_B7_o005_c000_t2_m132", "r3b_t8_B7_o005_c001_t2_m134",
    "r3b_t8_B7_o005_c001_t3_m024_109", "r3b_t8_B7_o005_c002_t3_m002_132",
    "r3b_t8_B7_o005_c003_t2_m038", "r3b_t8_B7_o006_c001_t2_m034", "r3b_t8_B7_o006_c001_t2_m132",
    "r3b_t8_B7_o004_c001_t3_m004_034", "r3b_t8_B7_o005_c002_t2_m163",
    "r3b_t8_B7_o005_c002_t3_m004_034", "r3b_t8_B7_o005_c003_t2_m132",
    "r3b_t8_B7_o005_c003_t3_m002_132", "r3b_t8_B7_o006_c001_t3_m002_132",
    "r3b_t8_B7_o003_c002_t2_m034", "r3b_t8_B7_o003_c002_t2_m163", "r3b_t8_B7_o003_c002_t3_m006_163",
    "r3b_t8_B7_o005_c001_t2_m034", "r3b_t8_B7_o005_c002_t2_m132",
    "r3b_t8_B7_o005_c002_t3_m006_163", "r3b_t8_B7_o005_c003_t3_m004_034",
    "r3b_t8_B7_o006_c001_t3_m004_034", "r3b_t8_B7_o004_c001_t2_m034",
    "r3b_t8_B7_o004_c001_t2_m132", "r3b_t8_B7_o005_c001_t2_m132",
    "r3b_t8_B7_o005_c001_t3_m004_034", "r3b_t8_B7_o005_c002_t2_m034",
    "r3b_t8_B7_o005_c003_t2_m034")
# shard b: (pair, class) and the k <= 4 counts of job m104a (m104_count.json)
TRANSFER = ((7, 8), (11, 0), (11, 5))
TRANSFER_LE4 = {"r3b_t8_B7_o007_c008": 37, "r3b_t8_B7_o011_c000": 30, "r3b_t8_B7_o011_c005": 6}


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


def vec_name(h):
    """A vector of V as a sum of basis names, e.g. 'u+v2'; 0 is '0'."""
    return "+".join(BASIS[i] for i in range(D) if (h >> i) & 1) or "0"


def deletion_order(masks):
    """Vectors with more basis terms are tried for removal first, so simple ones tend to stay."""
    return sorted(masks, key=lambda h: (-bin(h).count("1"), -h))


# ---------- the cases ----------

def case_of(instance):
    """(spec, case) of an instance name such as r3b_t8_B7_o004_c001_t3_m002_132."""
    name, label = instance[:19], instance[20:]
    pi, ci = int(name[11:14]), int(name[16:19])
    spec = m100.spec_of(pi, ci)
    if spec["name"] != name:
        raise ValueError(f"{instance}: class name {spec['name']}")
    return spec, m105.cases_by_label(pi, ci)[label]


def transfer_cases():
    out = []
    for pi, ci in TRANSFER:
        spec = m100.spec_of(pi, ci)
        out += [(spec, c) for c in m102.class_cases(spec)[1:] if m105.le4(c)]
    return out


def transfer_controls():
    """Two cases known SAT with anisotropy on N: o000_c000 t2 with M = J (jobs m102, m104c, m105e)
    and o011_c000 t3_m001_016 (job m103b's relax_n control)."""
    return [(m100.spec_of(0, 0), m102.case_t2(m102.J3)), (m100.spec_of(11, 0), m102.case_t3(1, 16))]


def min_items():
    """[(spec, case, part)]: the six core cases of m104, then the four k = 6 cases of m105."""
    items = [(m100.spec_of(pi, ci), m105.cases_by_label(pi, ci)[lab], "core")
             for pi, ci, lab in m104.CORE]
    spec, cs = m105.k6_cases()
    return items + [(spec, c, "k6") for c in cs]


def n_masks():
    return m104.w_masks(range(KD))


def out_masks(spec):
    return m104.w_masks(m104.h_split(spec)[0])


# ---------- the CNF with anisotropy on a set of vectors ----------

def add_aniso_masks(cnf, names, t, masks):
    """sigma(h) != 0 for each h in masks, as m101.add_aniso_on does on a whole subspace:
    sigma(h) = sum of s_i + sum of beta(e_i, e_j) over i < j in h. Returns the number of clauses."""
    S, B = names[1], names[2]
    for h in masks:
        bits = [i for i in range(D) if (h >> i) & 1]
        ys = []
        for r in range(t):
            vs = [S[i][r] for i in bits] + [B[(i, j)][r] for i, j in itertools.combinations(bits, 2)]
            ys.append(cnf.xor_def(vs))
        cnf.clauses.append(ys)
    return len(masks)


def child(spec, case, masks, path):
    from pysat.solvers import Solver
    cnf, names, _ = m102.build(spec, case, "relax")
    n_aniso = add_aniso_masks(cnf, names, T, masks)
    start = time.time()
    used = None
    for name in sa.SOLVERS:
        try:
            s = Solver(name=name, bootstrap_with=cnf.clauses)
            used = name
            break
        except Exception:
            continue
    if used is None:
        raise RuntimeError("no SAT solver available")
    ok = s.solve()
    res = {"status": "SAT" if ok else "UNSAT", "solver": used, "vars": cnf.nv,
           "clauses": len(cnf.clauses), "aniso_clauses": n_aniso,
           "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, T, D)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_masks(spec, case, masks, tag, part, cap, out_dir):
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--case", json.dumps(case), "--masks", json.dumps(list(masks)), "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=cap, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    inv, typ = m104.k_and_type(m103.space_of(case))
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({"instance": m102.inst_name(spec, case), "name": spec["name"], "tag": tag,
                "part": part, "masks": list(masks), "kind": case["kind"], "maps": case["maps"],
                "dmeet": spec["dmeet"], "inv": inv, "type": typ,
                "wall_seconds": round(time.time() - start, 2), "budget_seconds": cap})
    if res["status"] == "SAT":
        chk = m101.check_model(spec, res)
        chk.update(m102.extra_checks(spec, case, res))
        _, sv = sa.tables(res["A"], res["s"], {(i, k): v for i, k, v in res["B"]}, D)
        chk["aniso_masks"] = all(sv[h] for h in masks)
        row["check"] = chk
        row["verified"] = chk["aniso_masks"] and all(chk[k] for k in m102.needed(spec, "relax"))
        row["unsatisfied"] = [vec_name(h) for h in range(1, 1 << D) if not sv[h]][:12]
    print(f"solve {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


def minimize(masks, oracle):
    """A deletion-minimal sublist of masks for which oracle(list) is 'UNSAT', or None if the whole
    list is not. Returns (kept, why_kept, log): a kept vector's removal gave a status other than
    UNSAT (SAT proves it is needed; UNKNOWN or SKIPPED does not)."""
    cur = deletion_order(masks)
    log = [[None, oracle(cur)]]
    if log[0][1] != "UNSAT":
        return None, {}, log
    why, i = {}, 0
    while i < len(cur):
        trial = cur[:i] + cur[i + 1:]
        st = oracle(trial)
        log.append([cur[i], st])
        if st == "UNSAT":
            cur = trial
        else:
            why[cur[i]] = st
            i += 1
    return cur, why, log


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def append_row(out_dir, name, row):
    rows = m100.load(out_dir, name) or []
    rows.append(row)
    save(out_dir, name, rows)


# ---------- the parts ----------

def run_check(shard, out_dir):
    g, info = {}, {}
    if shard == "a":
        cases = [case_of(x) for x in UNKNOWN_D2]
        g["unknown_28"] = len(set(UNKNOWN_D2)) == 28 and all(
            m102.inst_name(s, c) == x for (s, c), x in zip(cases, UNKNOWN_D2))
        g["all_d2"] = all(s["dmeet"] == 2 for s, _ in cases)
        g["all_le4"] = all(m105.le4(c) for _, c in cases)
        g["in_m105_sweep"] = set(UNKNOWN_D2) <= {m102.inst_name(s, c) for s, c in m105.sweep_cases()}
        by_type = {}
        for _, c in cases:
            key = " ".join(map(str, m104.k_and_type(m103.space_of(c))))
            by_type[key] = by_type.get(key, 0) + 1
        info["by_type"] = by_type
    elif shard == "b":
        cases = transfer_cases()
        by_class = {}
        for s, _ in cases:
            by_class[s["name"]] = by_class.get(s["name"], 0) + 1
        g["transfer_73"] = by_class == TRANSFER_LE4 and len(cases) == 73
        g["dmeet"] = [m100.spec_of(pi, ci)["dmeet"] for pi, ci in TRANSFER] == [1, 0, 0]
        ctrl = transfer_controls()
        g["controls"] = [m102.inst_name(s, c) for s, c in ctrl] == [
            "r3b_t8_B7_o000_c000_t2_m511", "r3b_t8_B7_o011_c000_t3_m001_016"]
        info["by_class"] = by_class
    else:
        items = min_items()
        g["items_10"] = len(items) == 10
        g["core_le4"] = all(m104.k_and_type(m103.space_of(c))[0] <= 4
                                    for _, c, p in items if p == "core")
        g["k6"] = all(m104.k_and_type(m103.space_of(c))[0] == 6 for _, c, p in items if p == "k6")
        g["n_15"] = sorted(n_masks()) == list(range(1, 16))
        g["out_7"] = all(sorted(out_masks(s)) == sorted(
            a | b | c for a in (0, 256) for b in (0, 512) for c in (0, 1024))[1:]
            for s, _, _ in items)
        info["items"] = [m102.inst_name(s, c) for s, c, _ in items]
    info["graded"] = g
    save(out_dir, f"m106{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({k: v for k, v in info.items() if k != 'graded'}, sort_keys=True)}",
          flush=True)


def run_a(cap, minutes, out_dir):
    start = time.time()
    tab, skipped = {}, []
    plan = [("n", n_masks(), 90.0), ("none", [], 30.0), ("sweep", None, cap)]
    for level, masks, budget in plan:
        for x in UNKNOWN_D2:
            if time.time() - start > minutes * 60:
                skipped.append(f"{x}_{level}")
                continue
            spec, case = case_of(x)
            if level == "sweep":
                row = m102.solve_one(spec, case, "sweep", budget, out_dir, "sweep")
                row["tag"] = f"{x}_sweep"
            else:
                row = solve_masks(spec, case, masks, f"{x}_{level}", level, budget, out_dir)
            append_row(out_dir, "m106a_rows.json", row)
            tally(tab, level, row["status"])
    save(out_dir, "m106a_skipped.json", skipped)
    print(f"SUMMARY run a skipped {len(skipped)} {json.dumps(tab, sort_keys=True)}", flush=True)


def run_b(cap, minutes, out_dir):
    start = time.time()
    tab, skipped = {}, []
    work = ([(s, c, "control") for s, c in transfer_controls()]
            + [(s, c, "n") for s, c in transfer_cases()])
    for spec, case, part in work:
        x = m102.inst_name(spec, case)
        if time.time() - start > minutes * 60:
            skipped.append(x)
            continue
        row = solve_masks(spec, case, n_masks(), f"{x}_n", part, cap, out_dir)
        append_row(out_dir, "m106b_rows.json", row)
        tally(tab, f"{part} {spec['name'][10:]}", row["status"])
    save(out_dir, "m106b_skipped.json", skipped)
    print(f"SUMMARY run b skipped {len(skipped)} {json.dumps(tab, sort_keys=True)}", flush=True)


def run_e(cap, minutes, out_dir):
    start = time.time()
    spec, case = transfer_controls()[0]
    x = m102.inst_name(spec, case)
    for level, masks in (("none", []), ("n", n_masks())):
        append_row(out_dir, "m106e_rows.json",
                   solve_masks(spec, case, masks, f"{x}_{level}", "control", cap, out_dir))
    mins = []
    for spec, case, part in min_items():
        x = m102.inst_name(spec, case)
        step = [0]

        def oracle(masks, where):
            if time.time() - start > minutes * 60:
                return "SKIPPED"
            step[0] += 1
            row = solve_masks(spec, case, masks, f"{x}_{where}{step[0]:02d}", f"{part} {where}",
                              cap, out_dir)
            append_row(out_dir, "m106e_rows.json", row)
            return row["status"]

        none = oracle([], "none")
        entry = {"instance": x, "part": part, "type": m104.k_and_type(m103.space_of(case))[1],
                 "none": none}
        for where, masks in (("N", n_masks()), ("out", out_masks(spec))):
            if none == "UNSAT":
                entry[where] = {"kept": [], "why": {}, "log": []}
                continue
            kept, why, log = minimize(masks, lambda m, w=where: oracle(m, w))
            entry[where] = {"kept": None if kept is None else [vec_name(h) for h in kept],
                            "why": {vec_name(h): st for h, st in why.items()},
                            "log": [[None if h is None else vec_name(h), st] for h, st in log]}
        mins.append(entry)
        save(out_dir, "m106e_min.json", mins)
        print(f"min {x}: {json.dumps(entry, sort_keys=True)}", flush=True)
    short = {e["instance"][10:]: [e["none"], (e["N"]["kept"]), e["out"]["kept"]] for e in mins}
    print(f"SUMMARY run e {json.dumps(short, sort_keys=True)}", flush=True)


def proven(entry):
    """A kept set is proven minimal when the removal of each kept vector gave SAT."""
    return entry["kept"] is not None and all(v == "SAT" for v in entry["why"].values())


def grade(shard, out_dir):
    g, out = {}, {}
    chk = m100.load(out_dir, f"m106{shard}_check.json")
    if chk is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    rows = m100.load(out_dir, f"m106{shard}_rows.json") or []
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g[f"verified_{r['tag']}"] = bool(r.get("verified"))
    # a model anisotropic on all of V would be a system with t = 8, dim V = 11: flag it
    out["full_models"] = sorted(r["tag"] for r in rows if r["status"] == "SAT"
                                and r["check"].get("anisotropic"))
    if shard == "a":
        st = {}
        for r in rows:
            st.setdefault(r["instance"], {})[r["tag"][len(r["instance"]) + 1:]] = r["status"]
        g["rows_ran"] = len(rows) + len(m100.load(out_dir, "m106a_skipped.json") or []) == 84
        # the n CNF is implied by the sweep CNF: sweep SAT with n UNSAT would be a contradiction
        g["consistent"] = not any(v.get("sweep") == "SAT" and v.get("n") == "UNSAT"
                                  for v in st.values())
        out["by_level"] = {}
        for r in rows:
            tally(out["by_level"], r["tag"][len(r["instance"]) + 1:], r["status"])
        out["decided"] = sorted(x for x, v in st.items() if "UNSAT" in v.values())
        out["undecided"] = sorted(x for x, v in st.items() if "UNSAT" not in v.values())
        out["cases"] = st
    elif shard == "b":
        ctrl = [r for r in rows if r["part"] == "control"]
        g["controls_sat"] = len(ctrl) == 2 and all(r["status"] == "SAT" and r.get("verified")
                                                   for r in ctrl)
        g["rows_ran"] = len(rows) + len(m100.load(out_dir, "m106b_skipped.json") or []) == 75
        out["by_class"] = {}
        for r in rows:
            if r["part"] == "n":
                tally(out["by_class"], f"{r['name'][10:]} {r['type']}", r["status"])
        out["cases"] = {r["instance"]: r["status"] for r in rows if r["part"] == "n"}
    else:
        ctrl = [r for r in rows if r["part"] == "control"]
        g["control_n_sat"] = any(r["status"] == "SAT" and r.get("verified")
                                 and len(r["masks"]) == 15 for r in ctrl)
        mins = m100.load(out_dir, "m106e_min.json") or []
        g["min_ran"] = len(mins) == 10
        out["control"] = [[r["tag"], r["status"]] for r in ctrl]
        out["min"] = {e["instance"][10:]: {"none": e["none"], "N": e["N"]["kept"],
                                            "out": e["out"]["kept"],
                                            "N_proven": proven(e["N"]), "out_proven": proven(e["out"])}
                      for e in mins}
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "run", "grade", "child"], default="check")
    ap.add_argument("--shard", choices=["a", "b", "e"], default="a")
    ap.add_argument("--cap-seconds", type=float, default=60.0)
    ap.add_argument("--minutes", type=float, default=120.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--case")
    ap.add_argument("--masks")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), json.loads(args.case), json.loads(args.masks), args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "run":
        {"a": run_a, "b": run_b, "e": run_e}[args.shard](args.cap_seconds, args.minutes,
                                                          args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m106{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "cases")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
