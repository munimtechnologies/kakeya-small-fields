# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m107: which hand conditions the refutations in the rank-0 case of (B7)_8 (t = 8, dim V = 11)
need once no anisotropy clause is left, whether no anisotropy at all decides the cases with
k(T(N)) > 4 of the three d = 3 classes, and the four d = 2 cases still open (notes/a99.md,
cube_groups/m107-predictions.md).

What came back on 2026-10-25 (jobs m106a, m106b and m106e, notes/a99.md): every graded check held.
In job m106e the six core cases and the four k = 6 cases were all UNSAT with no anisotropy clause
at all ("none", 6 to 56 s), while the positive control was SAT. So the hand conditions of each case,
with the system (*) and the normal form, are already contradictory there. Of the 28 d = 2 cases
left open by m105, 24 were decided (22 with anisotropy on N); four t2 cases remain.

The hand conditions, in twelve groups. Every CNF keeps the system (*) and m42's normal form
(A_u, sigma(u) = x0 = e_0, beta(u, h_j) = phi(h_j)); i runs over 1, 2, 3 (v_1, v_2, v_3 span N with u):

    H1  A_(v_i) x0 = 0                                      m42.add_hints ((3) of a10.md)
    H2  A_(v_i) maps P + span(x0) (here all of X) into R    m42.add_hints ((2) of a10.md)
    H3  sigma(v_i) in X_1                                   m42.add_hints ((3) of a10.md)
    H4  beta(v_i, v_j) in X_1                               m42.add_hints ((2) of a10.md)
    S1  A_(v_i) X_1 = 0                                     m100.add_sweep (Lemma 103)
    S2  beta(v_i, v_j) = 0                                  m100.add_sweep (Lemma 103)
    Z   A_(v_1) = 0                                         m101 (Corollary 123)
    X   beta(v_1, e_j) in X_1 for j != 1                    m101 (Lemma 105 (a))
    C   x0 not in beta(v_1, V) + span(sigma(v_1))           m101 (Lemma 105 (d), (e))
    M   A_(v_2), A_(v_3) = A_u-bar T pi, T the case's maps  m102 (Lemma 106)
    XE  X for the other w in N_0 (t1 and t2 only)           m102
    CE  C for the other w in N_0 (t1 and t2 only)           m102

With all twelve the CNF is m102's "relax" CNF clause for clause (part check compares hashes). Leaving
groups out only removes conditions, so UNSAT without a group still means UNSAT for the case.

Parts:

    check    shard a: the four open d = 2 cases rebuilt; shards b, c: the 88 cases with k > 4 of
             the d = 3 classes and this shard's half; shards e, f: the groups against m102's relax
             CNF (hash) and the hand counts of each group
    run      shard a: the four at anisotropy on N ("n"), capped
             shards b, c: the positive control at "none", then each case at "none" and, if that is
             not UNSAT, at "n"
             shards e (six core cases), f (four k = 6 cases): the control with all groups, then for
             each case a deletion-minimal set of groups with the CNF still UNSAT (DROP_ORDER)
    grade    the graded checks of m107-predictions.md

Usage: python m107.py --part check|run|grade --shard a|b|c|e|f [--cap-seconds S] [--minutes M]
       [--out-dir D]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import m42
import m100
import m101
import m102
import m103
import m104
import m106
import sat_aniso as sa

T, D, KD = m102.T, m102.D, m102.KD
X0, X1_MASK = m101.X0, m101.X1_MASK
GROUPS = ("H1", "H2", "H3", "H4", "S1", "S2", "Z", "X", "C", "M", "XE", "CE")
# part e and f try to drop the groups in this order: first those m101 and m102 call implied or
# added for the solver, then Lemma 105's, then Lemma 103's, then the hints, then the case itself
DROP_ORDER = ("X", "XE", "CE", "C", "S2", "S1", "H4", "H3", "H2", "H1", "Z", "M")
# by hand: A_u has rank 3, so dim X_1 = 5 and dim R = 3, and m42's P + span(x0) is all of X (8
# vectors); three v_i, three pairs (v_i, v_j)
COUNTS = {"H1": 3 * 8, "H2": 3 * 8 * 5, "H3": 3 * 3, "H4": 3 * 3, "S1": 3 * 5 * 8, "S2": 3 * 8,
          "Z": 64, "X": 30, "C": 11, "M": 128}
# XE and CE by kind (the counts of m102's check part)
EXTRA = {"t1": (60, 70), "t2": (30, 23), "t3": (0, 0)}
# job m106a (compete-results/m106a-b7-undecided-v1): UNKNOWN at "n" (90 s), "none" (30 s) and with
# full anisotropy (120 s)
OPEN_D2 = ("r3b_t8_B7_o003_c002_t2_m163", "r3b_t8_B7_o005_c002_t2_m163",
           "r3b_t8_B7_o005_c003_t2_m034", "r3b_t8_B7_o005_c003_t2_m038")
# job m104a (m104_count.json): the cases with k > 4 of the three d = 3 classes, by class and by k
HIGH_BY_CLASS = {"r3b_t8_B7_o000_c000": 58, "r3b_t8_B7_o001_c000": 7, "r3b_t8_B7_o002_c000": 23}
HIGH_BY_K = {6: 56, 8: 21, 10: 11}
HIGH_SHARDS = "bc"


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def append_row(out_dir, name, row):
    rows = m100.load(out_dir, name) or []
    rows.append(row)
    save(out_dir, name, rows)


# ---------- the cases ----------

def kt(case):
    return m104.k_and_type(m103.space_of(case))


def high_cases():
    """[(spec, case)]: the t2 and t3 cases with k > 4 of the three d = 3 classes, in m102's order."""
    out = []
    for pi, ci in m104.D3:
        spec = m100.spec_of(pi, ci)
        out += [(spec, c) for c in m102.class_cases(spec)[1:] if kt(c)[0] > 4]
    return out


def high_shard(shard):
    return [x for i, x in enumerate(high_cases()) if HIGH_SHARDS[i % len(HIGH_SHARDS)] == shard]


def group_items(shard):
    """[(spec, case, part)]: shard e the six core cases, shard f the four k = 6 cases (m106)."""
    items = m106.min_items()
    return [x for x in items if x[2] == ("core" if shard == "e" else "k6")]


# ---------- the CNF with a set of groups ----------

def add_hint_parts(cnf, names, t, kd, au, s0, pvecs, groups):
    """m42.add_hints, one group at a time, in m42's order. Returns {group: conditions added}."""
    A, S, B = names[0], names[1], names[2]
    ann_x1 = m42.ann(m42.kernel(au, t), t)
    ann_r = m42.ann(m42.column_space(au, t), t)
    ext = m42.rref(list(pvecs) + [s0])
    n = {"H1": 0, "H2": 0, "H3": 0, "H4": 0}
    for i in range(1, kd):
        if "H1" in groups:
            for row in range(t):
                cnf.xor_eq([A[i][row][c] for c in range(t) if (s0 >> c) & 1], 0)
                n["H1"] += 1
        if "H2" in groups:
            for y in ext:
                for f in ann_r:
                    cnf.xor_eq([A[i][row][c] for row in range(t) if (f >> row) & 1
                                for c in range(t) if (y >> c) & 1], 0)
                    n["H2"] += 1
        if "H3" in groups:
            for f in ann_x1:
                cnf.xor_eq([S[i][row] for row in range(t) if (f >> row) & 1], 0)
                n["H3"] += 1
    if "H4" in groups:
        for i, j in itertools.combinations(range(1, kd), 2):
            for f in ann_x1:
                cnf.xor_eq([B[(i, j)][row] for row in range(t) if (f >> row) & 1], 0)
                n["H4"] += 1
    return {k: v for k, v in n.items() if k in groups}


def add_sweep_parts(cnf, names, t, kd, au, groups):
    """m100.add_sweep, one group at a time, in m100's order."""
    A, B = names[0], names[2]
    n = {}
    if "S1" in groups:
        n["S1"] = 0
        for i in range(1, kd):
            for y in m100.kernel_basis(au, t):
                for row in range(t):
                    cnf.xor_eq([A[i][row][c] for c in range(t) if (y >> c) & 1], 0)
                    n["S1"] += 1
    if "S2" in groups:
        n["S2"] = 0
        for i, j in itertools.combinations(range(1, kd), 2):
            for row in range(t):
                cnf.clauses.append([-B[(i, j)][row]])
                n["S2"] += 1
    return n


def build_groups(spec, case, groups):
    """(cnf, names, counts): the system (*), the normal form and the given groups, built in the
    order of m102.build(spec, case, "relax")."""
    groups = set(groups)
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    cnf, names = m100.encode_fixed(t, d, au, s0, phis, aniso=False)
    counts = add_hint_parts(cnf, names, t, kd, au, s0, pvecs, groups)
    counts.update(add_sweep_parts(cnf, names, t, kd, au, groups))
    two = m101.case_two_required(spec)
    if "Z" in groups:
        counts["Z"] = m101.add_zero_map(cnf, names, t)
    if "X" in groups:
        counts["X"] = m101.add_in_x1(cnf, names, t, d)
    if "C" in groups and two:
        counts["C"] = m101.add_case_two(cnf, names, t, d)[1]
    if "M" in groups:
        counts["M"] = sum(m102.add_fixed_map(cnf, names, i, m102.a_of_t(au, tm))
                          for i, tm in zip((2, 3), case["maps"]))
    if "XE" in groups:
        counts["XE"] = sum(m102.add_in_x1_at(cnf, names, i, T, D) for i in m102.extra_in_x1(case))
    if "CE" in groups and two:
        counts["CE"] = sum(m102.add_case_two_w(cnf, names, T, D, w)
                           for w in m102.n0_ws(case) if w != (1,))
    return cnf, names, counts


def group_checks(spec, case, res):
    """Each group read back from a model outside the encoder, as the property it states."""
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    As, ss = res["A"], res["s"]
    B = {(i, k): v for i, k, v in res["B"]}
    ns = range(1, kd)
    image = m100.image(au, t)
    ker = m100.kernel_basis(au, t)
    ext = m42.rref(list(pvecs) + [s0])
    extra = m102.extra_checks(spec, case, res)
    two = m101.case_two_required(spec)
    gens = [ss[1]] + [B[m101.bkey(1, j)] for j in range(d) if j != 1]
    return {"H1": all(sa.mat_apply(As[i], s0, t) == 0 for i in ns),
            "H2": all(sa.mat_apply(As[i], y, t) in image for i in ns for y in ext),
            "H3": all(sa.mat_apply(au, ss[i], t) == 0 for i in ns),
            "H4": all(sa.mat_apply(au, B[(i, j)], t) == 0
                      for i, j in itertools.combinations(ns, 2)),
            "S1": all(sa.mat_apply(As[i], y, t) == 0 for i in ns for y in ker),
            "S2": all(B[(i, j)] == 0 for i, j in itertools.combinations(ns, 2)),
            "Z": As[1] == 0,
            "X": all(B[m101.bkey(1, j)] & ~X1_MASK == 0 for j in range(d) if j != 1),
            "C": not two or X0 not in m100.span(gens),
            "M": extra["t_maps"],
            "XE": extra["in_x1_extra"],
            "CE": not two or extra["case_two_extra"]}


def child(spec, case, groups, path):
    from pysat.solvers import Solver
    cnf, names, counts = build_groups(spec, case, groups)
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
           "clauses": len(cnf.clauses), "counts": counts, "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, T, D)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_groups(spec, case, groups, tag, part, cap, out_dir):
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--case", json.dumps(case), "--groups", json.dumps(list(groups)), "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=cap, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    inv, typ = kt(case)
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({"instance": m102.inst_name(spec, case), "name": spec["name"], "tag": tag,
                "part": part, "groups": [g for g in GROUPS if g in groups], "kind": case["kind"],
                "maps": case["maps"], "dmeet": spec["dmeet"], "inv": inv, "type": typ,
                "wall_seconds": round(time.time() - start, 2), "budget_seconds": cap})
    if res["status"] == "SAT":
        chk = m100.check_model(spec, res)
        chk.update(group_checks(spec, case, res))
        row["check"] = {k: chk[k] for k in ("system", "normal_form", "anisotropic") + GROUPS}
        row["verified"] = chk["system"] and chk["normal_form"] and all(chk[g] for g in groups)
        row["violated"] = [g for g in GROUPS if not chk[g]]
    print(f"solve {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


def minimize_groups(oracle, order=DROP_ORDER):
    """A deletion-minimal set of groups for which oracle(list) is 'UNSAT', dropping them in the
    given order, or None if all of them together are not. Returns (kept in GROUPS order, why_kept,
    log): a kept group's removal gave a status other than UNSAT (SAT proves it is needed; UNKNOWN or
    SKIPPED does not)."""
    cur = list(order)
    log = [[None, oracle(cur)]]
    if log[0][1] != "UNSAT":
        return None, {}, log
    why = {}
    for g in order:
        trial = [x for x in cur if x != g]
        st = oracle(trial)
        log.append([g, st])
        if st == "UNSAT":
            cur = trial
        else:
            why[g] = st
    return [g for g in GROUPS if g in cur], why, log


# ---------- the parts ----------

def run_check(shard, out_dir):
    g, info = {}, {}
    if shard == "a":
        cases = [m106.case_of(x) for x in OPEN_D2]
        g["open_4"] = len(set(OPEN_D2)) == 4 and all(
            m102.inst_name(s, c) == x for (s, c), x in zip(cases, OPEN_D2))
        g["all_d2_t2"] = all(s["dmeet"] == 2 and c["kind"] == "t2" for s, c in cases)
        g["all_le4"] = all(kt(c)[0] <= 4 for _, c in cases)
        g["in_m106a"] = set(OPEN_D2) <= set(m106.UNKNOWN_D2)
        info["types"] = {x: list(kt(c)) for x, (_, c) in zip(OPEN_D2, cases)}
    elif shard in HIGH_SHARDS:
        cases = high_cases()
        names = [m102.inst_name(s, c) for s, c in cases]
        by_class, by_k = {}, {}
        for s, c in cases:
            by_class[s["name"]] = by_class.get(s["name"], 0) + 1
            by_k[kt(c)[0]] = by_k.get(kt(c)[0], 0) + 1
        g["high_88"] = len(cases) == 88 and len(set(names)) == 88
        g["by_class"] = by_class == HIGH_BY_CLASS
        g["by_k"] = by_k == HIGH_BY_K
        g["all_d3"] = all(s["dmeet"] == 3 for s, _ in cases)
        g["shard_44"] = len(high_shard(shard)) == 44
        types = {}
        for _, c in cases:
            key = " ".join(map(str, kt(c)))
            types[key] = types.get(key, 0) + 1
        info.update({"by_class": by_class, "by_k": {str(k): v for k, v in sorted(by_k.items())},
                     "types": types})
    else:
        items = group_items(shard)
        g["items"] = len(items) == (6 if shard == "e" else 4)
        picks = [items[0], items[-1]] if shard == "e" else [items[0]]
        same, right = True, True
        for spec, case, _ in picks:
            ref, _, _ = m102.build(spec, case, "relax")
            h_ref, n_ref, v_ref = m100.clause_hash(ref), len(ref.clauses), ref.nv
            del ref
            cnf, _, counts = build_groups(spec, case, GROUPS)
            same = same and (m100.clause_hash(cnf), len(cnf.clauses), cnf.nv) == (h_ref, n_ref, v_ref)
            want = dict(COUNTS, XE=EXTRA[case["kind"]][0], CE=EXTRA[case["kind"]][1])
            right = right and counts == want and m101.case_two_required(spec)
            info[m102.inst_name(spec, case)] = {"clauses": n_ref, "counts": counts}
            del cnf
        g["same_as_relax"] = same
        g["counts_by_hand"] = right
        info["items"] = [m102.inst_name(s, c) for s, c, _ in items]
    info["graded"] = g
    save(out_dir, f"m107{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({k: v for k, v in info.items() if k != 'graded'}, sort_keys=True)}",
          flush=True)


def run_a(cap, minutes, out_dir):
    start = time.time()
    tab, skipped = {}, []
    for x in OPEN_D2:
        if time.time() - start > minutes * 60:
            skipped.append(x)
            continue
        spec, case = m106.case_of(x)
        row = m106.solve_masks(spec, case, m106.n_masks(), f"{x}_n", "n", cap, out_dir)
        append_row(out_dir, "m107a_rows.json", row)
        tally(tab, "n", row["status"])
    save(out_dir, "m107a_skipped.json", skipped)
    print(f"SUMMARY run a skipped {len(skipped)} {json.dumps(tab, sort_keys=True)}", flush=True)


def run_high(shard, cap, minutes, out_dir):
    start = time.time()
    name = f"m107{shard}_rows.json"
    tab, skipped = {}, []
    spec, case = m106.transfer_controls()[0]
    x = m102.inst_name(spec, case)
    append_row(out_dir, name, m106.solve_masks(spec, case, [], f"{x}_none", "control", cap, out_dir))
    for spec, case in high_shard(shard):
        x = m102.inst_name(spec, case)
        if time.time() - start > minutes * 60:
            skipped.append(x)
            continue
        row = m106.solve_masks(spec, case, [], f"{x}_none", "none", cap, out_dir)
        append_row(out_dir, name, row)
        final = row["status"]
        if final != "UNSAT":
            row = m106.solve_masks(spec, case, m106.n_masks(), f"{x}_n", "n", cap, out_dir)
            append_row(out_dir, name, row)
            final = "UNSAT_n" if row["status"] == "UNSAT" else final + "/" + row["status"]
        tally(tab, f"k{row['inv']}", final)
    save(out_dir, f"m107{shard}_skipped.json", skipped)
    print(f"SUMMARY run {shard} skipped {len(skipped)} {json.dumps(tab, sort_keys=True)}",
          flush=True)


def run_groups(shard, cap, minutes, out_dir):
    start = time.time()
    name = f"m107{shard}_rows.json"
    spec, case = m106.transfer_controls()[0]
    x = m102.inst_name(spec, case)
    append_row(out_dir, name, solve_groups(spec, case, GROUPS, f"{x}_all", "control", cap, out_dir))
    mins = []
    for spec, case, part in group_items(shard):
        x = m102.inst_name(spec, case)
        step = [0]

        def oracle(groups):
            if time.time() - start > minutes * 60:
                return "SKIPPED"
            step[0] += 1
            row = solve_groups(spec, case, groups, f"{x}_g{step[0]:02d}", part, cap, out_dir)
            append_row(out_dir, name, row)
            return row["status"]

        kept, why, log = minimize_groups(oracle)
        entry = {"instance": x, "part": part, "type": kt(case)[1], "kept": kept, "why": why,
                 "log": log}
        mins.append(entry)
        save(out_dir, f"m107{shard}_min.json", mins)
        print(f"min {x}: {json.dumps(entry, sort_keys=True)}", flush=True)
    short = {e["instance"][10:]: e["kept"] for e in mins}
    print(f"SUMMARY run {shard} {json.dumps(short, sort_keys=True)}", flush=True)


def grade(shard, out_dir):
    g, out = {}, {}
    chk = m100.load(out_dir, f"m107{shard}_check.json")
    if chk is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    rows = m100.load(out_dir, f"m107{shard}_rows.json") or []
    skipped = m100.load(out_dir, f"m107{shard}_skipped.json") or []
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g[f"verified_{r['tag']}"] = bool(r.get("verified"))
    # a model anisotropic on all of V would be a system with t = 8, dim V = 11: flag it
    out["full_models"] = sorted(r["tag"] for r in rows if r["status"] == "SAT"
                                and r["check"].get("anisotropic"))
    if shard == "a":
        g["rows_ran"] = len(rows) + len(skipped) == 4
        out["cases"] = {r["instance"]: [r["status"], r["wall_seconds"]] for r in rows}
    elif shard in HIGH_SHARDS:
        ctrl = [r for r in rows if r["part"] == "control"]
        g["control_sat"] = len(ctrl) == 1 and ctrl[0]["status"] == "SAT" and bool(
            ctrl[0].get("verified"))
        none = [r for r in rows if r["part"] == "none"]
        g["rows_ran"] = len(none) + len(skipped) == 44
        final = {}
        for r in rows:
            if r["part"] in ("none", "n"):
                e = final.setdefault(r["instance"], {"inv": r["inv"], "type": r["type"]})
                e[r["part"]] = [r["status"], r["wall_seconds"]]
        out["by_k"] = {}
        for e in final.values():
            st = e["none"][0] + ("/" + e["n"][0] if "n" in e else "")
            tally(out["by_k"], f"k{e['inv']}", st)
        out["decided"] = sum(e["none"][0] == "UNSAT" or e.get("n", [""])[0] == "UNSAT"
                             for e in final.values())
        out["skipped"] = len(skipped)
        out["cases"] = final
    else:
        ctrl = [r for r in rows if r["part"] == "control"]
        g["control_sat"] = len(ctrl) == 1 and ctrl[0]["status"] == "SAT" and bool(
            ctrl[0].get("verified"))
        mins = m100.load(out_dir, f"m107{shard}_min.json") or []
        g["min_ran"] = len(mins) == (6 if shard == "e" else 4)
        # all twelve groups is m106e's "none" CNF, UNSAT for every one of these cases
        g["all_groups_unsat"] = bool(mins) and all(e["log"][0][1] == "UNSAT" for e in mins)
        out["min"] = {e["instance"][10:]: {"kept": e["kept"], "proven": m106.proven(e),
                                           "why": e["why"], "type": e["type"]} for e in mins}
        out["violated"] = {r["tag"]: r["violated"] for r in rows
                           if r["status"] == "SAT" and r["part"] != "control"}
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "run", "grade", "child"], default="check")
    ap.add_argument("--shard", choices=["a", "b", "c", "e", "f"], default="a")
    ap.add_argument("--cap-seconds", type=float, default=90.0)
    ap.add_argument("--minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--case")
    ap.add_argument("--groups")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), json.loads(args.case), json.loads(args.groups), args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "run":
        if args.shard == "a":
            run_a(args.cap_seconds, args.minutes, args.out_dir)
        elif args.shard in HIGH_SHARDS:
            run_high(args.shard, args.cap_seconds, args.minutes, args.out_dir)
        else:
            run_groups(args.shard, args.cap_seconds, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m107{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "cases")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
