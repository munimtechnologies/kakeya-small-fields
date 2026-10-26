# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m111: where the d = 1 cases left open by job m110 sit, and which anisotropy decides them
(notes/a103.md, cube_groups/m111-predictions.md).

What came back on 2026-10-26 (jobs m110a-g, notes/a103.md): of the 2,715 cases with k(T(N)) <= 4 in
shards a to g of the 34 d = 1 classes, 2,389 were UNSAT with anisotropy kept only on the 15 vectors
of N ("n", 60 s) and 11 more with the full sweep CNF (120 s); 315 stayed open (31 SAT at "n", none
SAT at the sweep). Every graded check held. Shards h and i were stopped from outside at 08:22 UTC
and re-filed; shard j had not come back. Read off the instance names, 313 of the 315 open cases have
basis matrices with index < 64 (row 2 of each, in m102's bit order, is 0 or (0, 0, 1)): T(N) then
leaves span(q_0, q_1) invariant, and in all four d = 1 pair orbits span(q_0, q_1) is
pi(R) = (R + X_1) / X_1, R = Im A_u. Part "struct" tests that reading by machine.

S : Q -> Q is the map A_u induces on Q = X / X_1 (S pi = pi A_u). Its image is pi(R), of dimension
3 - d, and its kernel A_u-bar^(-1)(X_1 n R) has dimension d.

Parts:

    struct    shard a: pi(R), ker S and Im S for all 68 classes against m99's d and Im A_u; for each
              of the 3,876 d = 1 cases whether T(N) leaves pi(R) invariant, leaves ker S invariant,
              commutes with S, and the row-2 index rule; cross-tables against m110a-g's answers;
              the same predicate on the d = 2 cases of m105 and the 28 that m105 left UNKNOWN
    check     shards b, c: this shard's half of the pilot sample (one open case of m110a-g per
              label, the first by name), the vector sets, the control
    run       shards b, c: the control (o000_c000 t2_m511) at "n", "in4" and "out3"; then each case
              of the sample at "in4" (N + span(h_1..h_4), 255 vectors, 120 s) and "out3"
              (N + span(h_5, h_6, h_7), 127 vectors, 120 s), and m102's sweep CNF (600 s) when
              neither was UNSAT
    grade     the graded checks of m111-predictions.md

Every CNF here keeps all conditions of its case and asks sigma(h) != 0 on a subset of V, so it is
implied by the full CNF: UNSAT at any level means the case is impossible.

Usage: python m111.py --part struct|check|run|grade --shard a|b|c [--minutes M] [--out-dir D]
       (the grade files m110{a..g}_grade.json must be in the working directory)
"""
import argparse
import json
import os
import time

import m100
import m102
import m103
import m104
import m105
import m106
import m110
import sat_aniso as sa

T, D, KD = m102.T, m102.D, m102.KD
NX1, Q = m102.NX1, m102.Q
M110_DONE = "abcdefg"          # the m110 shards that finished (2026-10-26)
CONTROL = "r3b_t8_B7_o000_c000_t2_m511"
LEVELS = (("in4", 120.0), ("out3", 120.0))
N_CAP = 60.0
SWEEP_CAP = 600.0
RUN_SHARDS = "bc"
FEATURES = ("pres_r", "pres_ker", "comm_s", "row2")


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


def append_row(out_dir, name, row):
    rows = m100.load(out_dir, name) or []
    rows.append(row)
    save(out_dir, name, rows)


# ---------- S, pi(R) and the predicates ----------

def all_specs():
    return [s for sh in sorted(m100.SHARDS) for s in m100.shard_specs(sh)]


def pi_r(spec):
    """pi(R) as a set of vectors of Q (bit i is the coordinate of pi(e_(5 + i)))."""
    return frozenset(m100.span([r >> NX1 for r in spec["r"]]))


def s_map(spec):
    """S as a 3 x 3 matrix: column c is pi(A_u e_(5 + c))."""
    return sa.from_cols([sa.mat_apply(spec["au"], 1 << (NX1 + c), T) >> NX1 for c in range(Q)], Q)


def ker_s(spec):
    s = s_map(spec)
    return frozenset(q for q in range(1 << Q) if sa.mat_apply(s, q, Q) == 0)


def im_s(spec):
    s = s_map(spec)
    return frozenset(sa.mat_apply(s, q, Q) for q in range(1 << Q))


def preserves(space, w):
    return all(sa.mat_apply(m, x, Q) in w for m in space for x in w)


def commutes(space, s):
    return all(m102.mm3(m, s) == m102.mm3(s, m) for m in space)


def row2_rule(case):
    """The reading of the names: every basis matrix has entries (2, 0) and (2, 1) zero."""
    return all((m >> (2 * Q)) & 3 == 0 for m in case["maps"])


def features(spec, case):
    sp = m103.space_of(case)
    return {"pres_r": preserves(sp, pi_r(spec)), "pres_ker": preserves(sp, ker_s(spec)),
            "comm_s": commutes(sp, s_map(spec)), "row2": row2_rule(case)}


# ---------- m110's answers ----------

def m110_parts(shards=M110_DONE, src="."):
    """{instance: {part: status}} from the grade files of m110's finished shards, or None if one
    is missing."""
    out = {}
    for s in shards:
        g = m100.load(src, f"m110{s}_grade.json")
        if g is None:
            return None
        out.update(g["cases"])
    return out


def finals(parts):
    return {x: m110.final_status(v) for x, v in parts.items()}


def sample(open_names):
    """One open case per label (kind and maps), the first by name, in label order."""
    first = {}
    for x in sorted(open_names):
        first.setdefault(x[20:], x)
    return [first[k] for k in sorted(first)]


def shard_sample(shard, open_names):
    return sample(open_names)[RUN_SHARDS.index(shard)::len(RUN_SHARDS)]


def control_case():
    """(spec, case) of o000_c000 t2 with M = J (SAT at "n" in jobs m106b and m110a-g). Not an orbit
    representative's label, so it is built directly, as m106.transfer_controls does."""
    return m106.transfer_controls()[0]


def level_masks(spec, level):
    out_idx, in_idx = m104.h_split(spec)
    extra = {"n": [], "in4": in_idx, "out3": out_idx}[level]
    return m104.w_masks(list(range(KD)) + list(extra))


# ---------- the parts ----------

def run_struct(out_dir):
    g, info = {}, {}
    specs = all_specs()
    g["specs_68"] = len(specs) == 68
    g["dims_68"] = all(len(pi_r(s)) == 2 ** (Q - s["dmeet"]) and len(ker_s(s)) == 2 ** s["dmeet"]
                       for s in specs)
    g["im_s_is_pi_r"] = all(im_s(s) == pi_r(s) for s in specs)
    g["d1_pi_r_q01"] = all(pi_r(s) == frozenset({0, 1, 2, 3}) for s in m110.d1_specs())
    cases = m110.sweep_cases()
    feats = {m102.inst_name(s, c): dict(features(s, c), type=m104.k_and_type(m103.space_of(c))[1],
                                        kind=c["kind"])
             for s, c in cases}
    g["cases_3876"] = len(feats) == m110.TOTAL
    g["row2_is_pres_r"] = all(f["row2"] == f["pres_r"] for f in feats.values())
    parts = m110_parts()
    g["grades_loaded"] = parts is not None and len(parts) == sum(m110.SIZE[s] for s in M110_DONE)
    parts = parts or {}
    g["names_known"] = set(parts) <= set(feats)
    fin = finals(parts)
    cross = {k: {} for k in FEATURES}
    by_class, by_type = {}, {}
    for x, f in fin.items():
        for k in FEATURES:
            tally(cross[k], str(feats[x][k]), f)
        tally(by_class, x[10:19], f)
        tally(by_type, f"{feats[x]['type']} pres_r={feats[x]['pres_r']}", f)
    info["cross"] = cross
    info["by_class"] = by_class
    info["by_type"] = by_type
    info["open_not_pres_r"] = sorted(x for x, f in fin.items() if f != "UNSAT"
                                     and not feats[x]["pres_r"])
    info["unsat_pres_r"] = {x: parts[x] for x, f in sorted(fin.items())
                            if f == "UNSAT" and feats[x]["pres_r"]}
    info["pres_r_total"] = sum(f["pres_r"] for f in feats.values())
    info["pres_r_by_type"] = {}
    for f in feats.values():
        tally(info["pres_r_by_type"], f"{f['kind']} {f['type']}", str(f["pres_r"]))
    rest = [x for x in feats if x not in fin]
    info["not_yet_run"] = {"cases": len(rest), "pres_r": sum(feats[x]["pres_r"] for x in rest)}
    # d = 2: the 1,078 cases of m105 and the 28 it left UNKNOWN
    d2 = [(s, c) for s, c in m105.sweep_cases()]
    unk = [m106.case_of(x) for x in m106.UNKNOWN_D2]
    info["d2"] = {"cases": len(d2), "pres_r": sum(features(s, c)["pres_r"] for s, c in d2),
                  "unknown_28_pres_r": sum(features(s, c)["pres_r"] for s, c in unk),
                  "unknown_28_not": sorted(x for x, (s, c) in zip(m106.UNKNOWN_D2, unk)
                                           if not features(s, c)["pres_r"])}
    g["d2_1078"] = len(d2) == 1078 and len(unk) == 28
    info["graded"] = g
    save(out_dir, "m111a_struct.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    short = {k: info[k] for k in ("cross", "open_not_pres_r", "pres_r_total", "not_yet_run", "d2")}
    print(f"SUMMARY struct all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps(short, sort_keys=True)}", flush=True)


def run_check(shard, out_dir):
    g, info = {}, {}
    parts = m110_parts()
    g["grades_loaded"] = parts is not None
    fin = finals(parts or {})
    open_names = sorted(x for x, f in fin.items() if f != "UNSAT")
    mine = shard_sample(shard, open_names)
    labels = [x[20:] for x in sample(open_names)]
    g["sample_one_per_label"] = len(labels) == len(set(labels)) == len({x[20:] for x in open_names})
    g["sample_nonempty"] = len(mine) > 0
    known = {m102.inst_name(s, c) for s, c in m110.sweep_cases()}
    g["sample_d1_open"] = all(x in known and fin[x] != "UNSAT" for x in mine)
    cspec, ccase = control_case()
    g["control_name"] = m102.inst_name(cspec, ccase) == CONTROL
    sizes = {CONTROL: [len(level_masks(cspec, lv)) for lv in ("n", "in4", "out3")]}
    for x in mine:
        spec, _ = m106.case_of(x)
        sizes[x] = [len(level_masks(spec, lv)) for lv in ("n", "in4", "out3")]
    g["mask_sizes"] = all(v == [15, 255, 127] for v in sizes.values())
    info.update({"sample": mine, "labels": labels, "open": len(open_names), "graded": g})
    save(out_dir, f"m111{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'sample': mine, 'labels': len(labels), 'open': len(open_names)})}",
          flush=True)


def run(shard, minutes, out_dir):
    start = time.time()
    name = f"m111{shard}_rows.json"
    info = m100.load(out_dir, f"m111{shard}_check.json") or {"sample": []}
    tab, skipped = {}, []
    spec, case = control_case()
    for level, cap in (("n", N_CAP),) + LEVELS:
        row = m106.solve_masks(spec, case, level_masks(spec, level), f"{CONTROL}_{level}",
                               "control " + level, cap, out_dir)
        m110.drop_child(out_dir, row)
        append_row(out_dir, name, row)
        tally(tab, "control " + level, row["status"])
    for x in info["sample"]:
        spec, case = m106.case_of(x)
        got = []
        for level, cap in LEVELS:
            if time.time() - start > minutes * 60:
                skipped.append(f"{x}_{level}")
                continue
            row = m106.solve_masks(spec, case, level_masks(spec, level), f"{x}_{level}", level,
                                   cap, out_dir)
            m110.drop_child(out_dir, row)
            append_row(out_dir, name, row)
            tally(tab, level, row["status"])
            got.append(row["status"])
        if "UNSAT" in got:
            continue
        if time.time() - start > minutes * 60:
            skipped.append(f"{x}_sweep")
            continue
        row = m102.solve_one(spec, case, "sweep", SWEEP_CAP, out_dir, "sweep")
        row["tag"] = f"{x}_sweep"
        row["inv"], row["type"] = m104.k_and_type(m103.space_of(case))
        m110.drop_child(out_dir, row)
        append_row(out_dir, name, row)
        tally(tab, "sweep", row["status"])
    save(out_dir, f"m111{shard}_skipped.json", skipped)
    print(f"SUMMARY run {shard} skipped {len(skipped)} {json.dumps(tab, sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade_rows(rows, skipped, smp):
    """(graded, out) for a run shard from its rows, skipped tags and sample."""
    g, out = {}, {}
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g[f"verified_{r['tag']}"] = bool(r.get("verified"))
    ctrl = {r["part"]: r["status"] for r in rows if r["part"].startswith("control")}
    g["control_n_sat"] = ctrl.get("control n") == "SAT"
    st = {}
    for r in rows:
        if not r["part"].startswith("control"):
            st.setdefault(r["instance"], {})[r["part"]] = r["status"]
    for t in skipped:
        x, level = t.rsplit("_", 1)
        st.setdefault(x, {})[level] = "SKIPPED"
    g["levels_ran"] = all(set(st.get(x, {})) >= {lv for lv, _ in LEVELS} for x in smp)
    # the sweep ran (or was skipped) exactly when neither level was UNSAT
    g["sweep_rule"] = all(("sweep" in st.get(x, {})) == ("UNSAT" not in [st.get(x, {}).get(lv)
                                                                         for lv, _ in LEVELS])
                          for x in smp)
    # every CNF here is implied by the sweep CNF
    g["consistent"] = not any(v.get("sweep") == "SAT" and "UNSAT" in v.values()
                              for v in st.values())
    out["full_models"] = sorted(r["tag"] for r in rows if r["status"] == "SAT"
                                and r["check"].get("anisotropic"))
    out["control"] = ctrl
    out["by_level"] = {}
    for r in rows:
        if not r["part"].startswith("control"):
            tally(out["by_level"], r["part"], r["status"])
    out["decided"] = sorted(x for x, v in st.items() if "UNSAT" in v.values())
    out["open"] = sorted(x for x, v in st.items() if "UNSAT" not in v.values())
    out["cases"] = st
    return g, out


def grade(shard, out_dir):
    if shard == "a":
        st = m100.load(out_dir, "m111a_struct.json")
        g = {"struct_ran": st is not None}
        if st is not None:
            g.update({"struct_" + k: v for k, v in st["graded"].items()})
        return {"graded": g}
    chk = m100.load(out_dir, f"m111{shard}_check.json")
    rows = m100.load(out_dir, f"m111{shard}_rows.json") or []
    skipped = m100.load(out_dir, f"m111{shard}_skipped.json")
    g, out = grade_rows(rows, skipped or [], chk["sample"] if chk else [])
    g["check_ran"] = chk is not None
    if chk is not None:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    g["run_ran"] = skipped is not None
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["struct", "check", "run", "grade"], default="check")
    ap.add_argument("--shard", choices=["a", "b", "c"], default="a")
    ap.add_argument("--minutes", type=float, default=200.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "struct":
        run_struct(args.out_dir)
    elif args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "run":
        run(args.shard, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m111{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "cases")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
