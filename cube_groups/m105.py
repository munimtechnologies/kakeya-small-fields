# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m105: the cases with at most 4 invariant subspaces in the twelve other d = 2 classes of the
rank-0 case of (B7)_8 (t = 8, dim V = 11), and how little anisotropy the refutations of the d = 3
cases need (notes/a97.md, cube_groups/m105-predictions.md).

What came back on 2026-10-24 (jobs m104a, m104b and m104c, notes/a97.md): all 57 cases with
k(T(N)) <= 4 in the three d = 3 classes have DRAT proofs verified by drat-trim (Proposition 38).
Over all 68 classes there are 6,548 such cases, 1,115 of them in the 13 classes with d = 2, so
by m104's decision rule the d = 2 ones are run next (45 s each, four shards). In m104c's six core
cases, anisotropy kept only on W = N + span(h_5, h_6, h_7) (dim 7) was already contradictory, and
so was anisotropy only on N + span(h_1, ..., h_4) (dim 8). The level "out3_in1" failed with a
KeyError: m104.level_idx listed h_1 after h_5..h_7, and m101.add_aniso_on needs increasing
indices. Here every index list is sorted.

Parts:

    check    shards a-d: the 13 d = 2 classes against job m104a's count, the 1,078 cases of the 12
             classes not run before (o004_c000's 37 were all UNSAT in job m103b), this shard's
             share; shard e: the h split of the six core cases, the sizes of W at each level, the
             four k = 6 cases
    controls shards a-d: job m102's three positive controls of shard a (m102.control_list)
    sweep    shards a-d: this shard's cases with m102's sweep CNF, capped
    core     shard e: the positive control of m104c, then the six core cases of m104 with
             anisotropy only on smaller subspaces W of V (levels below), then four k = 6 cases of
             o000_c000 that were UNSAT under full anisotropy, at "out3" and "in4"
    grade    the graded checks of m105-predictions.md

Usage: python m105.py --part check|controls|sweep|core|grade --shard a|b|c|d|e
       [--cap-seconds S] [--minutes M] [--out-dir D]
"""
import argparse
import functools
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
import sat_aniso as sa

SHARDS = "abcd"
# job m104a (m104_count.json, 2026-10-24): the k <= 4 cases of the 13 classes with d = 2
D2_LE4 = {"r3b_t8_B7_o003_c000": 179, "r3b_t8_B7_o003_c001": 179, "r3b_t8_B7_o003_c002": 95,
          "r3b_t8_B7_o003_c003": 95, "r3b_t8_B7_o003_c004": 95, "r3b_t8_B7_o004_c000": 37,
          "r3b_t8_B7_o004_c001": 30, "r3b_t8_B7_o005_c000": 95, "r3b_t8_B7_o005_c001": 95,
          "r3b_t8_B7_o005_c002": 53, "r3b_t8_B7_o005_c003": 95, "r3b_t8_B7_o006_c000": 37,
          "r3b_t8_B7_o006_c001": 30}
# job m103b: all 37 k <= 4 cases of o004_c000 UNSAT at 60 s
DONE = {"r3b_t8_B7_o004_c000"}
SWEEP_TOTAL = 1078
LE4_TYPES = {"irr", "nil3", "x(x2+x+1)", "F8", "F2xF4", "F2[x]/x3"}
# levels of part core: the indices of V on which anisotropy is kept (N = indices 0..3; in the
# normal form h_5, h_6, h_7 = 8, 9, 10 have pi phi(h) != 0 and h_1..h_4 = 4..7 have phi(h) in X_1)
CORE_LEVELS = ("n", "out1_h5", "out1_h6", "out1_h7", "noN_out3", "out2_h56", "out2_h57", "out2_h67",
               "in1_h1", "in2_h12", "noN_in4")
K6_LEVELS = ("out3", "in4")
W_SIZES = {"n": 15, "out1_h5": 31, "out1_h6": 31, "out1_h7": 31, "noN_out3": 7, "out2_h56": 63,
           "out2_h57": 63, "out2_h67": 63, "in1_h1": 31, "in2_h12": 63, "noN_in4": 15,
           "out3": 127, "in4": 255}
CORE_ITEMS = 1 + 6 * len(CORE_LEVELS) + 4 * len(K6_LEVELS)


def shard_of(i):
    return SHARDS[i % len(SHARDS)]


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


# ---------- the cases ----------

def d2_specs():
    return [spec for sh in sorted(m100.SHARDS) for spec in m100.shard_specs(sh)
            if spec["dmeet"] == 2]


def le4(case):
    return m104.k_and_type(m103.space_of(case))[0] <= 4


def sweep_cases():
    """[(spec, case)]: the k <= 4 cases of the d = 2 classes not run before, in m102's order."""
    out = []
    for spec in d2_specs():
        if spec["name"] not in DONE:
            out += [(spec, c) for c in m102.class_cases(spec)[1:] if le4(c)]
    return out


def shard_cases(shard):
    return [x for i, x in enumerate(sweep_cases()) if shard_of(i) == shard]


def level_idx(spec, level):
    """The sorted indices of V spanning W at one level."""
    out, inside = m104.h_split(spec)
    n = list(range(m102.KD))
    table = {"n": n, "out1_h5": n + out[:1], "out1_h6": n + out[1:2], "out1_h7": n + out[2:],
             "noN_out3": out, "out2_h56": n + out[:2], "out2_h57": n + [out[0], out[2]],
             "out2_h67": n + out[1:], "in1_h1": n + inside[:1], "in2_h12": n + inside[:2],
             "noN_in4": inside, "out3": n + out, "in4": n + inside}
    return sorted(table[level])


@functools.lru_cache(maxsize=None)
def cases_by_label(pi, ci):
    return {m102.case_label(c): c for c in m102.class_cases(m100.spec_of(pi, ci))}


def k6_cases():
    """Four cases of o000_c000 with k = 6 that job m102 or m103a answered UNSAT, in m102's order."""
    spec = m100.spec_of(0, 0)
    known = m104.known_unsat(spec["name"])
    cs = [c for c in cases_by_label(0, 0).values()
          if c["kind"] != "t1" and m104.k_and_type(m103.space_of(c))[0] == 6
          and m102.case_label(c) in known]
    return spec, cs[:4]


def core_items():
    """[(spec, case, level, part)]: the control, the core cases level by level, the k = 6 cases."""
    items = [(m100.spec_of(0, 0), m102.case_t2(m102.J3), "n", "control")]
    for level in CORE_LEVELS:
        for pi, ci, lab in m104.CORE:
            items.append((m100.spec_of(pi, ci), cases_by_label(pi, ci)[lab], level, "core"))
    spec, cs = k6_cases()
    for level in K6_LEVELS:
        items += [(spec, c, level, "k6") for c in cs]
    return items


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def append_row(out_dir, name, row):
    rows = m100.load(out_dir, name) or []
    rows.append(row)
    save(out_dir, name, rows)


# ---------- the parts ----------

def run_check(shard, out_dir):
    g = {}
    info = {}
    if shard in SHARDS:
        names = [s["name"] for s in d2_specs()]
        g["d2_13"] = sorted(names) == sorted(D2_LE4)
        cases = sweep_cases()
        labels = [m102.inst_name(spec, c) for spec, c in cases]
        g["sweep_1078"] = len(cases) == SWEEP_TOTAL and len(set(labels)) == SWEEP_TOTAL
        by_class = {}
        for spec, _ in cases:
            by_class[spec["name"]] = by_class.get(spec["name"], 0) + 1
        g["by_class"] = by_class == {n: v for n, v in D2_LE4.items() if n not in DONE}
        types = {m104.k_and_type(m103.space_of(c))[1] for _, c in cases}
        g["types_le4"] = types <= LE4_TYPES
        mine = shard_cases(shard)
        g["shard_size"] = len(mine) == (270 if shard in "ab" else 269)
        info = {"by_class": by_class, "types": sorted(types), "shard": len(mine)}
    else:
        specs = [m100.spec_of(pi, ci) for pi, ci, _ in m104.CORE]
        g["h_split"] = all(m104.h_split(s) == ([8, 9, 10], [4, 5, 6, 7]) for s in specs)
        spec = specs[0]
        sizes = {lv: len(m104.w_masks(level_idx(spec, lv))) for lv in W_SIZES}
        g["w_sizes"] = sizes == W_SIZES
        g["no_repeats"] = all(len(set(level_idx(spec, lv))) == len(level_idx(spec, lv))
                              for lv in W_SIZES)
        g["core_known_unsat"] = all(lab in m104.known_unsat(m100.spec_of(pi, ci)["name"])
                                    for pi, ci, lab in m104.CORE)
        _, k6 = k6_cases()
        g["k6_four"] = len(k6) == 4
        items = core_items()
        g["items"] = len(items) == CORE_ITEMS
        info = {"k6": [m102.case_label(c) for c in k6],
                "k6_types": [m104.k_and_type(m103.space_of(c))[1] for c in k6],
                "levels": {lv: level_idx(spec, lv) for lv in W_SIZES}, "items": len(items)}
    info["graded"] = g
    save(out_dir, f"m105{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({k: v for k, v in info.items() if k != 'graded'}, sort_keys=True)}",
          flush=True)


def run_controls(shard, cap, out_dir):
    tab = {}
    for (pi, ci), case, mode in m102.control_list("a"):
        row = m102.solve_one(m100.spec_of(pi, ci), case, mode, cap, out_dir, "control")
        append_row(out_dir, f"m105{shard}_rows.json", row)
        tally(tab, f"{row['name'][10:]} {case['kind']} {mode}", row["status"])
    print(f"SUMMARY controls {shard} {json.dumps(tab, sort_keys=True)} cap {cap}", flush=True)


def run_sweep(shard, cap, minutes, out_dir):
    start = time.time()
    tab, skipped = {}, []
    for spec, case in shard_cases(shard):
        if time.time() - start > minutes * 60:
            skipped.append(m102.inst_name(spec, case))
            continue
        row = m102.solve_one(spec, case, "sweep", cap, out_dir, "d2")
        row["inv"], row["type"] = m104.k_and_type(m103.space_of(case))
        append_row(out_dir, f"m105{shard}_rows.json", row)
        tally(tab, spec["name"][10:], row["status"])
    save(out_dir, f"m105{shard}_skipped.json", skipped)
    print(f"SUMMARY sweep {shard} skipped {len(skipped)} {json.dumps(tab, sort_keys=True)} "
          f"cap {cap}", flush=True)


def solve_w(spec, case, level, part, cap, out_dir):
    """m104's child (m102's relax CNF plus anisotropy on W only), with sorted indices."""
    idx = level_idx(spec, level)
    tag = m102.inst_name(spec, case) + "_" + level
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(m104.__file__), "--part", "child", "--spec",
           json.dumps(spec), "--case", json.dumps(case), "--idx", json.dumps(idx),
           "--child-out", path]
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
    row.update({"instance": m102.inst_name(spec, case), "name": spec["name"], "level": level,
                "part": part, "idx": idx, "kind": case["kind"], "maps": case["maps"], "inv": inv,
                "type": typ, "wall_seconds": round(time.time() - start, 2), "budget_seconds": cap})
    if res["status"] == "SAT":
        chk = m101.check_model(spec, res)
        chk.update(m102.extra_checks(spec, case, res))
        _, sv = sa.tables(res["A"], res["s"], {(i, k): v for i, k, v in res["B"]}, m102.D)
        chk["aniso_w"] = all(sv[h] for h in m104.w_masks(idx))
        row["check"] = chk
        row["verified"] = chk["aniso_w"] and all(chk[k] for k in m102.needed(spec, "relax"))
    print(f"core {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


def run_core(cap, minutes, out_dir):
    start = time.time()
    tab, skipped = {}, 0
    for spec, case, level, part in core_items():
        if time.time() - start > minutes * 60:
            skipped += 1
            continue
        row = solve_w(spec, case, level, part, cap, out_dir)
        append_row(out_dir, "m105e_core.json", row)
        tally(tab, f"{part} {level}", row["status"])
    print(f"SUMMARY core skipped {skipped} {json.dumps(tab, sort_keys=True)} cap {cap}", flush=True)


def grade(shard, out_dir):
    g = {}
    chk = m100.load(out_dir, f"m105{shard}_check.json")
    if chk is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    out = {}
    if shard in SHARDS:
        rows = m100.load(out_dir, f"m105{shard}_rows.json") or []
        ctrl = [r for r in rows if r["part"] == "control"]
        g["controls_sat"] = len(ctrl) == 3 and all(r["status"] == "SAT" and r.get("verified")
                                                   for r in ctrl)
        sweep = [r for r in rows if r["part"] == "d2"]
        skipped = m100.load(out_dir, f"m105{shard}_skipped.json")
        g["sweep_ran"] = skipped is not None and len(sweep) + len(skipped) == (
            270 if shard in "ab" else 269)
        by_class, by_type = {}, {}
        for r in sweep:
            tally(by_class, r["name"][10:], r["status"])
            tally(by_type, f"inv{r['inv']} {r['type']}", r["status"])
        out.update({"by_class": by_class, "by_type": by_type, "skipped": len(skipped or []),
                    "unsat": sum(r["status"] == "UNSAT" for r in sweep),
                    "unknown": sorted(r["instance"] for r in sweep if r["status"] == "UNKNOWN"),
                    "sat": sorted(r["instance"] for r in sweep if r["status"] == "SAT"),
                    "max_wall": max((r["wall_seconds"] for r in sweep), default=None)})
    else:
        rows = m100.load(out_dir, "m105e_core.json") or []
        ctrl = [r for r in rows if r["part"] == "control"]
        g["control_sat"] = len(ctrl) == 1 and ctrl[0]["status"] == "SAT" and bool(
            ctrl[0].get("verified"))
        g["core_ran"] = len(rows) == CORE_ITEMS
        by_level = {}
        for r in rows:
            if r["part"] != "control":
                tally(by_level, f"{r['part']} {r['level']}", r["status"])
        # a model anisotropic on all of V in a k <= 4 case would contradict the DRAT proofs
        g["no_full_model"] = not any(r["status"] == "SAT" and r["check"].get("anisotropic")
                                     for r in rows if r["part"] != "control")
        out.update({"by_level": by_level,
                    "rows": {f"{r['instance']}_{r['level']}": [r["status"], r["wall_seconds"],
                                                               r["inv"], r["type"]] for r in rows}})
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g[f"verified_{r['instance']}_{r.get('level', r.get('mode'))}"] = bool(r.get("verified"))
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "sweep", "core", "grade"],
                    default="check")
    ap.add_argument("--shard", choices=list(SHARDS) + ["e"], default="a")
    ap.add_argument("--cap-seconds", type=float, default=45.0)
    ap.add_argument("--minutes", type=float, default=120.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.cap_seconds, args.out_dir)
    elif args.part == "sweep":
        run_sweep(args.shard, args.cap_seconds, args.minutes, args.out_dir)
    elif args.part == "core":
        run_core(args.cap_seconds, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m105{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
