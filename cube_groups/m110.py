# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m110: the 3,876 cases with k(T(N)) <= 4 of the 34 d = 1 classes of the rank-0 case of
(B7)_8 (t = 8, dim V = 11), first with anisotropy kept only on N, then with the full sweep CNF for
every case still open (notes/a102.md, cube_groups/m110-predictions.md).

What came back on 2026-10-25 (jobs m108a-d and m109h-j, notes/a102.md): drat-trim verified the DRAT
proofs of all 1,115 d = 2 cases with k <= 4 (Proposition 39). The deletion-minimal systems of job
m109 keep 8 to 10 basis indices of V and 798 to 1,980 equations of (*), so the next step is the
d = 1 classes, not a hand proof along that route.

The CNF "n" (m106: m102's relax CNF plus sigma(h) != 0 for the 15 non-zero h in N) is implied by
m102's sweep CNF, so "n" UNSAT for a case means the case is impossible. In job m106b, 33 of the 37
k <= 4 cases of the d = 1 class o007_c008 were UNSAT at "n" within 60 s, t2_m012 was SAT (a model
that is not anisotropic on all of V) and three were UNKNOWN.

Parts:

    check     the 34 d = 1 classes and their k <= 4 counts against job m104a (m104_count.json),
              3,876 distinct cases, all d = 1 and k <= 4, no t1, m106b's four open cases among
              them, this shard's share, the 15 vectors of N
    controls  three cases known SAT at "n": m106b's two controls (o000_c000 t2_m511, o011_c000
              t3_m001_016) and o007_c008 t2_m012; each must be SAT with a verified model
    run       pass 1: this shard's cases at "n" (60 s each); pass 2: m102's sweep CNF (full
              anisotropy, 120 s) on each case that was not UNSAT at "n", while time remains
    grade     the graded checks of m110-predictions.md

Usage: python m110.py --part check|controls|run|grade --shard a..j [--n-seconds S]
       [--sweep-seconds S] [--minutes M] [--out-dir D]
"""
import argparse
import functools
import json
import os
import time

import m100
import m102
import m103
import m104
import m105
import m106

SHARDS = "abcdefghij"
TOTAL = 3876
# 3,876 = 10 * 387 + 6: shards a-f take 388 cases, g-j 387
SIZE = {s: 388 if s in "abcdef" else 387 for s in SHARDS}
# job m104a (m104_count.json, 2026-10-24): the k <= 4 cases of the 34 classes with d = 1
D1_LE4 = {
    "r3b_t8_B7_o007_c000": 95, "r3b_t8_B7_o007_c001": 179, "r3b_t8_B7_o007_c002": 95,
    "r3b_t8_B7_o007_c003": 63, "r3b_t8_B7_o007_c004": 179, "r3b_t8_B7_o007_c005": 179,
    "r3b_t8_B7_o007_c006": 179, "r3b_t8_B7_o007_c007": 179, "r3b_t8_B7_o007_c008": 37,
    "r3b_t8_B7_o007_c009": 95,
    "r3b_t8_B7_o008_c000": 95, "r3b_t8_B7_o008_c001": 63, "r3b_t8_B7_o008_c002": 49,
    "r3b_t8_B7_o008_c003": 95, "r3b_t8_B7_o008_c004": 37,
    "r3b_t8_B7_o009_c000": 95, "r3b_t8_B7_o009_c001": 179, "r3b_t8_B7_o009_c002": 95,
    "r3b_t8_B7_o009_c003": 63, "r3b_t8_B7_o009_c004": 179, "r3b_t8_B7_o009_c005": 179,
    "r3b_t8_B7_o009_c006": 179, "r3b_t8_B7_o009_c007": 179, "r3b_t8_B7_o009_c008": 37,
    "r3b_t8_B7_o009_c009": 95,
    "r3b_t8_B7_o010_c000": 179, "r3b_t8_B7_o010_c001": 179, "r3b_t8_B7_o010_c002": 49,
    "r3b_t8_B7_o010_c003": 95, "r3b_t8_B7_o010_c004": 95, "r3b_t8_B7_o010_c005": 95,
    "r3b_t8_B7_o010_c006": 95, "r3b_t8_B7_o010_c007": 95, "r3b_t8_B7_o010_c008": 95}
# job m106b (m106b_grade.json): o007_c008 at "n", 60 s
M106B_SAT = "r3b_t8_B7_o007_c008_t2_m012"
M106B_UNKNOWN = ("r3b_t8_B7_o007_c008_t3_m004_034", "r3b_t8_B7_o007_c008_t3_m015_049",
                 "r3b_t8_B7_o007_c008_t2_m015")
CONTROLS = ("r3b_t8_B7_o000_c000_t2_m511", "r3b_t8_B7_o011_c000_t3_m001_016", M106B_SAT)


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


def drop_child(out_dir, row):
    """Remove the child's answer file unless it holds a model (SAT)."""
    path = os.path.join(out_dir, row["tag"] + ".child.json")
    if row["status"] != "SAT" and os.path.exists(path):
        os.remove(path)


# ---------- the cases ----------

@functools.lru_cache(maxsize=None)
def d1_specs():
    return tuple(spec for sh in sorted(m100.SHARDS) for spec in m100.shard_specs(sh)
                 if spec["dmeet"] == 1)


@functools.lru_cache(maxsize=None)
def sweep_cases():
    """((spec, case), ...): the k <= 4 cases of the 34 d = 1 classes, in m102's order."""
    out = []
    for spec in d1_specs():
        out += [(spec, c) for c in m102.class_cases(spec)[1:] if m105.le4(c)]
    return tuple(out)


def shard_of(i):
    return SHARDS[i % len(SHARDS)]


def shard_cases(shard):
    return [x for i, x in enumerate(sweep_cases()) if shard_of(i) == shard]


def control_cases():
    return m106.transfer_controls() + [m106.case_of(M106B_SAT)]


def followups(rows):
    """The instances that get the sweep CNF: those whose answer at "n" was not UNSAT."""
    return [r["instance"] for r in rows if r["part"] == "n" and r["status"] != "UNSAT"]


def final_status(parts):
    """One case's answer from {part: status}: UNSAT if any CNF was UNSAT (each is implied by the
    full sweep CNF), else the sweep's answer if it ran, else the answer at "n"."""
    if "UNSAT" in parts.values():
        return "UNSAT"
    return parts.get("sweep", parts.get("n"))


# ---------- the parts ----------

def run_check(shard, out_dir):
    g, info = {}, {}
    g["classes_34"] = sorted(s["name"] for s in d1_specs()) == sorted(D1_LE4)
    cases = sweep_cases()
    names = [m102.inst_name(s, c) for s, c in cases]
    g["cases_3876"] = len(cases) == TOTAL and len(set(names)) == TOTAL
    by_class = {}
    for s, _ in cases:
        by_class[s["name"]] = by_class.get(s["name"], 0) + 1
    g["by_class"] = by_class == D1_LE4
    g["all_d1_le4"] = all(s["dmeet"] == 1 and m105.le4(c) for s, c in cases)
    g["no_t1"] = all(c["kind"] != "t1" for _, c in cases)
    g["m106b_inside"] = {M106B_SAT, *M106B_UNKNOWN} <= set(names)
    types = {m104.k_and_type(m103.space_of(c))[1] for _, c in cases}
    g["types_le4"] = types <= m105.LE4_TYPES
    g["shard_size"] = len(shard_cases(shard)) == SIZE[shard]
    g["n_15"] = sorted(m106.n_masks()) == list(range(1, 16))
    g["controls"] = [m102.inst_name(s, c) for s, c in control_cases()] == list(CONTROLS)
    info["types"] = sorted(types)
    info["shard"] = [x for i, x in enumerate(names) if shard_of(i) == shard]
    info["graded"] = g
    save(out_dir, f"m110{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'types': info['types'], 'shard': len(info['shard'])}, sort_keys=True)}",
          flush=True)


def run_controls(shard, cap, out_dir):
    rows = []
    for spec, case in control_cases():
        x = m102.inst_name(spec, case)
        row = m106.solve_masks(spec, case, m106.n_masks(), f"{x}_control", "control", cap, out_dir)
        drop_child(out_dir, row)
        rows.append(row)
    g = {"controls_sat": len(rows) == 3 and all(r["status"] == "SAT" and r.get("verified")
                                                for r in rows)}
    save(out_dir, f"m110{shard}_controls.json", {"graded": g, "rows": rows})
    print(f"SUMMARY controls {shard} all_match {all(g.values())} "
          f"{json.dumps([[r['instance'][10:], r['status'], r.get('verified')] for r in rows])}",
          flush=True)


def run(shard, n_cap, sweep_cap, minutes, out_dir):
    start = time.time()
    name = f"m110{shard}_rows.json"
    tab, skipped = {}, []
    cases = {m102.inst_name(s, c): (s, c) for s, c in shard_cases(shard)}
    for x, (spec, case) in cases.items():
        if time.time() - start > minutes * 60:
            skipped.append(f"{x}_n")
            continue
        row = m106.solve_masks(spec, case, m106.n_masks(), f"{x}_n", "n", n_cap, out_dir)
        drop_child(out_dir, row)
        append_row(out_dir, name, row)
        tally(tab, "n", row["status"])
    for x in followups(m100.load(out_dir, name) or []):
        if time.time() - start > minutes * 60:
            skipped.append(f"{x}_sweep")
            continue
        spec, case = cases[x]
        row = m102.solve_one(spec, case, "sweep", sweep_cap, out_dir, "sweep")
        row["tag"] = f"{x}_sweep"
        row["inv"], row["type"] = m104.k_and_type(m103.space_of(case))
        drop_child(out_dir, row)
        append_row(out_dir, name, row)
        tally(tab, "sweep", row["status"])
    save(out_dir, f"m110{shard}_skipped.json", skipped)
    print(f"SUMMARY run {shard} skipped {len(skipped)} {json.dumps(tab, sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def grade(shard, out_dir):
    g, out = {}, {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m110{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    rows = m100.load(out_dir, f"m110{shard}_rows.json") or []
    skipped = m100.load(out_dir, f"m110{shard}_skipped.json")
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g[f"verified_{r['tag']}"] = bool(r.get("verified"))
    n_rows = [r for r in rows if r["part"] == "n"]
    g["n_ran"] = skipped is not None and len(n_rows) + sum(
        x.endswith("_n") for x in skipped) == SIZE[shard]
    # the sweep CNF ran (or was skipped for time) on exactly the cases not UNSAT at "n"
    swept = ({r["instance"] for r in rows if r["part"] == "sweep"}
             | {x[:-len("_sweep")] for x in skipped or [] if x.endswith("_sweep")})
    g["sweep_rule"] = swept == set(followups(rows))
    st = {}
    for r in rows:
        st.setdefault(r["instance"], {})[r["part"]] = r["status"]
    final = {x: final_status(v) for x, v in st.items()}
    # a model anisotropic on all of V would be a system with t = 8, dim V = 11: flag it
    out["full_models"] = sorted(r["tag"] for r in rows if r["status"] == "SAT"
                                and r["check"].get("anisotropic"))
    by_part, by_class, by_type = {}, {}, {}
    for r in rows:
        tally(by_part, r["part"], r["status"])
    info = {r["instance"]: (r["name"], r["type"]) for r in rows}
    for x, f in final.items():
        tally(by_class, info[x][0][10:], f)
        tally(by_type, info[x][1], f)
    n_unsat = [r["wall_seconds"] for r in n_rows if r["status"] == "UNSAT"]
    out.update({"by_part": by_part, "by_class": by_class, "by_type": by_type,
                "unsat": sum(f == "UNSAT" for f in final.values()),
                "open": sorted(x for x, f in final.items() if f != "UNSAT"),
                "sat_n": sorted(x for x, v in st.items() if v.get("n") == "SAT"),
                "sat_sweep": sorted(x for x, v in st.items() if v.get("sweep") == "SAT"),
                "skipped": skipped or [],
                "n_unsat_max_seconds": max(n_unsat, default=None),
                "n_unsat_mean_seconds": round(sum(n_unsat) / len(n_unsat), 2) if n_unsat else None,
                "cases": st})
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "run", "grade"], default="check")
    ap.add_argument("--shard", choices=list(SHARDS), default="a")
    ap.add_argument("--n-seconds", type=float, default=60.0)
    ap.add_argument("--sweep-seconds", type=float, default=120.0)
    ap.add_argument("--minutes", type=float, default=200.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.n_seconds, args.out_dir)
    elif args.part == "run":
        run(args.shard, args.n_seconds, args.sweep_seconds, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m110{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "cases")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
