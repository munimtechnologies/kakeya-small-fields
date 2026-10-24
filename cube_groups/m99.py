# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m99: the rank-3 configurations (B7)_8 and (B6)_8 of Proposition 36 for t = 8 and dim V = 11,
split by the pair (ker A_u, Im A_u) and then by the matrix A_u, with m42's classification unchanged
(cube_groups/m99-predictions.md, notes/a91.md).

What came back on 2026-10-24 (jobs m98a and m98b, notes/a91.md): every graded check held, so type
(N4) at (8, 11) is empty (Proposition 37) and no element has rank 4 at (8, 11) (Corollary 122),
both computer-assisted. By Proposition 36 (notes/a83.md), A(8) <= 10 now holds if (B7)_8 (p = 7,
ker phi of dimension 4) and (B6)_8 (p = 6, ker phi of dimension 5) are empty. Lemma 101 (by hand,
notes/a91.md) counts their pair orbits: 13 and 51.

Parts:

    classify   m42.classify at (t, p) = (7, 6), (7, 5) as controls (m42a's 13 and 49 pairs, 68 and
               420 classes) and at (8, 7), (8, 6); every pair is sorted into the kinds of Lemma 101
               and compared with hand_breakdown; the pairs and classes are written for later jobs
    pilot      the first class of the first three pairs of each shape at (8, 11), with m42's
               encoding and hints, solved with a cap (a measurement, not a search of the shape)
    grade      the graded checks of m99-predictions.md

Usage: python m99.py --part classify|pilot|grade [--cap-seconds S] [--per-shape N] [--out-dir DIR]
"""
import argparse
import json
import os
import time

import m42
import sat_aniso as sa

RHO = 3
ORDER = ((7, 6), (7, 5), (8, 7), (8, 6))
SHAPE_NAMES = {(7, 6): "B6", (7, 5): "B5", (8, 7): "B7_8", (8, 6): "B6_8"}
D8 = 11
# job m42a (compete-results, 2026-10-19; notes/a32.md, a33.md): pairs and classes at t = 7
M42A = {(7, 6): (13, 68), (7, 5): (49, 420)}
# Lemma 101 (notes/a91.md), written before the job ran
HAND_PAIRS_T8 = {(8, 7): 13, (8, 6): 51}
HAND_BY_X_T8 = {(8, 7): {11811: 13}, (8, 6): {651: 20, 11160: 31}}
HAND_GROUP_T8 = {(8, 7): 163849992929280, (8, 6): 2580314849280}
HAND_SUBSPACES_T8 = {"x1": 11811, "r": 97155}


# ---------- the count of Lemmas 83 and 101 ----------

def gaussian(n, k):
    """The number of k-dimensional subspaces of F_2^n."""
    num = den = 1
    for i in range(k):
        num *= (1 << (n - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def step2(u, k, p):
    """Orbits of the stabiliser of U (dim u) in GL(P) (dim p) on subspaces R of H0 = L + P of
    dimension k, by kind (Step 2 of Lemma 83)."""
    js = range(max(0, u + k - p), min(u, k) + 1)
    return {"P": len(js),
            "L": len(range(max(0, u + k - 1 - p), min(u, k - 1) + 1)),
            "graph": sum(1 if j in (0, k) else 2 for j in js)}


def hand_breakdown(t, p, rho):
    """The pair orbits of Lemmas 83 and 101 by side (alpha: X_1 inside H0, beta: not) and kind
    (P, L, graph for R inside H0; out for R not inside H0), for p = t - 1 and p = t - 2."""
    kx = t - rho
    out = {}
    if p == t - 1:
        for kind, n in step2(kx - 1, rho, p).items():
            out["alpha_" + kind] = n
    elif p == t - 2:
        if (kx - 2) + (rho - 1) >= p:
            raise ValueError("Step 5 needs dim(Y + pi(R0)) < p")
        a_in, b_in = step2(kx - 1, rho, p), step2(kx - 2, rho, p)
        for kind in a_in:
            out["alpha_" + kind] = a_in[kind]
            out["beta_" + kind] = b_in[kind]
        out["alpha_out"] = sum(step2(kx - 1, rho - 1, p).values())
        out["beta_out"] = 2 * sum(step2(kx - 2, rho - 1, p).values())
    else:
        raise ValueError("only p = t - 1 and p = t - 2")
    return {k: v for k, v in out.items() if v}


def hand_pairs(t, p, rho):
    return sum(hand_breakdown(t, p, rho).values())


def hand_by_x(t, p, rho):
    """{orbit size of X_1: number of pair orbits over it}."""
    kx = t - rho
    hb = hand_breakdown(t, p, rho)
    if p == t - 1:
        return {gaussian(t - 1, kx - 1): sum(hb.values())}
    alpha = gaussian(t - 2, kx - 1)
    return {alpha: sum(v for k, v in hb.items() if k.startswith("alpha")),
            gaussian(t - 1, kx - 1) - alpha: sum(v for k, v in hb.items()
                                                 if k.startswith("beta"))}


def machine_key(t, p, pr):
    """The side and kind of a computed pair orbit, read off m42.invariants."""
    inv = m42.invariants(t, p, pr["x1"], pr["r"])
    side = "alpha" if inv["X1_in_H0"] else "beta"
    if not inv["R_in_H0"]:
        kind = "out"
    elif inv["dim_R_P"] == len(pr["r"]):
        kind = "P"
    elif inv["x0_in_R"]:
        kind = "L"
    else:
        kind = "graph"
    return side + "_" + kind


# ---------- the parts ----------

def classify_one(t, p, out_dir):
    start = time.time()
    pairs, cls, pst = m42.classify(t, p, RHO)
    go = m42.group_order(t, p)
    info = m42.check_classes(t, p, RHO, pairs, cls)
    by_x, breakdown, rows = {}, {}, []
    for pi, (pr, (cl, st)) in enumerate(zip(pairs, cls)):
        key = machine_key(t, p, pr)
        by_x[pr["x_orbit_size"]] = by_x.get(pr["x_orbit_size"], 0) + 1
        breakdown[key] = breakdown.get(key, 0) + 1
        rows.append({"pair": pi, "x1": list(pr["x1"]), "r": list(pr["r"]), "size": pr["size"],
                     "x_orbit_size": pr["x_orbit_size"], "key": key,
                     "invariants": m42.invariants(t, p, pr["x1"], pr["r"]),
                     "classes": [[rep, len(m)] for rep, m in cl], "stats": st})
    info.update({"t": t, "p": p, "pairs": len(pairs), "group_order": go,
                 "by_x_orbit_size": {str(k): v for k, v in sorted(by_x.items())},
                 "breakdown": dict(sorted(breakdown.items())),
                 "hand_breakdown": dict(sorted(hand_breakdown(t, p, RHO).items())),
                 "total": sum(pr["size"] for pr in pairs),
                 "pairs_divide_G": all(go % pr["size"] == 0 for pr in pairs),
                 "x_units_ok": pst["units_ok"], "x_orbits": pst["x_orbits"],
                 "reps_rank_3": all(sa.rank_f2(m42.cols_of(rep, t)) == RHO for cl, _ in cls
                                    for rep, _ in cl),
                 "classes_by_key": {}, "seconds": round(time.time() - start, 1)})
    for r in rows:
        info["classes_by_key"][r["key"]] = info["classes_by_key"].get(r["key"], 0) + len(r["classes"])
    with open(os.path.join(out_dir, f"m99_classes_t{t}_B{p}.json"), "w") as f:
        json.dump({"info": info, "pairs": rows}, f, indent=1)
    print(f"classify t{t}_B{p} ({SHAPE_NAMES[(t, p)]}): pairs {info['pairs']} classes "
          f"{info['classes']} by_x {json.dumps(info['by_x_orbit_size'])} breakdown "
          f"{json.dumps(info['breakdown'])} hand {json.dumps(info['hand_breakdown'])} "
          f"valid {info['sizes_add_up'] and info['members'] and info['units_in_H'] and info['divide_H']} "
          f"stable {info['stable']} seconds {info['seconds']}", flush=True)
    return info


def run_classify(out_dir):
    infos = {}
    for t, p in ORDER:
        infos[f"t{t}_B{p}"] = classify_one(t, p, out_dir)
    with open(os.path.join(out_dir, "m99_classify.json"), "w") as f:
        json.dump(infos, f, indent=1)
    print("SUMMARY classify " + json.dumps({k: [v["pairs"], v["classes"]] for k, v in
                                            infos.items()}, sort_keys=True), flush=True)


def pilot_specs(out_dir, per_shape):
    sps = []
    for t, p in ((8, 7), (8, 6)):
        with open(os.path.join(out_dir, f"m99_classes_t{t}_B{p}.json")) as f:
            rows = json.load(f)["pairs"]
        for row in rows[:per_shape]:
            rep, size = row["classes"][0]
            sps.append({"name": m42.instance_name(t, p, row["pair"], 0), "kind": "main", "t": t,
                        "d": D8, "p": p, "pair": row["pair"], "cls": 0, "x1": row["x1"],
                        "r": row["r"], "au": rep, "class_size": size, "pair_size": row["size"],
                        "key": row["key"]})
    return sps


def run_pilot(out_dir, cap, per_shape):
    counts, rows = {}, []
    for sp in pilot_specs(out_dir, per_shape):
        res = m42.solve_one(sp, "auto", cap, out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
        rows.append({k: res.get(k) for k in ("name", "key", "status", "seconds", "wall_seconds",
                                             "vars", "clauses", "verified", "max_rank",
                                             "rank_u")})
    with open(os.path.join(out_dir, "m99_pilot.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print(f"SUMMARY pilot {json.dumps(counts, sort_keys=True)} cap {cap}", flush=True)


# ---------- grading (pre-registered in m99-predictions.md) ----------

def load(out_dir, name):
    try:
        with open(os.path.join(out_dir, name)) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def grade(out_dir):
    g = {}
    infos = load(out_dir, "m99_classify.json") or {}
    for (t, p) in ORDER:
        v = infos.get(f"t{t}_B{p}")
        key = f"t{t}_B{p}"
        if v is None:
            g[key + "_ran"] = False
            continue
        g[key + "_valid"] = (v["sizes_add_up"] and v["members"] and v["units_in_H"]
                             and v["divide_H"] and v["pairs_divide_G"] and v["x_units_ok"]
                             and v["reps_rank_3"])
        g[key + "_total"] = v["total"] == gaussian(t - 1, t - RHO - 1) * gaussian(t, RHO)
        g[key + "_breakdown"] = v["breakdown"] == v["hand_breakdown"]
        g[key + "_by_x"] = v["by_x_orbit_size"] == {str(k): n for k, n in
                                                     sorted(hand_by_x(t, p, RHO).items())}
        if t == 7:
            g[key + "_as_m42a"] = (v["pairs"], v["classes"]) == M42A[(t, p)]
        else:
            g[key + "_group"] = v["group_order"] == HAND_GROUP_T8[(t, p)]
            g[key + "_pairs"] = v["pairs"] == HAND_PAIRS_T8[(t, p)]
            g[key + "_by_x_hand"] = v["by_x_orbit_size"] == {
                str(k): n for k, n in sorted(HAND_BY_X_T8[(t, p)].items())}
    pilot = load(out_dir, "m99_pilot.json") or []
    for r in pilot:
        if r["status"] == "SAT":
            g["pilot_verified_" + r["name"]] = bool(r.get("verified"))
    out = {"graded": g,
           "classes": {k: v["classes"] for k, v in infos.items()},
           "classes_by_key": {k: v["classes_by_key"] for k, v in infos.items()},
           "stable": {k: v["stable"] for k, v in infos.items()},
           "seconds": {k: v["seconds"] for k, v in infos.items()},
           "pilot": {r["name"]: [r["status"], r.get("wall_seconds")] for r in pilot}}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["classify", "pilot", "grade"], default="classify")
    ap.add_argument("--cap-seconds", type=float, default=240.0)
    ap.add_argument("--per-shape", type=int, default=3)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "classify":
        run_classify(args.out_dir)
    elif args.part == "pilot":
        run_pilot(args.out_dir, args.cap_seconds, args.per_shape)
    else:
        out = grade(args.out_dir)
        with open(os.path.join(args.out_dir, "m99_grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad[:12]} "
              f"classes {json.dumps(out['classes'], sort_keys=True)} stable "
              f"{json.dumps(out['stable'], sort_keys=True)} pilot "
              f"{json.dumps(out['pilot'], sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
