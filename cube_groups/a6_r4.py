# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m23: rank 4 in Case B at t = 6 (notes/a8.md, Corollary 36), the shape (c) search of
shape_c.py at (t, k) = (6, 2).

An anisotropic system with t = 6 and dim V = 7 and an element u of rank 4 has k = 2 and
dim V = t + k - 1, so u is in Case A or Case B (Proposition 26), and in Case B it is in shape (c)
(Proposition 27(c), k = 2). shape_c.py splits shape (c) at (6, 2) by the similarity class of the one
4 x 4 matrix M = M_(v_1): 34 classes. M = 0 and M = I are ruled out by hand (Corollary 36), so this
job runs the other 32, each with a time budget. UNSAT for all 32 would show that no such system has
an element of rank 4 in Case B; it would not give A(6) = 6, which also needs Case A at rank 4 and
rank 3 (notes/a8.md). The controls (3, 2) and (4, 2) run every class, as in job m13, and are UNSAT
(A(3) = 3, A(4) = 4).

Parts: controls (selfcheck, then the controls; needs python-sat), solve (the 32 classes at (6, 2);
needs python-sat), grade (the pre-registered predictions of m23/predictions.md).

Usage: python a6_r4.py --part controls|solve|grade [--budget-minutes 5] [--group-minutes 160]
                       [--out-dir DIR]
"""
import argparse
import json
import os
import time

import shape_c as sc

T, K = 6, 2
CONTROLS = ((3, 2), (4, 2))


def reps(t, k, skip_by_hand=True):
    """[(orbit index, Ms)] for the orbits of shape_c at (t, k); with k = 2 and skip_by_hand, the
    classes of M = 0 and M = I (Corollary 36) are left out. The index is the one in
    shape_c.orbits, so instance names agree with shape_c.instance_name."""
    m = t - k
    out = []
    for idx, o in enumerate(sc.orbits(m, k - 1)):
        Ms = o[0]
        if skip_by_hand and k == 2 and Ms[0] in (0, sc.identity(m)):
            continue
        out.append((idx, Ms))
    return out


def selfcheck():
    orb = sc.orbits(T - K, K - 1)
    group = len(sc.gl(T - K))
    skipped = [idx for idx, o in enumerate(orb) if o[0][0] in (0, sc.identity(T - K))]
    st = {"classes_4": len(orb), "group": group, "skipped": skipped,
          "to_run": len(reps(T, K)),
          "controls": {f"{t},{k}": len(reps(t, k, skip_by_hand=False)) for t, k in CONTROLS}}
    st["graded"] = {
        "classes_4": len(orb) == 34,
        "group": group == 20160,
        "orbit_stabiliser": sum(o[1] for o in orb) == 1 << 16
        and all(o[1] * o[2] == group for o in orb),
        "two_skipped": len(skipped) == 2 and all(orb[i][1] == 1 for i in skipped)
        and st["to_run"] == 32,
        "controls": st["controls"] == {"3,2": 2, "4,2": 6}}
    return st


def run(t, k, todo, budget_seconds, group_seconds, out_dir):
    """Each instance in a child process (shape_c.solve_one); once the group budget is used up the
    rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for idx, Ms in todo:
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = {"status": "SKIPPED", "t": t, "k": k, "orbit": idx, "Ms": list(Ms),
                   "name": sc.instance_name(t, k, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = sc.solve_one(t, k, idx, Ms, "auto", min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("sc_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


# Pre-registered (m23/predictions.md). Graded: the selfcheck, the controls UNSAT, and every SAT
# answer verified, with ranks <= 4 (Proposition 26(a)), the facts of Lemma 38, and
# dim(X_1 n R) >= 1 (Proposition 27(c4)). The 32 classes at (6, 2) are exploratory: UNSAT, UNKNOWN
# and SKIPPED are reported, not graded.
def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    for t, k in CONTROLS:
        for idx, _ in reps(t, k, skip_by_hand=False):
            name = sc.instance_name(t, k, idx)
            s = results.get(name, {}).get("status", "missing")
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    for name, r in results.items():
        if r.get("status") != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - r["k"]
        graded[name + "_lemma38"] = all(fa.get(key) for key in
                                        ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e"))
        graded[name + "_d"] = fa.get("dim_D", 0) >= r["k"] - 1
    main_names = [sc.instance_name(T, K, idx) for idx, _ in reps(T, K)]
    status = [results.get(n, {}).get("status", "missing") for n in main_names]
    counts = {s: status.count(s) for s in sorted(set(status))}
    times = {n: results[n].get("wall_seconds") for n in main_names if n in results}
    return {"graded": graded, "ungraded": ungraded, "counts_6_2": counts,
            "status_6_2": dict(zip(main_names, status)), "times_6_2": times,
            "all_unsat_6_2": bool(status) and all(s == "UNSAT" for s in status),
            "any_sat_6_2": any(s == "SAT" for s in status)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["controls", "solve", "grade"], default="grade")
    ap.add_argument("--budget-minutes", type=float, default=5.0)
    ap.add_argument("--group-minutes", type=float, default=160.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)
        for t, k in CONTROLS:
            counts = run(t, k, reps(t, k, skip_by_hand=False), 120, 600, args.out_dir)
            print(f"SUMMARY control t{t} k{k} {json.dumps(counts, sort_keys=True)}", flush=True)
    elif args.part == "solve":
        counts = run(T, K, reps(T, K), args.budget_minutes * 60, args.group_minutes * 60,
                     args.out_dir)
        print(f"SUMMARY solve t{T} k{K} {json.dumps(counts, sort_keys=True)}", flush=True)
    else:
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"counts_6_2 {json.dumps(out['counts_6_2'], sort_keys=True)}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
