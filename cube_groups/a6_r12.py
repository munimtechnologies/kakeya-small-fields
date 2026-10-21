# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m28: elements of rank 1 and 2 at t = 6, dim V = 7, in the shapes that Lemma 68
(notes/a15.md) leaves for the elements of U+ of a Case B element of rank 4.

Lemma 68: let u be a Case B element of rank 4 in an anisotropic system with t = 6 and dim V = 7
(so U+ = N has dimension 2), and let n in N have M_n of rank r in {1, 2, 3}. Then n has rank r and
is in shape ("A", r + 2) or ("B", r + 1) in the sense of a6_r3.py. Of the four instances that job
m25 left (notes/a12.md), q2_t6_i03 has an element of rank 3 (job m27 searches ("A", 5) and
("B", 4)), q2_t6_i07 one of rank 1 and q2_t6_i119, q2_t6_i120 one of rank 2. This job searches
the rank-1 shapes ("A", 3), ("B", 2) and the rank-2 shapes ("A", 4), ("B", 3) at t = 6, dim V = 7,
with the encoding, normal form and runner of a6_r3.py (Lemma 67) unchanged. Only the subspaces are
listed differently (by extension, as a6_r3.subspaces would try 7 million 5-tuples at rank 1).

UNSAT for every orbit of ("A", 3) and ("B", 2) rules out q2_t6_i07; for ("A", 4) and ("B", 3), the
pair q2_t6_i119, q2_t6_i120. A SAT answer is checked by brute force and would be a system with
dim V = 7, so A(6) = 7.

Parts: selfcheck (pure Python: subspace counts, the groups, the orbits, hand values), controls
(the controls of a6_r3.py through this module's orbits; needs python-sat), solve (one shape at
t = 6; needs python-sat), grade (the predictions of m28/predictions.md).

Usage: python a6_r12.py --part selfcheck|controls|solve|grade [--shape A3|B2|A4|B3]
                        [--budget-minutes 2] [--group-minutes 20] [--out-dir DIR]
"""
import argparse
import json
import os

import a6_r3 as r3

T = 6
D = 7
# shape key -> (shape, p, rho), as Lemma 68 gives them: ("A", rho + 2) and ("B", rho + 1).
SHAPES = {"A3": ("A", 3, 1), "B2": ("B", 2, 1), "A4": ("A", 4, 2), "B3": ("B", 3, 2)}
# Which instance of job m25/m26 each pair of shapes rules out when all of its orbits are UNSAT.
KILLS = {"q2_t6_i07": ("A3", "B2"), "q2_t6_i119": ("A4", "B3"), "q2_t6_i120": ("A4", "B3")}


def lemma68_shapes(rho):
    return (("A", rho + 2), ("B", rho + 1))


# ---------- subspaces and orbits ----------

def subspaces_fast(t, k, containing=0):
    """The same list as a6_r3.subspaces, built by adding one vector at a time."""
    level = {r3.rref([containing])} if containing else {()}
    for _ in range(1 if containing else 0, k):
        nxt = set()
        for s in level:
            for v in range(1, 1 << t):
                if not r3.in_span(s, v):
                    nxt.add(r3.rref(list(s) + [v]))
        level = nxt
    return sorted(level)


def orbits(t, shape, p, rho):
    """a6_r3.orbits with subspaces_fast: [(X_1, R, orbit size)] for the orbits of the pairs
    (X_1 containing e_0, R) under the transvections of G, by decreasing dim(X_1 n R)."""
    xs = subspaces_fast(t, t - rho, 1)
    rs = subspaces_fast(t, rho)
    xi = {x: i for i, x in enumerate(xs)}
    ri = {r: i for i, r in enumerate(rs)}
    gens = r3.generators(t, shape, p)
    gx = [[xi[r3.image(g, x, t)] for x in xs] for g in gens]
    gr = [[ri[r3.image(g, r, t)] for r in rs] for g in gens]
    nr = len(rs)
    seen = bytearray(len(xs) * nr)
    found = []
    for a0 in range(len(xs)):
        for b0 in range(nr):
            if seen[a0 * nr + b0]:
                continue
            seen[a0 * nr + b0] = 1
            stack, size = [(a0, b0)], 0
            while stack:
                a, b = stack.pop()
                size += 1
                for g in range(len(gens)):
                    a2, b2 = gx[g][a], gr[g][b]
                    if not seen[a2 * nr + b2]:
                        seen[a2 * nr + b2] = 1
                        stack.append((a2, b2))
            found.append((xs[a0], rs[b0], size))
    order = sorted(range(len(found)), key=lambda i: (-r3.dim_meet(found[i][0], found[i][1]), i))
    return [found[i] for i in order]


def instance_name(t, rho, shape, p, idx):
    return f"r{rho}_t{t}_{shape}{p}_o{idx:03d}"


def specs(t, d, rho, shape, p):
    return [{"t": t, "d": d, "rho": rho, "shape": shape, "p": p, "x1": list(x1), "r": list(r),
             "size": size, "name": instance_name(t, rho, shape, p, idx)}
            for idx, (x1, r, size) in enumerate(orbits(t, shape, p, rho))]


# ---------- selfcheck ----------

# Hand values (m28/predictions.md): Gaussian binomials of F_2^6, and k-spaces through e_0 =
# (k - 1)-spaces of F_2^5.
HAND_SUBSPACES = {(6, 1, 0): 63, (6, 2, 0): 651, (6, 3, 0): 1395, (6, 4, 0): 651, (6, 5, 0): 63,
                  (6, 2, 1): 31, (6, 3, 1): 155, (6, 4, 1): 155, (6, 5, 1): 31,
                  (4, 2, 0): 35, (4, 2, 1): 7}
HAND_GROUP = {"A3": 2064384, "B2": 516096, "A4": 2064384, "B3": 258048}
HAND_GENS = {"A3": 19, "B2": 17, "A4": 19, "B3": 16}
HAND_TOTALS = {1: 31 * 63, 2: 155 * 651}


def selfcheck():
    st = {"subspaces": {}, "fast_matches": {}, "group_order": {}, "gens": {}, "gens_in_group": {},
          "orbit_counts": {}, "orbit_sizes": {}, "totals": {}, "divides": {}, "invariants": {},
          "controls_orbit_sizes": {}}
    for (t, k, c) in HAND_SUBSPACES:
        st["subspaces"][f"{t},{k},{c}"] = len(subspaces_fast(t, k, c))
    for t, k, c in ((4, 2, 0), (4, 2, 1), (6, 2, 1), (6, 3, 1), (6, 3, 0)):
        st["fast_matches"][f"{t},{k},{c}"] = subspaces_fast(t, k, c) == r3.subspaces(t, k, c)
    for key, (s, p, rho) in SHAPES.items():
        orb = orbits(T, s, p, rho)
        go = r3.group_order(T, s, p)
        gens = r3.generators(T, s, p)
        st["group_order"][key] = go
        st["gens"][key] = len(gens)
        st["gens_in_group"][key] = all(r3.in_group(g, T, s, p) for g in gens)
        st["orbit_counts"][key] = len(orb)
        st["orbit_sizes"][key] = sorted(o[2] for o in orb)
        st["totals"][key] = sum(o[2] for o in orb)
        st["divides"][key] = all(go % o[2] == 0 for o in orb)
        st["invariants"][key] = [r3.invariants(T, s, p, x1, r) for x1, r, _ in orb]
    for (t, s, p), sizes in r3.HAND_ORBITS.items():
        rho = 1 if t == 2 else 2
        st["controls_orbit_sizes"][f"t{t}_{s}{p}"] = sorted(o[2] for o in orbits(t, s, p, rho))
    st["graded"] = {
        "subspaces": all(st["subspaces"][f"{t},{k},{c}"] == n
                         for (t, k, c), n in HAND_SUBSPACES.items()),
        "fast_matches": all(st["fast_matches"].values()),
        "group_order": all(st["group_order"][k] == n for k, n in HAND_GROUP.items()),
        "gens": all(st["gens"][k] == n for k, n in HAND_GENS.items()),
        "gens_in_group": all(st["gens_in_group"].values()),
        "totals": all(st["totals"][k] == HAND_TOTALS[SHAPES[k][2]] for k in SHAPES),
        "divides": all(st["divides"].values()),
        "hand_orbits": all(st["controls_orbit_sizes"][f"t{t}_{s}{p}"] == v
                           for (t, s, p), v in r3.HAND_ORBITS.items())}
    return st


# ---------- grading ----------

def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if (fn.startswith(("r1_", "r2_")) and fn.endswith(".json")
                and not fn.endswith(".child.json") and not fn.endswith(".spec.json")):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    for name, r in results.items():
        if r.get("t") == T:
            continue
        s = r.get("status", "missing")
        if s in ("SAT", "UNSAT"):
            graded[name] = s == r3.expected_control(r["t"], r["shape"], r["r"])
            if s == "SAT":
                graded[name + "_verified"] = bool(r.get("verified"))
        else:
            ungraded[name] = s
    per_shape = {}
    for key, (s, p, rho) in SHAPES.items():
        st = [r for n, r in sorted(results.items()) if r.get("t") == T and r["shape"] == s
              and r["p"] == p and r.get("rho") == rho]
        status = [r.get("status") for r in st]
        per_shape[key] = {"instances": len(st),
                          "counts": {x: status.count(x) for x in sorted(set(status))},
                          "all_unsat": bool(st) and all(x == "UNSAT" for x in status),
                          "undecided": [r["name"] for r in st if r.get("status") != "UNSAT"]}
        for r in st:
            if r.get("status") == "SAT":
                graded[r["name"] + "_verified"] = bool(r.get("verified"))
    ruled_out = {name: all(per_shape[k]["all_unsat"] for k in keys)
                 for name, keys in KILLS.items()}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "per_shape": per_shape,
            "ruled_out": ruled_out, "times": times,
            "any_sat_6": any(r.get("status") == "SAT" for r in results.values()
                             if r.get("t") == T)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "grade"],
                    default="selfcheck")
    ap.add_argument("--shape", choices=sorted(SHAPES), default="B2")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=2.0)
    ap.add_argument("--group-minutes", type=float, default=20.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        sps = [sp for t, d, rho, s, p in r3.CONTROLS for sp in specs(t, d, rho, s, p)]
        out = r3.run_group(sps, args.solver, 120, 3600, args.out_dir)
        print(f"SUMMARY controls {json.dumps(out, sort_keys=True)}", flush=True)
    elif args.part == "solve":
        s, p, rho = SHAPES[args.shape]
        sps = specs(T, D, rho, s, p)
        out = r3.run_group(sps, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                           args.out_dir)
        print(f"SUMMARY solve {args.shape} instances {len(sps)} {json.dumps(out, sort_keys=True)}",
              flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_6 {out['any_sat_6']} ruled_out {json.dumps(out['ruled_out'])} "
              + " ".join(f"{k} {v['counts']}" for k, v in out["per_shape"].items()), flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
