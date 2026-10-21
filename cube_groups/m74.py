# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m74: a machine check of Proposition 34 (notes/a58.md), the second-matrix split of the three
classes of (B5) with d = dim(X_1 n R) = 2 that are still open at t = 7 and dim V = 9:
r3b_t7_B5_o004_c001, o005_c005 and o006_c000 (cube_groups/m74-predictions.md, notes/a61.md). It
counts; it solves nothing.

Everything is m55.py's, imported unchanged: the space of maps (A x0 = 0, A(H0) inside R, A e_6
free), Adm (rank at most 2 on X_1, rank at most 3, A + A_u of rank at most 3, not 0, not A_u), the
group G found by solving g x0 = x0, g P = P, g A_u = A_u g, and the union-find over a generating set
of G whose closure is checked to be all of G. This file sets m55's class list and hand orders to
the three classes and grades d = 2 where m55 graded R inside X_1 (d = 3). A_u is m42d's
representative (m57.py's LEFTOVERS); X_1 = span(e_0, ..., e_3) lies in H0 (pair orbits 4, 5, 6),
and R is the image of the pair as in m57.py's PAIR_R.

Graded against Proposition 34, written before the job ran: (b) |Adm| = 405566 for each class,
(c) |G| = 2048, 512 and 1024, (d) the lower bound ceil(405566 / (2 |G|)) = 100, 397 and 199, and
the number of classes at least that; also m55's own checks (G element by element, the action closed
on Adm, the fast rank test against the slow one, the conjugation tables against direct
conjugation, orbit sizes dividing 2 |G| and adding up to |Adm|). Reported, not graded: the number
of classes and its split by rank on X_1; the classes of rank 1 and 2 are the split instances that
are needed, because the rank-0 sweep of each class was UNSAT (job m64b, Lemma 93 (a)).

Usage: python m74.py [--out-dir DIR] [--names NAME,NAME]
"""
import argparse
import json
import os
import random

import m55

ALPHA = m55.ALPHA
# m42d's representatives (m57.py's LEFTOVERS), X_1 and R (m57.py's PAIR_R[4], [5], [6]).
CLASSES = {
    "r3b_t7_B5_o004_c001": (8590204928, ALPHA, (16, 4, 2)),
    "r3b_t7_B5_o005_c005": (8590207056, ALPHA, (16, 4, 3)),
    "r3b_t7_B5_o006_c000": (4295499792, ALPHA, (17, 4, 2)),
}
# Proposition 34 (c) and (d), by hand (notes/a58.md), written before this job ran.
HAND_ORDER = {"r3b_t7_B5_o004_c001": 2048, "r3b_t7_B5_o005_c005": 512,
              "r3b_t7_B5_o006_c000": 1024}
HAND_LOWER = {"r3b_t7_B5_o004_c001": 100, "r3b_t7_B5_o005_c005": 397,
              "r3b_t7_B5_o006_c000": 199}
HAND_D = 2


def install():
    """m55's class list and hand orders become this job's."""
    m55.CLASSES, m55.HAND_ORDER = CLASSES, HAND_ORDER


install()


def meet_dim(x1, rb):
    """dim(X_1 n R): the intersection of the two spans has 2^dim elements."""
    return len(m55.span_set(x1) & m55.span_set(rb)).bit_length() - 1


def grade(results):
    checks = {}
    for name, r in results.items():
        s = r["structure"]
        tag = name[10:]
        checks["structure_" + tag] = (s["rank_au"] == 3 and s["ker_is_x1"] and s["im_is_r"]
                                      and meet_dim(tuple(r["x1"]), tuple(r["r"])) == HAND_D
                                      and not s["d3"] and s["x1_in_h0"]
                                      and tuple(r["x1"]) == ALPHA)
        checks["group_" + tag] = (r["group_checked"] and r["order"] == r["order_hand"]
                                  == HAND_ORDER[name])
        checks["valid_" + tag] = (r["valid"] == r["valid_hand"] == 405566 and r["action_closed"]
                                  and r["fast_matches_slow"] and r["linear_ok"])
        checks["sizes_" + tag] = r["sizes_ok"]
        checks["lower_" + tag] = (r["lower_bound"] == HAND_LOWER[name]
                                  and r["orbits"] >= r["lower_bound"])
    by_rank = {k[10:]: r["orbits_by_rank_x1"] for k, r in results.items()}
    split = {k: sum(v for rk, v in b.items() if rk in ("1", "2")) for k, b in by_rank.items()}
    return {"checks": checks, "passed": sum(checks.values()), "total": len(checks),
            "all_held": all(checks.values()),
            "orbits": {k[10:]: r["orbits"] for k, r in results.items()},
            "orbits_by_rank_x1": by_rank,
            "split_rank12": split, "split_rank12_total": sum(split.values()),
            "lower_bounds": {k[10:]: r["lower_bound"] for k, r in results.items()},
            "orders": {k[10:]: r["order"] for k, r in results.items()},
            "valid": {k[10:]: r["valid"] for k, r in results.items()}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--names", default=",".join(CLASSES))
    args = ap.parse_args()
    install()
    os.makedirs(args.out_dir, exist_ok=True)
    rng = random.Random(74)
    results, cache = {}, {}
    for name in args.names.split(","):
        results[name] = r = m55.run_class(name, rng, cache)
        print(name, "order", r["order"], "valid", r["valid"], "orbits", r["orbits"],
              r["orbits_by_rank_x1"], "%.1f s" % r["seconds"], flush=True)
        with open(os.path.join(args.out_dir, "m74_%s.json" % name[10:]), "w") as f:
            json.dump(r, f, indent=1)
    g = grade(results)
    with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
        json.dump(g, f, indent=1)
    print("SUMMARY", json.dumps({k: v for k, v in g.items() if k != "checks"}), flush=True)
    print("SUMMARY checks %d of %d held" % (g["passed"], g["total"]), flush=True)


if __name__ == "__main__":
    main()
