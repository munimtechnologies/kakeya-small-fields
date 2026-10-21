# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""A(6) = 6 and A(9) <= 13 (notes/a23.md): the table of Corollary 49 and the settled cases of
Corollary 50.

The recursion of Proposition 24 (notes/rank-restriction.md), as in a6_bounds.bounds, started from
A(t) = t for t <= 5 (Theorems 26 and 27) and with A(t) <= upper[t] wherever an upper bound is known
by other means: here upper = {6: 6, 7: 9, 8: 11, 9: 13} (Theorems 31, 29, 30 and 32). The count is
the one of Corollary 14, as in a6_bounds.settled.

This file is self-contained (it repeats the 20 lines of a6_bounds.bounds and settled) so that its
tests run on their own. With --cross-check it also imports a7_bounds (and through it a6_bounds and
a5_bounds) from the same directory and checks that a7_bounds.bounds with the same upper bounds gives
the same table and the same settled pairs.

Pure Python, no dependencies.

Usage: python a23_bounds.py [--out-dir DIR] [--cross-check]
"""
import argparse
import json
import os

UPPER = {6: 6, 7: 9, 8: 11, 9: 13}
UPPER_31_ONLY = {6: 6, 7: 9, 8: 11}
UPPER_A7 = {6: 7, 7: 9, 8: 11}


def bounds(tmax, known=5, upper=None):
    """Upper bounds A[t] >= A(t) and E[t] >= M(t) - t for t = 0..tmax:
    A(t) <= min(2t, upper[t], max(t, t + A(t - 4), max over 0 < d < t of M(t - d) + A(d)))
    for t > known, with M(s) <= s + E(s) and E(s) = max over r <= s of (A(r) - r)."""
    upper = UPPER if upper is None else upper
    A, E = [0], [0]
    for t in range(1, max(tmax, known) + 1):
        if t <= known:
            A.append(t)
        else:
            red = max(t - d + E[t - d] + A[d] for d in range(1, t))
            A.append(min(2 * t, upper.get(t, 2 * t), max(t, t + A[t - 4], red)))
        E.append(max(E[t - 1], A[t] - t))
    return A[:tmax + 1], E[:tmax + 1]


def settled(a, b, upper=None):
    """The count of Corollary 14: tau = the largest t <= a with E[s] <= b for every s <= t; the
    pair (a, b) is settled if (a - tau - 2)(b - 1) <= 1."""
    if b <= 1:
        return True
    E = bounds(a, upper=upper)[1]
    tau = 0
    while tau < a and E[tau + 1] <= b:
        tau += 1
    return (a - tau - 2) * (b - 1) <= 1


def reducible(t, A, E):
    """The largest term M(t - d) + A(d), 0 < d < t, with M(s) <= s + E(s)."""
    return max(t - d + E[t - d] + A[d] for d in range(1, t))


# The extra pairs of Corollary 34 (a7_bounds.EXTRA34), and the two that Corollary 50 adds.
EXTRA34 = {(10, 2), (10, 3), (10, 4), (10, 5), (11, 5), (10, 6), (11, 6), (10, 7), (11, 7),
           (12, 7), (11, 8), (12, 8), (12, 9), (13, 9), (13, 10), (14, 11)}
NEW_BY_31 = {(12, 6)}
NEW_BY_32 = {(11, 4)}
EXTRA50 = EXTRA34 | NEW_BY_31 | NEW_BY_32


def table():
    A, E = bounds(14)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    old = {(a, b): settled(a, b, upper=UPPER_A7) for a in range(1, 15) for b in range(0, 13)}
    only_31 = {(a, b): settled(a, b, upper=UPPER_31_ONLY) for a in range(1, 15)
               for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "newly_settled": sorted(k for k in grid if grid[k] and not old[k]),
            "newly_settled_by_31_alone": sorted(k for k in only_31 if only_31[k] and not old[k]),
            "graded": {"a_bounds": A == [0, 1, 2, 3, 4, 5, 6, 9, 11, 13, 16, 20, 23, 26, 28],
                       "e_bounds": E == [0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 6, 9, 11, 13, 14],
                       "corollary33_back": bounds(14, upper=UPPER_A7) == (
                           [0, 1, 2, 3, 4, 5, 7, 9, 11, 14, 17, 20, 23, 26, 28],
                           [0, 0, 0, 0, 0, 0, 1, 2, 3, 5, 7, 9, 11, 13, 14]),
                       "corollary34_back": all(v == (b <= 1 or a <= max(9, b + 2)
                                                     or (a, b) in EXTRA34)
                                               for (a, b), v in old.items()),
                       "corollary50": all(v == (b <= 1 or a <= max(9, b + 2) or (a, b) in EXTRA50)
                                          for (a, b), v in grid.items()),
                       "contains_corollary34": all(v for (a, b), v in grid.items() if old[(a, b)])}}


def cross_check():
    """a7_bounds (fetched from the repository) with the same upper bounds gives the same answers."""
    import a7_bounds as a7
    same_table = a7.bounds(14, upper=UPPER) == bounds(14)
    same_old = a7.bounds(14) == bounds(14, upper=UPPER_A7)
    same_pairs = all(a7.settled(a, b, upper=UPPER) == settled(a, b)
                     for a in range(1, 15) for b in range(0, 13))
    # a7.EXTRA34 is built from older sets that may also list pairs with a <= max(9, b + 2); compare
    # only the pairs outside that region, inside the grid a <= 14, b <= 12.
    extra = {(a, b) for (a, b) in a7.EXTRA34
             if a <= 14 and 2 <= b <= 12 and a > max(9, b + 2)}
    return {"same_table": same_table, "same_corollary33": same_old, "same_pairs": same_pairs,
            "same_extra34": extra == EXTRA34}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="")
    ap.add_argument("--cross-check", action="store_true")
    args = ap.parse_args()
    out = {"table": table()}
    if args.cross_check:
        out["cross_check"] = cross_check()
    text = json.dumps(out, indent=1)
    print(text)
    if args.out_dir:
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "a23.json"), "w") as f:
            f.write(text)
    ok = all(out["table"]["graded"].values()) and all(out.get("cross_check", {}).values())
    print("SUMMARY a23_bounds all_match", ok)


if __name__ == "__main__":
    main()
