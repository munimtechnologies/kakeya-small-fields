# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""A(7) <= 9 and A(8) <= 11 (notes/a7.md): the table of Corollary 33 and the settled cases of
Corollary 34.

The recursion of Proposition 24 (notes/rank-restriction.md), as in a6_bounds.bounds, started from
A(t) = t for t <= 5 (Theorems 26 and 27) and with A(t) <= upper[t] wherever an upper bound is known
by other means: here upper = {6: 7, 7: 9, 8: 11} (Theorems 28, 29 and 30). With upper = {6: 7} it
gives the table of Corollary 29 (a6_bounds). The count of Corollary 14 is a6_bounds.settled with
these bounds.

Pure Python, no dependencies.

Usage: python a7_bounds.py [--out-dir DIR]
"""
import argparse
import json
import os

import a6_bounds as a6

UPPER = {6: 7, 7: 9, 8: 11}


def bounds(tmax, upper=None):
    return a6.bounds(tmax, upper=UPPER if upper is None else upper)


def settled(a, b, upper=None):
    return a6.settled(a, b, upper=UPPER if upper is None else upper)


def reducible(t, A, E):
    """The largest term M(t - d) + A(d), 0 < d < t, with M(s) <= s + E(s)."""
    return max(t - d + E[t - d] + A[d] for d in range(1, t))


# The pairs that Theorem 29 (A(7) <= 9) and Theorem 30 (A(8) <= 11) add to Corollary 30.
NEW_BY_29 = {(10, 2), (13, 9)}
NEW_BY_30 = {(10, 3), (14, 11)}
EXTRA34 = a6.EXTRA30 | NEW_BY_29 | NEW_BY_30


def table():
    A, E = bounds(14)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    old = {(a, b): a6.settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    only_29 = {(a, b): settled(a, b, upper={6: 7, 7: 9}) for a in range(1, 15) for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "newly_settled": sorted(k for k in grid if grid[k] and not old[k]),
            "newly_settled_by_29_alone": sorted(k for k in only_29 if only_29[k] and not old[k]),
            "graded": {"a_bounds": A == [0, 1, 2, 3, 4, 5, 7, 9, 11, 14, 17, 20, 23, 26, 28],
                       "e_bounds": E == [0, 0, 0, 0, 0, 0, 1, 2, 3, 5, 7, 9, 11, 13, 14],
                       "corollary29_back": bounds(14, upper={6: 7}) == a6.bounds(14),
                       "corollary34": all(v == (b <= 1 or a <= max(9, b + 2) or (a, b) in EXTRA34)
                                          for (a, b), v in grid.items()),
                       "contains_corollary30": all(v for (a, b), v in grid.items() if old[(a, b)])}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="")
    args = ap.parse_args()
    text = json.dumps({"table": table()}, indent=1)
    print(text)
    if args.out_dir:
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "a7.json"), "w") as f:
            f.write(text)


if __name__ == "__main__":
    main()
