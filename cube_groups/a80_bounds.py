# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""A(7) <= 8 (notes/a80.md, Theorem 33): the table of Corollary 119 and the settled cases of
Corollary 120.

The recursion of Proposition 24 (notes/rank-restriction.md), as in a23_bounds.bounds, started from
A(t) = t for t <= 5 (Theorems 26 and 27) and with A(t) <= upper[t] wherever an upper bound is known
by other means: here upper = {6: 6, 7: 8, 8: 11, 9: 13} (Theorems 31, 33, 30 and 32). The count is
the one of Corollary 14, as in a23_bounds.settled.

This file is self-contained (it repeats the 20 lines of a23_bounds.bounds and settled) so that its
tests run on their own. UPPER_A23 gives back the table of Corollary 49 and the pairs of Corollary 50.

Pure Python, no dependencies.

Usage: python a80_bounds.py [--out-dir DIR]
"""
import argparse
import json
import os

UPPER = {6: 6, 7: 8, 8: 11, 9: 13}
UPPER_A23 = {6: 6, 7: 9, 8: 11, 9: 13}


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


# The extra pairs of Corollary 50 (a23_bounds.EXTRA50), and the one that Corollary 120 adds.
EXTRA50 = {(10, 2), (10, 3), (10, 4), (11, 4), (10, 5), (11, 5), (10, 6), (11, 6), (12, 6),
           (10, 7), (11, 7), (12, 7), (11, 8), (12, 8), (12, 9), (13, 9), (13, 10), (14, 11)}
NEW_BY_33 = {(13, 8)}
EXTRA120 = EXTRA50 | NEW_BY_33


def table():
    A, E = bounds(14)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    old = {(a, b): settled(a, b, upper=UPPER_A23) for a in range(1, 15) for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "newly_settled": sorted(k for k in grid if grid[k] and not old[k]),
            "graded": {"a_bounds": A == [0, 1, 2, 3, 4, 5, 6, 8, 11, 13, 16, 19, 23, 26, 28],
                       "e_bounds": E == [0, 0, 0, 0, 0, 0, 0, 1, 3, 4, 6, 8, 11, 13, 14],
                       "corollary49_back": bounds(14, upper=UPPER_A23) == (
                           [0, 1, 2, 3, 4, 5, 6, 9, 11, 13, 16, 20, 23, 26, 28],
                           [0, 0, 0, 0, 0, 0, 0, 2, 3, 4, 6, 9, 11, 13, 14]),
                       "corollary50_back": all(v == (b <= 1 or a <= max(9, b + 2)
                                                     or (a, b) in EXTRA50)
                                               for (a, b), v in old.items()),
                       "corollary120": all(v == (b <= 1 or a <= max(9, b + 2)
                                                 or (a, b) in EXTRA120)
                                           for (a, b), v in grid.items()),
                       "contains_corollary50": all(v for (a, b), v in grid.items() if old[(a, b)])}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="")
    args = ap.parse_args()
    out = {"table": table()}
    text = json.dumps(out, indent=1)
    print(text)
    if args.out_dir:
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "a80.json"), "w") as f:
            f.write(text)
    print("SUMMARY a80_bounds all_match", all(out["table"]["graded"].values()))


if __name__ == "__main__":
    main()
