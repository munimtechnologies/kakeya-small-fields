# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""A(6) <= 7 (notes/a6.md): the table of Corollary 29 and the settled cases of Corollary 30.

The recursion of Proposition 24 (notes/rank-restriction.md), as in a5_bounds.bounds, started from
A(t) = t for t <= 5 (Theorems 26 and 27) and with A(t) <= upper[t] wherever an upper bound is known
by other means: here upper = {6: 7} (Theorem 28, jobs m18 and m19). With upper = {} it gives the
table of Corollary 26 (a5_bounds.bounds). The count of Corollary 14 is a5_bounds.settled with these
bounds.

Pure Python, no dependencies.

Usage: python a6_bounds.py [--out-dir DIR]
"""
import argparse
import json
import os

import a5_bounds as a5

UPPER = {6: 7}


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


EXTRA30 = a5.EXTRA27 | {(12, 7)}


def table():
    A, E = bounds(14)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    old = {(a, b): a5.settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "newly_settled": sorted(k for k in grid if grid[k] and not old[k]),
            "graded": {"a_bounds": A == [0, 1, 2, 3, 4, 5, 7, 10, 12, 14, 17, 21, 24, 26, 28],
                       "e_bounds": E == [0, 0, 0, 0, 0, 0, 1, 3, 4, 5, 7, 10, 12, 13, 14],
                       "corollary26_back": bounds(14, upper={}) == a5.bounds(14),
                       "corollary30": all(v == (b <= 1 or a <= max(9, b + 2) or (a, b) in EXTRA30)
                                          for (a, b), v in grid.items()),
                       "contains_corollary27": all(v for (a, b), v in grid.items() if old[(a, b)])}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="")
    args = ap.parse_args()
    text = json.dumps({"table": table()}, indent=1)
    print(text)
    if args.out_dir:
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "a6.json"), "w") as f:
            f.write(text)


if __name__ == "__main__":
    main()
