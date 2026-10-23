# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Which bound next (notes/a83.md): the pairs each candidate bound would settle, and the
configurations of an element of the largest rank that a counterexample at (t, dim V) would need.

newly_settled(upper) runs the count of Corollary 120 (a80_bounds.settled) with a candidate bound
added to a80_bounds.UPPER and lists the pairs (a, b), a <= 15, b <= 12, that it settles and the
current bounds do not.

reduction(t, n) is the counting part of Proposition 29 (notes/a24.md), written for any (t, n):
alpha(V) must be irreducible (Lemma 27(c): n > M(t - d) + A(d) for 0 < d < t, with
M(s) <= s + E(s)), some element has rank >= 3 when n > t (Lemmas 28 and 29), and an element of
rank s needs n <= t + A(t - s - 1) (Lemma 30). For an element u of the largest rank rho, with
k = t - rho, it lists the pairs (x0 in P or not, dim P) that Lemma 30 (dim U+ <= 1 + A(k - 1)) and
Corollary 38 (c = t - dim P >= ceil((t + 1 - 2 rho) / 2) when x0 is in P) leave, as
(kind, dim P, dim U+) with kind "A" if x0 is in P and "B" if not. Upper bounds for A are used
throughout, so the list can only be too long, never too short. In the tight case
n = t + k - 1 it gives back Cases A and B of Proposition 26, with Case A only when 2 rho >= t + 1.
It is a count, not a proof: each configuration still has to be ruled out.

Pure Python; imports a80_bounds.py only.

Usage: python a83_targets.py
"""
import json

import a80_bounds as ab

TARGETS = {"A(7) = 7": {7: 7}, "A(8) <= 10": {8: 10}, "A(9) <= 12": {9: 12}}


def newly_settled(upper, amax=15, bmax=12):
    """Pairs settled with the bounds upper (on top of a80_bounds.UPPER) and not without them."""
    up = {**ab.UPPER, **upper}
    return sorted((a, b) for a in range(1, amax + 1) for b in range(0, bmax + 1)
                  if ab.settled(a, b, upper=up) and not ab.settled(a, b))


def ranks(t, n, A):
    """The ranks 3 <= s <= t - 2 that Lemma 30 allows (rank t - 1 gives n <= t)."""
    return [s for s in range(3, t - 1) if n <= t + A[t - s - 1]]


def configs(t, n, A, rho):
    """(kind, dim P, dim U+) for an element of the largest rank rho."""
    k = t - rho
    cap = 1 + A[k - 1]
    c0 = max(0, -((2 * rho - t - 1) // 2))
    out = []
    for p in range(1, t + 1):
        if p <= t - c0 and n - p + 1 <= cap:
            out.append(("A", p, n - p + 1))
        if p <= t - 1 and n - p <= cap:
            out.append(("B", p, n - p))
    return sorted(out)


def reduction(t, n):
    """{rho: configurations} for a counterexample with dim V = n at t, or None if Lemma 27(c) or
    Lemmas 28 and 29 already rule n out."""
    A, E = ab.bounds(t)
    if n <= t or n <= ab.reducible(t, A, E):
        return None
    return {rho: configs(t, n, A, rho) for rho in ranks(t, n, A)}


def main():
    out = {"targets": {name: newly_settled(up) for name, up in TARGETS.items()},
           "reductions": {f"{t},{n}": reduction(t, n)
                          for t, n in ((6, 7), (7, 9), (7, 8), (8, 11), (9, 13))}}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
