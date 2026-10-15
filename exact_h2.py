"""Exact maximum of the fibre score S(P) over every map P : F_q^k -> F_q^k (q prime), by branch
and bound in pure Python (README section 9).

S(P) = sum over t in F_q and over the fibres of x -> P(x) + t x of s log2 s. A map with
S(P) > k (q - 1) q^k would give a Kakeya bound below q * 2^(-(q-1)/q) (Theorem 2).

Each x gives the progression P(x), P(x) + x, ..., P(x) + (q-1) x, whose point t lies in slice t.
The search fixes P(0) = 0 (P -> P + c does not change S), chooses P(x) for x = 1, 2, ... in turn,
and keeps the number of progressions through each point of each slice. Adding a point to a cell
that already holds c points raises S by D[c] = (c+1) log2(c+1) - c log2 c. D increases with c, so
r more progressions raise slice t by at most D[m] + D[m+1] + ... + D[m+r-1], where m is the largest
count in that slice; branches whose bound falls below the floor are cut.

  python exact_h2.py --q 3 --k 2          every map on F_3^2: maximum, count, one maximiser

By MV2 of Munim, Inc., 2026-10-15. Researched and written with AI agents working in MV2's name.
Code Apache-2.0.
"""
import argparse
import json
import math
import time
from itertools import product

EPS = 1e-9


def digits(q, k, v):
    """Coordinates of the vector coded by the integer v (base q, lowest digit first)."""
    return [(v // q ** i) % q for i in range(k)]


def number(q, ds):
    return sum(d * q ** i for i, d in enumerate(ds))


def tables(q, k):
    """add[u][v] and mul[t][v] on F_q^k for prime q, vectors coded as the integers 0..q^k - 1."""
    n = q ** k
    vs = [digits(q, k, v) for v in range(n)]
    add = [[number(q, [(a + b) % q for a, b in zip(vs[u], vs[v])]) for v in range(n)]
           for u in range(n)]
    mul = [[number(q, [(t * a) % q for a in vs[v]]) for v in range(n)] for t in range(q)]
    return add, mul


def xlog2x(c):
    return c * math.log2(c) if c > 1 else 0.0


def score(q, k, P):
    """S(P) straight from the definition, with coordinate arithmetic (independent of tables)."""
    total = 0.0
    for t in range(q):
        counts = {}
        for x in range(q ** k):
            y = tuple((p + t * d) % q for p, d in zip(digits(q, k, P[x]), digits(q, k, x)))
            counts[y] = counts.get(y, 0) + 1
        total += sum(xlog2x(c) for c in counts.values())
    return total


def threshold(q, k):
    """k (q - 1) q^k: S of k copies of an optimal one-coordinate map. Above it beats Theorem 1."""
    return k * (q - 1) * q ** k


def squares(q, k):
    """The coordinatewise squares P(x) = (x_1^2, ..., x_k^2) as a list of codes."""
    return [number(q, [d * d % q for d in digits(q, k, x)]) for x in range(q ** k)]


def brute_force(q, k, fixed=None):
    """(max S, number of maps at the max) over every P with P(0) = 0 that agrees with `fixed`."""
    n = q ** k
    fixed = dict(fixed or {})
    free = [x for x in range(1, n) if x not in fixed]
    best, count = -1.0, 0
    for values in product(range(n), repeat=len(free)):
        P = [0] * n
        for x, a in fixed.items():
            P[x] = a
        for x, a in zip(free, values):
            P[x] = a
        s = score(q, k, P)
        if s > best + EPS:
            best, count = s, 1
        elif s > best - EPS:
            count += 1
    return best, count


def search(q, k, floor, fixed=None):
    """Branch and bound over every P with P(0) = 0 that agrees with `fixed` (a dict x -> P(x)).

    Only maps with S >= floor are visited. Returns their maximum ("max_score", None if there are
    none), how many maps reach it, how many reach the floor, one maximiser, and the node count."""
    started = time.time()
    n = q ** k
    add, mul = tables(q, k)
    fixed = dict(fixed or {})
    steps = [x for x in range(1, n) if x not in fixed]
    # pts[x][a]: the q points a, a + x, ..., a + (q-1) x of the progression with start a and step x
    pts = [[tuple(add[a][mul[t][x]] for t in range(q)) for a in range(n)] for x in range(n)]
    D = [xlog2x(c + 1) - xlog2x(c) for c in range(2 * n + 1)]
    tail = [[sum(D[m + i] for i in range(r)) for r in range(n + 1)] for m in range(n + 1)]
    counts = [[0] * n for _ in range(q)]
    for t in range(q):
        counts[t][0] = 1  # x = 0 with P(0) = 0 puts the point 0 in every slice
    S0 = 0.0
    choice = [0] * n
    for x, a in fixed.items():
        choice[x] = a
        for t, p in enumerate(pts[x][a]):
            S0 += D[counts[t][p]]
            counts[t][p] += 1
    top = [max(row) for row in counts]
    limit = floor - EPS
    state = {"best": None, "at_best": 0, "above": 0, "example": None, "nodes": 0}

    def record(total, x_last, a_last):
        state["above"] += 1
        best = state["best"]
        if best is None or total > best + EPS:
            example = list(choice)
            example[x_last] = a_last
            state.update(best=total, at_best=1, example=example)
        elif total > best - EPS:
            state["at_best"] += 1

    def rec(i, S):
        state["nodes"] += 1
        r = len(steps) - i
        if S + sum(tail[top[t]][r] for t in range(q)) < limit:
            return
        x = steps[i]
        row = pts[x]
        if r == 1:
            for a in range(n):
                total = S
                for t, p in enumerate(row[a]):
                    total += D[counts[t][p]]
                if total >= limit:
                    record(total, x, a)
            return
        for a in range(n):
            saved = list(top)
            gain = 0.0
            for t, p in enumerate(row[a]):
                c = counts[t][p]
                gain += D[c]
                counts[t][p] = c + 1
                if c + 1 > top[t]:
                    top[t] = c + 1
            choice[x] = a
            rec(i + 1, S + gain)
            for t, p in enumerate(row[a]):
                counts[t][p] -= 1
            top[:] = saved

    if steps:
        rec(0, S0)
    elif S0 >= limit:
        record(S0, 0, 0)
    return {"q": q, "k": k, "normalisation": "P(0) = 0", "floor": floor,
            "threshold": threshold(q, k), "max_score": state["best"],
            "maps_at_max": state["at_best"], "maps_at_or_above_floor": state["above"],
            "example": state["example"], "nodes": state["nodes"],
            "seconds": round(time.time() - started, 2)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=3)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--floor", type=float, default=None, help="default: the threshold")
    args = ap.parse_args()
    floor = threshold(args.q, args.k) if args.floor is None else args.floor
    result = search(args.q, args.k, floor)
    if result["example"] is not None:
        P = result["example"]
        result["example"] = [[digits(args.q, args.k, x), digits(args.q, args.k, P[x])]
                             for x in range(args.q ** args.k)]
        result["score_rechecked"] = score(args.q, args.k, P)
    print(json.dumps(result, indent=1))


if __name__ == "__main__":
    main()
