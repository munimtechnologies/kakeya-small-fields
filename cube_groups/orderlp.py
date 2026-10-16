# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Best mixture of peeling orders for the commutator loss (draft for kakeya-small-fields 1.7).

Peeling the r-cube Y_t = A d_1^(t_1) ... d_r^(t_r) in the order sigma gives, in any finite group,

    sum_t H(Y_t) >= H(d) + sum_(i < r) 2^(r-i-1) H(d_(sigma_1), ..., d_(sigma_i)) - L(sigma) log|G'|,

where L(sigma) counts the lossy pairs (peeling j while some later index i > j is still present
with t_i = 1). Mixing orders with weights w, Shearer's lemma gives the abelian main term
((2^r - 1)/r) H(d) exactly when every index has coverage sum_sigma w_sigma (2^(r - pos) - 1) equal
to c_r = (2^r - 1 - r)/r. lam_r is the least average loss over such mixtures, an exact LP; then

    |K| >= |D|^((1 - 2^-r)/r) |G'|^(-lam_r / 2^r).

The uniform mixture gives l_r (13/6 for r = 3); by hand lam_3 = 2. This file solves the LP exactly
(two-phase simplex over Fractions, Bland's rule), certifies each optimum with a dual solution, and
checks the per-order inequality on random laws in small groups.

    python orderlp.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os
import random
import time
from fractions import Fraction


# ---------- the order LP ----------

def loss(sigma):
    """Number of lossy pairs when peeling in the order sigma (a permutation of 1..r)."""
    R = set(sigma)
    total = 0
    for j in sigma:
        lower = sum(1 for i in R if i < j)
        total += 2 ** (len(R) - 1) - 2 ** lower
        R.remove(j)
    return total


def coverage(sigma):
    """Shearer coverage of each index 1..r in the main term of the order sigma."""
    r = len(sigma)
    cov = [0] * r
    for pos, i in enumerate(sigma, 1):
        cov[i - 1] = 2 ** (r - pos) - 1
    return cov


def l_r(r):
    """Average loss of the uniform mixture (the run-32 formula)."""
    return 2 ** r - 1 - sum(Fraction(2 ** k - 1, k) for k in range(1, r + 1))


def gpk_lower(r):
    """Least |G'| exponent any such bound can have: G(p, k) needs a >= (r + 1) e_r - 1."""
    return Fraction(2 ** r - 1, 2 ** r) * Fraction(r + 1, r) - 1


def problem(r):
    orders = list(itertools.permutations(range(1, r + 1)))
    covs = [coverage(s) for s in orders]
    A = [[covs[k][i] for k in range(len(orders))] for i in range(r)]
    b = [Fraction(2 ** r - 1 - r, r)] * r
    c = [loss(s) for s in orders]
    return orders, A, b, c


def solve(M, v):
    """Exact solution of the square system M x = v, or None if M is singular."""
    n = len(M)
    M = [[Fraction(a) for a in row] + [Fraction(x)] for row, x in zip(M, v)]
    for col in range(n):
        piv = next((i for i in range(col, n) if M[i][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        p = M[col][col]
        M[col] = [a / p for a in M[col]]
        for i in range(n):
            f = M[i][col]
            if i != col and f != 0:
                M[i] = [a - f * q for a, q in zip(M[i], M[col])]
    return [M[i][n] for i in range(n)]


def simplex(A, b, c):
    """min c.x subject to A x = b, x >= 0, b >= 0, rows independent. Returns (value, x, basis)."""
    m, n = len(A), len(A[0])
    T = [[Fraction(v) for v in A[i]] + [Fraction(int(i == k)) for k in range(m)] + [Fraction(b[i])]
         for i in range(m)]
    basis = [n + i for i in range(m)]

    def pivot(r0, col, Z):
        p = T[r0][col]
        T[r0] = [v / p for v in T[r0]]
        prow = T[r0]
        for i in range(m):
            f = T[i][col]
            if i != r0 and f != 0:
                T[i] = [a - f * q for a, q in zip(T[i], prow)]
        f = Z[col]
        if f != 0:
            Z[:] = [a - f * q for a, q in zip(Z, prow)]
        basis[r0] = col

    def run(cost, allowed):
        Z = list(cost) + [Fraction(0)]
        for i in range(m):
            f = cost[basis[i]]
            if f != 0:
                Z = [a - f * q for a, q in zip(Z, T[i])]
        while True:
            enter = next((j for j in allowed if Z[j] < 0), None)
            if enter is None:
                return
            best = None
            for i in range(m):
                if T[i][enter] > 0:
                    key = (T[i][-1] / T[i][enter], basis[i])
                    if best is None or key < best[0]:
                        best = (key, i)
            if best is None:
                raise ValueError("unbounded")
            pivot(best[1], enter, Z)

    run([Fraction(0)] * n + [Fraction(1)] * m, range(n + m))
    if any(basis[i] >= n and T[i][-1] != 0 for i in range(m)):
        raise ValueError("infeasible")
    for i in range(m):
        if basis[i] >= n:
            j = next((j for j in range(n) if T[i][j] != 0), None)
            if j is None:
                raise ValueError("redundant constraint")
            pivot(i, j, [Fraction(0)] * (n + m + 1))
    run([Fraction(v) for v in c] + [Fraction(0)] * m, range(n))
    x = [Fraction(0)] * n
    for i, j in enumerate(basis):
        x[j] = T[i][-1]
    return sum(Fraction(cj) * xj for cj, xj in zip(c, x)), x, basis


def certify(A, b, c, x, basis):
    """Exact optimality certificate: x feasible, y dual feasible, c.x == b.y. Returns (value, y)."""
    m, n = len(A), len(A[0])
    if any(v < 0 for v in x):
        raise ValueError("x not nonnegative")
    if any(sum(A[i][j] * x[j] for j in range(n)) != b[i] for i in range(m)):
        raise ValueError("x not feasible")
    y = solve([[A[i][j] for i in range(m)] for j in basis], [c[j] for j in basis])
    if y is None:
        raise ValueError("singular basis")
    if any(sum(A[i][j] * y[i] for i in range(m)) > c[j] for j in range(n)):
        raise ValueError("y not dual feasible")
    value = sum(c[j] * x[j] for j in range(n))
    if value != sum(b[i] * y[i] for i in range(m)):
        raise ValueError("no strong duality")
    return value, y


def vertex_min(A, b, c):
    """Least cost over all basic feasible solutions (independent cross-check for small r)."""
    m, n = len(A), len(A[0])
    best = None
    for S in itertools.combinations(range(n), m):
        xs = solve([[A[i][j] for j in S] for i in range(m)], b)
        if xs is None or any(v < 0 for v in xs):
            continue
        v = sum(c[j] * xj for j, xj in zip(S, xs))
        if best is None or v < best:
            best = v
    return best


def lam(r):
    orders, A, b, c = problem(r)
    value, x, basis = simplex(A, b, c)
    value, y = certify(A, b, c, x, basis)
    support = {"".join(map(str, orders[j])): str(x[j]) for j in range(len(orders)) if x[j] != 0}
    return value, y, support


# ---------- entropy checks in small groups ----------

class Group:
    def __init__(self, name, elems, op):
        self.name = name
        self.el = list(elems)
        self.idx = {e: i for i, e in enumerate(self.el)}
        self.n = len(self.el)
        self.mul = [[self.idx[op(x, y)] for y in self.el] for x in self.el]
        self.e = next(i for i in range(self.n) if all(self.mul[i][j] == j for j in range(self.n)))
        self.inv = [next(j for j in range(self.n) if self.mul[i][j] == self.e) for i in range(self.n)]

    def derived_order(self):
        m, inv = self.mul, self.inv
        sub = {m[m[m[inv[a]][inv[b]]][a]][b] for a in range(self.n) for b in range(self.n)}
        sub.add(self.e)
        frontier = list(sub)
        while frontier:
            new = []
            for a in frontier:
                for b in list(sub):
                    for x in (m[a][b], m[b][a]):
                        if x not in sub:
                            sub.add(x)
                            new.append(x)
            frontier = new
        return len(sub)


def quaternion_op(x, y):
    # units 0..3 = 1, i, j, k; elements (sign, unit)
    table = {(0, 0): (1, 0), (0, 1): (1, 1), (0, 2): (1, 2), (0, 3): (1, 3),
             (1, 0): (1, 1), (1, 1): (-1, 0), (1, 2): (1, 3), (1, 3): (-1, 2),
             (2, 0): (1, 2), (2, 1): (-1, 3), (2, 2): (-1, 0), (2, 3): (1, 1),
             (3, 0): (1, 3), (3, 1): (1, 2), (3, 2): (-1, 1), (3, 3): (-1, 0)}
    s, u = table[(x[1], y[1])]
    return (x[0] * y[0] * s, u)


def small_groups():
    return [
        Group("Z2xZ4", [(a, b) for a in range(2) for b in range(4)],
              lambda x, y: ((x[0] + y[0]) % 2, (x[1] + y[1]) % 4)),
        Group("S3", list(itertools.permutations(range(3))),
              lambda x, y: tuple(x[y[i]] for i in range(3))),
        Group("D4", [(k, s) for s in range(2) for k in range(4)],
              lambda x, y: ((x[0] + (-1) ** x[1] * y[0]) % 4, (x[1] + y[1]) % 2)),
        Group("Q8", [(s, u) for s in (1, -1) for u in range(4)], quaternion_op),
    ]


def entropy(law, f):
    acc = {}
    for o, p in law:
        k = f(o)
        acc[k] = acc.get(k, 0.0) + p
    return -sum(p * math.log2(p) for p in acc.values() if p > 0)


def cube_point(G, o, t):
    w = o[0]
    for i, ti in enumerate(t, 1):
        if ti:
            w = G.mul[w][o[i]]
    return w


def cube_sum(G, law, r):
    return sum(entropy(law, lambda o, t=t: cube_point(G, o, t))
               for t in itertools.product((0, 1), repeat=r))


def main_term(law, sigma):
    r = len(sigma)
    s = entropy(law, lambda o: o[1:])
    for i in range(1, r):
        S = sorted(sigma[:i])
        s += 2 ** (r - i - 1) * entropy(law, lambda o, S=S: tuple(o[k] for k in S))
    return s


def random_law(G, r, rng, size):
    pts = [tuple(rng.randrange(G.n) for _ in range(r + 1)) for _ in range(size)]
    ws = [rng.random() + 1e-3 for _ in pts]
    s = sum(ws)
    return [(pt, w / s) for pt, w in zip(pts, ws)]


def order_slacks(G, law, r):
    """Least slack of the per-order inequality over all orders (>= 0 if the lemma holds)."""
    lg = math.log2(G.derived_order())
    lhs = cube_sum(G, law, r)
    return min(lhs - (main_term(law, s) - loss(s) * lg)
               for s in itertools.permutations(range(1, r + 1)))


MIX3 = {(3, 2, 1): Fraction(1, 3), (2, 1, 3): Fraction(1, 3), (1, 3, 2): Fraction(1, 3)}


def theorem_slack(G, law):
    """r = 3: sum_t H(Y_t) - ((7/3) H(d) - 2 log|G'|)."""
    return cube_sum(G, law, 3) - (7 / 3 * entropy(law, lambda o: o[1:])
                                  - 2 * math.log2(G.derived_order()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--max-r", type=int, default=7)
    ap.add_argument("--budget-seconds", type=float, default=1200)
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    out = {"lp": [], "vertex_check": {}, "entropy": [], "lemma_violations": []}

    def dump():
        with open(os.path.join(args.out_dir, "orderlp.json"), "w") as f:
            json.dump(out, f, indent=1)

    start = time.time()
    for r in range(2, args.max_r + 1):
        if time.time() - start > args.budget_seconds:
            print("r=%d skipped (time budget)" % r, flush=True)
            break
        t0 = time.time()
        value, y, support = lam(r)
        row = {"r": r, "lam": str(value), "lam_float": float(value),
               "exponent": str(value / 2 ** r), "uniform_l": str(l_r(r)),
               "uniform_exponent": str(l_r(r) / 2 ** r), "theorem9p_exponent": str(Fraction(2 ** r - 1, 2 ** r)),
               "gpk_lower_exponent": str(gpk_lower(r)), "consistent": value / 2 ** r >= gpk_lower(r),
               "dual_y": [str(v) for v in y], "support": support, "seconds": round(time.time() - t0, 2)}
        out["lp"].append(row)
        print("r=%d lam=%s exponent=%s (uniform %s, G(p,k) needs >= %s) consistent=%s support=%d %.1fs"
              % (r, value, value / 2 ** r, l_r(r) / 2 ** r, gpk_lower(r), row["consistent"],
                 len(support), row["seconds"]), flush=True)
        dump()
    for r in (3, 4):
        _, A, b, c = problem(r)
        v = vertex_min(A, b, c)
        out["vertex_check"][str(r)] = str(v)
        print("vertex enumeration r=%d: %s" % (r, v), flush=True)
    dump()
    rng = random.Random(20261016)
    for G in small_groups():
        for r in (2, 3):
            worst_order, worst_thm = None, None
            for trial in range(300):
                law = random_law(G, r, rng, rng.choice((1, 2, 4, 8, 16, 40)))
                s = order_slacks(G, law, r)
                if s < -1e-9:
                    out["lemma_violations"].append({"group": G.name, "r": r, "law": [[list(o), p] for o, p in law]})
                worst_order = s if worst_order is None else min(worst_order, s)
                if r == 3:
                    ts = theorem_slack(G, law)
                    worst_thm = ts if worst_thm is None else min(worst_thm, ts)
            out["entropy"].append({"group": G.name, "derived": G.derived_order(), "r": r,
                                   "least_order_slack": worst_order, "least_theorem_slack": worst_thm})
            print("entropy %s r=%d least per-order slack %.6f%s" % (
                G.name, r, worst_order, "" if worst_thm is None else " least r=3 theorem slack %.6f" % worst_thm),
                flush=True)
    dump()
    print("lemma violations:", len(out["lemma_violations"]))
    print("inconsistent r:", [row["r"] for row in out["lp"] if not row["consistent"]])


if __name__ == "__main__":
    main()
