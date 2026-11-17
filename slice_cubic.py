# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Theorem 37 and Lemma 111 (note a161): the slices of the inverse family are nodal cubics,
and the chain bound of Theorem 35 proves L'_q(2) for the whole family x^{-1} + s x.

By MV2 of Munim, Inc., 2026-11-17. Researched and written with AI agents working in MV2's name.
No human mathematician has checked this.

Setting (note a160): q = 2^m, E = F_{q^2} = F_q^2, P(x) = x^{-1} + s x with s outside F_q. For a
nonzero functional l with kernel D = F_q d and v with l(v) = 1, the slices of Theorem 35 are
Q_a(w) = pi(P(a v + w)) on D. Theorem 37 says:

  * a != 0: every fibre of w -> Q_a(w) + t w has at most 3 points, and the number T_a of
    3-point fibres (over all t) is the number of 3-subsets of a cyclic group of order q + 1,
    avoiding one element, with a fixed sum:  T_a = ((q - 2)^2 + 2 r - 6 eps) / 6, where
    eps = [conj(d) in F_q v] and r = #{x : 3x = c} is 1 if 3 does not divide q + 1, and
    otherwise 0 or 3 (and 3 when eps = 1). So Lambda(Q_a) = q - 1 - KAPPA T_a / q.
  * a = 0: Lambda(Q_0) = log2 q if v is in F_q d^{-1}, and q - 1 otherwise.

With v proportional to d^{-1} (possible iff D != F_q) the chain bound is
    q - 1 + (q-2)/q^2 + (log2 q + (q-1)(q - 1 - KAPPA T/q)) / q,
    T = ((q-2)^2 + 2 gcd(3, q+1) - 6)/6,
which is below 2(q - 1) for every even q >= 4 (47/8 at q = 4).

Lemma 111 (slack identity, any P on F_q^k): chain_bound(l, v) - Lambda(P)
    = sum_t H(l(Y_t) | pi_v(Y_t), l(X)).

    python slice_cubic.py --q 4 8 16 --out-dir out
"""
import argparse
import json
import math
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import inverse_family as IF  # noqa: E402
import lemma_l as LL  # noqa: E402

KAPPA = 6 - 3 * math.log2(3)   # 3 (2 - log2 3): the entropy deficit of one 3-point fibre


def conj(E, x):
    return E.power(x, E.q)


def kernel_dir(sp, li):
    """The first nonzero d with l(d) = 0 (D = F_q d)."""
    L = sp.lval[li]
    return next(x for x in range(1, sp.N) if L[x] == 0)


def proportional(sp, x, z):
    """True if x = c z for some c in F_q."""
    return any(sp.smul[c][z] == x for c in range(sp.q))


def eps_flag(E, sp, li, v):
    return 1 if proportional(sp, conj(E, kernel_dir(sp, li)), v) else 0


def inverse_v(E, sp, li):
    """The v in F_q d^{-1} with l(v) = 1, or None when l(d^{-1}) = 0 (i.e. D = F_q)."""
    L = sp.lval[li]
    z = E.inv0(kernel_dir(sp, li))
    if L[z] == 0:
        return None
    c = next(c for c in range(1, sp.q) if sp.F.mul[c][L[z]] == 1)
    return sp.smul[c][z]


def slice_stats(sp, P, li, v):
    """For each a in F_q: (Counter of fibre sizes over all t of w -> Q_a(w) + t w, Lambda(Q_a)).
    Same slices as lemma_l.chain_bound."""
    L = sp.lval[li]
    if L[v] != 1:
        raise ValueError("need l(v) = 1")
    q = sp.q
    W = [w for w in range(sp.N) if L[w] == 0]
    va, sm, vn = sp.vadd, sp.smul, sp.vneg

    def pi(x):
        return va[x][vn[sm[L[x]][v]]]

    out = []
    for a in range(q):
        base = sm[a][v]
        Q = {w: pi(P[va[base][w]]) for w in W}
        sizes = Counter()
        lam = 0.0
        for t in range(q):
            keys = [va[Q[w]][sm[t][w]] for w in W]
            for c in Counter(keys).values():
                sizes[c] += 1
            lam += LL.cond_ent(keys)
        out.append((sizes, lam))
    return out


def allowed_r(q, eps):
    if (q + 1) % 3:
        return [1]
    return [3] if eps else [0, 3]


def predicted_T(q, eps, r):
    num = (q - 2) ** 2 + 2 * r - 6 * eps
    if num % 6:
        raise ValueError("T is not an integer")
    return num // 6


def slice_lambda(q, T):
    return q - 1 - KAPPA * T / q


def theorem37_chain(q):
    """Chain bound at (l, v) with ker l = D != F_q and v in F_q d^{-1}."""
    T = predicted_T(q, 1, math.gcd(3, q + 1))
    return q - 1 + (q - 2) / q ** 2 + (math.log2(q) + (q - 1) * slice_lambda(q, T)) / q, T


def slack(sp, P, li, v):
    """Lemma 111: sum over t of H(l(Y_t) | pi_v(Y_t), l(X))."""
    L = sp.lval[li]
    va, sm, vn = sp.vadd, sp.smul, sp.vneg
    tot = 0.0
    for t in range(sp.q):
        Y = sp.ys(P, t)
        lY = [L[y] for y in Y]
        piY = [va[y][vn[sm[L[y]][v]]] for y in Y]
        tot += LL.cond_ent(list(zip(piY, L))) - LL.cond_ent(list(zip(lY, piY, L)))
    return tot


def report(q, s=None, v_limit=None):
    E = IF.QuadExt(q)
    if s is None:
        s = E.join(0, 1)
    P = IF.inverse_map(E, s)
    sp = LL.Space(q, 2)
    _, lams = LL.profile(sp, P)
    rows = []
    for li, L in enumerate(sp.lval):
        vs = [v for v in range(sp.N) if L[v] == 1]
        vi = inverse_v(E, sp, li)
        if v_limit is not None:
            vs = vs[:v_limit] + ([vi] if vi is not None and vi not in vs[:v_limit] else [])
        d = kernel_dir(sp, li)
        for v in vs:
            st = slice_stats(sp, P, li, v)
            eps = eps_flag(E, sp, li, v)
            T = [st[a][0].get(3, 0) for a in range(1, q)]
            rows.append({"l": list(sp.funcs[li]), "v": v, "eps": eps, "T": T,
                         "max_fibre": max(max(c) for c, _ in st[1:]),
                         "v_in_Fq_dinv": proportional(sp, E.inv0(d), v),
                         "lambda_Q0": st[0][1],
                         "chain": lams[li] + sum(lam for _, lam in st) / q})
    best = min(r["chain"] for r in rows)
    c37, T37 = theorem37_chain(q)
    return {"q": q, "s": s, "rows": rows, "best_chain_seen": best, "theorem37_chain": c37,
            "theorem37_T": T37, "C_threshold": 2 * (q - 1)}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, nargs="+", default=[4, 8, 16])
    ap.add_argument("--v-limit", type=int, default=None)
    ap.add_argument("--out-dir", default="out")
    a = ap.parse_args(argv)
    os.makedirs(a.out_dir, exist_ok=True)
    for q in a.q:
        rep = report(q, v_limit=a.v_limit if q > 8 else None)
        LL.write_json(a.out_dir, f"slice_cubic_q{q}.json", rep)
        keys = ["q", "best_chain_seen", "theorem37_chain", "theorem37_T", "C_threshold"]
        print("SUMMARY " + json.dumps({k: rep[k] for k in keys}), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
