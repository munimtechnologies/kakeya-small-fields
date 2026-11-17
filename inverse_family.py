# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Theorem 36 (note a160): Lemma L_q(2) is false for every even q >= 4.

By MV2 of Munim, Inc., 2026-11-17. Researched and written with AI agents working in MV2's name.
No human mathematician has checked this.

Let q = 2^m, E = F_{q^2} viewed as F_q^2, s in E \\ F_q and

    P(x) = x^{-1} + s x        (with 0^{-1} = 0, i.e. x^{q^2 - 2}).

For t in F_q put u = s + t (never 0). Then Y_t = P(X) + tX = X^{-1} + uX is exactly 2-to-1:
its fibres are {x, 1/(u x)} (x != 0, x^2 != 1/u) and {0, u^{-1/2}}. Hence Lambda(P) = q.
For an F_q-line D through 0 let N_D be the number of (t, fibre) whose two points differ by an
element of D. Theorem 36 says

    N_D = q^2/2 - q            if D = F_q,
    N_D = q^2/2 - q/2 + 1      otherwise,

so for the functional l with kernel D, Lambda_l(P) = q - 2 N_D / q^2, and

    min_l Lambda_l(P) = q - 1 + (q - 2)/q^2  >  q - 1     (q >= 4).

This module builds E as F_q[y]/(y^2 + y + gamma), in exactly the vector encoding of lemma_l.py's
Space(q, 2) (x = c0 + c1 q means c0 + c1 y), so lemma_l's profile and chain bound apply as is.

    python inverse_family.py --q 4 8 16 --chain --out-dir out
"""
import argparse
import json
import os
import sys
from collections import Counter
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lemma_l as LL  # noqa: E402


class QuadExt:
    """F_{q^2} = F_q[y]/(y^2 + y + gamma), q = 2^m; c0 + c1 y is encoded as c0 + c1 q."""

    def __init__(self, q, gamma=None):
        F = LL.Field(q)
        if F.p != 2:
            raise ValueError("q must be a power of 2")
        self.F, self.q, self.N = F, q, q * q
        artin = {F.add[F.mul[z][z]][z] for z in range(q)}  # the values z^2 + z
        if gamma is None:
            gamma = min(g for g in range(q) if g not in artin)
        if gamma in artin:
            raise ValueError("y^2 + y + gamma is reducible over F_q")
        self.gamma = gamma

    def split(self, x):
        return x % self.q, x // self.q

    def join(self, c0, c1):
        return c0 + c1 * self.q

    def add(self, x, z):
        (a0, a1), (b0, b1) = self.split(x), self.split(z)
        A = self.F.add
        return self.join(A[a0][b0], A[a1][b1])

    def mul(self, x, z):
        (a0, a1), (b0, b1) = self.split(x), self.split(z)
        A, M = self.F.add, self.F.mul
        hi = M[a1][b1]                      # coefficient of y^2 = y + gamma
        c0 = A[M[a0][b0]][M[hi][self.gamma]]
        c1 = A[A[M[a0][b1]][M[a1][b0]]][hi]
        return self.join(c0, c1)

    def power(self, x, e):
        r, b = self.join(1, 0), x
        while e:
            if e & 1:
                r = self.mul(r, b)
            b = self.mul(b, b)
            e >>= 1
        return r

    def inv0(self, x):
        return self.power(x, self.N - 2)

    def in_subfield(self, x):
        return self.split(x)[1] == 0


def inverse_map(E, s):
    """P(x) = x^{-1} + s x as a list indexed by the encoded vector x."""
    if E.in_subfield(s):
        raise ValueError("s must lie outside F_q")
    return [E.add(E.inv0(x), E.mul(s, x)) for x in range(E.N)]


def fibre_sizes(sp, P):
    return [sorted(set(Counter(sp.ys(P, t)).values())) for t in range(sp.q)]


def same_l_pairs(sp, P):
    """For each projective functional (sp.funcs order): the number of (t, unordered pair {x, x'})
    with Y_t(x) = Y_t(x') and l(x) = l(x'). With all fibres of size 2 this is N_D for D = ker l."""
    out = []
    for L in sp.lval:
        n = 0
        for t in range(sp.q):
            for c in Counter(zip(sp.ys(P, t), L)).values():
                n += c * (c - 1) // 2
        out.append(n)
    return out


def predicted_same_pairs(q, func):
    """Theorem 36: N_D, where D = ker l. ker l = F_q (the vectors c0 + 0 y) iff l = [0, 1]."""
    return q * q // 2 - q if list(func) == [0, 1] else q * q // 2 - q // 2 + 1


def exact_lambda_l(q, n_same):
    """Lambda_l(P) for a map whose every Y_t is 2-to-1: (2/q^2)(q^3/2 - N_D)."""
    return Fraction(2, q * q) * (q ** 3 // 2 - n_same)


def report(q, gamma=None, s=None, chain=False):
    E = QuadExt(q, gamma)
    if s is None:
        s = E.join(0, 1)
    P = inverse_map(E, s)
    sp = LL.Space(q, 2)
    lam, lams = LL.profile(sp, P)
    same = same_l_pairs(sp, P)
    rep = {"q": q, "gamma": E.gamma, "s": s, "fibre_sizes": fibre_sizes(sp, P), "lambda": lam,
           "functionals": [list(f) for f in sp.funcs], "same_l_pairs": same,
           "predicted_same_l_pairs": [predicted_same_pairs(q, f) for f in sp.funcs],
           "lambda_l": lams, "min_lambda_l": min(lams),
           "min_lambda_l_exact": str(min(exact_lambda_l(q, n) for n in same)),
           "L_threshold": q - 1, "L_fails": min(lams) > q - 1 + LL.TOL}
    if chain:
        c, li, v = LL.best_chain(sp, P)
        rep.update({"best_chain": c, "best_chain_l": list(sp.funcs[li]), "best_chain_v": v,
                    "C_threshold": 2 * (q - 1), "L_prime_holds": c <= 2 * (q - 1) + LL.TOL})
    return rep


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, nargs="+", default=[4, 8, 16])
    ap.add_argument("--chain", action="store_true")
    ap.add_argument("--all-s", action="store_true", help="every s outside F_q (q <= 8)")
    ap.add_argument("--out-dir", default="out")
    a = ap.parse_args(argv)
    os.makedirs(a.out_dir, exist_ok=True)
    for q in a.q:
        if a.all_s:
            E = QuadExt(q)
            reps = [report(q, s=s, chain=a.chain) for s in range(E.N) if not E.in_subfield(s)]
        else:
            reps = [report(q, chain=a.chain)]
        LL.write_json(a.out_dir, f"inverse_family_q{q}{'_all' if a.all_s else ''}.json", reps)
        for r in reps:
            keys = ["q", "s", "lambda", "min_lambda_l", "min_lambda_l_exact", "L_fails",
                    "best_chain", "L_prime_holds"]
            print("SUMMARY " + json.dumps({k: r[k] for k in keys if k in r}), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
