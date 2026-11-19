# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Note a181: sums-differences in characteristic 3 and the Kakeya constant of F_3.

A configuration in F_3^N is a probability law mu on directions d in F_3^N together
with a base point P(d) for every direction. Its three slices are
Y_t = P(D) + t D (t in F_3), D ~ mu. With X = Y_1, Y = Y_0 one has
X - Y = D, X + Y = -Y_2, so this is exactly the injective sums-differences problem
in F_3^N (X - Y determines (X, Y)).

Ruzsa's example is the map d -> d^2 on F_3 with uniform mu; its product rho^n has
H(D) / H(Y_t) = R0 = log 27 / log(27/4) = 1.7259824... for every t.

Theorem 69 (notes/a181.md): rho^n is a strict local maximum of
H(D) / avg_t H(Y_t) (and of H(D) / max_t H(Y_t)) among all configurations in
F_3^N, for every N >= n. Over the integers the same example is not a local maximum
(Proposition 76, z_config below).

This module checks the exact ingredients:
  Lemma 144 (frame bound)       frame_quantities, gram_lambda_max
  Lemma 145 (first-order cancel) slice_product
  Lemma 146 (one join)          max_joins
  Lemma 147 (Lemm collapses)    lemm4_collapses
  Proposition 76 (integers)     z_config, z_ratio
Standard library only; self-contained.
"""

import itertools
import math
from fractions import Fraction

LOG3 = math.log(3.0)
R0 = math.log(27.0) / math.log(27.0 / 4.0)      # Ruzsa's ratio
H_STAR = math.log(27.0 / 4.0) / 3.0              # h(1/3) in nats
KAPPA = 2.0 * R0 / 3.0 - 1.0                      # 0.15065..., the one-join margin


def entropy(weights):
    """Shannon entropy in nats of the law proportional to the given weights."""
    vals = list(weights.values()) if isinstance(weights, dict) else list(weights)
    tot = float(sum(vals))
    return -sum((float(v) / tot) * math.log(float(v) / tot) for v in vals if v > 0)


def f3_vectors(k):
    return list(itertools.product(range(3), repeat=k))


def vadd(a, b):
    return tuple((x + y) % 3 for x, y in zip(a, b))


def vscale(t, a):
    return tuple((t * x) % 3 for x in a)


def slice_value(base, d, t):
    return vadd(base, vscale(t, d))


def ruzsa_product(n):
    """rho^n: direction -> (base point d o d, weight 3^-n), exact weights."""
    w = Fraction(1, 3 ** n)
    return {d: (tuple((x * x) % 3 for x in d), w) for d in f3_vectors(n)}


def embed(config, extra):
    """Embed a configuration of F_3^n into F_3^(n+extra) (zeros appended)."""
    z = (0,) * extra
    return {d + z: (b + z, w) for d, (b, w) in config.items()}


def slice_laws(config):
    laws = [dict(), dict(), dict()]
    for d, (b, w) in config.items():
        for t in range(3):
            y = slice_value(b, d, t)
            laws[t][y] = laws[t].get(y, 0) + w
    return laws


def ratios(config):
    """(H(D), [H(Y_0), H(Y_1), H(Y_2)], R_avg, R_max), entropies in nats."""
    hd = entropy([w for (_, w) in config.values()])
    hs = [entropy(law) for law in slice_laws(config)]
    return hd, hs, hd / (sum(hs) / 3.0), hd / max(hs)


def slice_product(config, d):
    """prod_t P(Y_t = Y_t(d)) as an exact Fraction (weights must be Fractions)."""
    laws = slice_laws(config)
    tot = sum(w for (_, w) in config.values())
    b = config[d][0]
    out = Fraction(1)
    for t in range(3):
        out *= Fraction(laws[t][slice_value(b, d, t)]) / tot
    return out


def frame_quantities(n, f):
    """For f: F_3^n -> Q with mean 0 under the uniform law, return
    (E[f^2], sum_t E[E[f | Y_t]^2]) exactly, Y_t the slices of rho^n."""
    dirs = f3_vectors(n)
    size = len(dirs)
    ef2 = sum(Fraction(f[d]) ** 2 for d in dirs) / size
    conf = ruzsa_product(n)
    total = Fraction(0)
    for t in range(3):
        fib = {}
        for d in dirs:
            y = slice_value(conf[d][0], d, t)
            s, c = fib.get(y, (Fraction(0), 0))
            fib[y] = (s + Fraction(f[d]), c + 1)
        total += sum(s * s / c for (s, c) in fib.values()) / size
    return ef2, total


def gram_lambda_max(s):
    """Largest eigenvalue of the Gram matrix of u_0^(x)s, u_1^(x)s, u_2^(x)s
    (three unit vectors at 120 degrees, tensored s times): max(1 + 2a, 1 - a), a = (-1/2)^s."""
    a = Fraction(-1, 2) ** s
    return max(1 + 2 * a, 1 - a)


def max_joins(n, big_n):
    """Max over directions d outside F_3^n x 0 and base points b in F_3^N of the number
    of t in F_3 with b + t d in F_3^n x 0 (where every slice value of rho^n lies)."""
    best = 0
    for d in f3_vectors(big_n):
        if all(x == 0 for x in d[n:]):
            continue
        for b in f3_vectors(big_n):
            k = sum(1 for t in range(3)
                    if all(x == 0 for x in slice_value(b, d, t)[n:]))
            best = max(best, k)
    return best


def lemm4_collapses(m):
    """Lemm's four-point pattern in (F_3^m)^2, p1 at the origin (translation is harmless):
    X: p2~p3; Y: p1~p3, p2~p4; S = X+Y: p1~p2, p3~p4. Returns (number of realisations,
    whether every one has D(p1) = D(p4))."""
    pts = [(x, y) for x in f3_vectors(m) for y in f3_vectors(m)]
    zero = (0,) * m
    count = 0
    allsame = True
    p1 = (zero, zero)
    for p2 in pts:
        if vadd(p2[0], p2[1]) != zero:            # S: p1 ~ p2
            continue
        for p3 in pts:
            if p3[0] != p2[0] or p3[1] != zero:   # X: p2 ~ p3; Y: p1 ~ p3
                continue
            for p4 in pts:
                if p4[1] != p2[1]:                # Y: p2 ~ p4
                    continue
                if vadd(p4[0], p4[1]) != vadd(p3[0], p3[1]):   # S: p3 ~ p4
                    continue
                count += 1
                d1 = tuple((a - b) % 3 for a, b in zip(*p1))
                d4 = tuple((a - b) % 3 for a, b in zip(*p4))
                if d1 != d4:
                    allsame = False
    return count, allsame


def z_config(eps):
    """Ruzsa's triangle in Z^2 (mass (1-eps)/3 each) plus (2,0), (0,2) with mass eps/2 each."""
    a = (1.0 - eps) / 3.0
    pts = {(0, 1): a, (1, 0): a, (1, 1): a}
    if eps > 0:
        pts[(2, 0)] = eps / 2.0
        pts[(0, 2)] = eps / 2.0
    return pts


def _law(pts, fn):
    out = {}
    for p, w in pts.items():
        k = fn(p)
        out[k] = out.get(k, 0.0) + w
    return out


def z_ratio(pts):
    """H(X-Y) / max(H(X), H(Y), H(X+Y)) for a law on Z^2 with X-Y injective."""
    dl = _law(pts, lambda p: p[0] - p[1])
    if len(dl) != len(pts):
        raise ValueError("X - Y is not injective")
    hx = entropy(_law(pts, lambda p: p[0]))
    hy = entropy(_law(pts, lambda p: p[1]))
    hs = entropy(_law(pts, lambda p: p[0] + p[1]))
    return entropy(dl) / max(hx, hy, hs)


def z_joins(p, base):
    """Number of the forms X, Y, X+Y in which point p shares a value with some point of base."""
    forms = (lambda q: q[0], lambda q: q[1], lambda q: q[0] + q[1])
    return sum(1 for f in forms if any(f(p) == f(q) for q in base))


if __name__ == "__main__":
    print("R0 =", R0, " (27/4)^(1/3) =", (27.0 / 4.0) ** (1.0 / 3.0))
    print("max joins (1,2):", max_joins(1, 2), " (2,3):", max_joins(2, 3))
    print("Z ratio at eps=1e-4:", z_ratio(z_config(1e-4)))
