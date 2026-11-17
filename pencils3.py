# SPDX-License-Identifier: Apache-2.0
"""pencils3.py - degree-2 Kakeya blocks of F_q^3 with two 'type (b)' structures
(note a165: Theorem 41, Proposition 49).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only, self-contained. Prime odd q only.

Setting (as in a164 / quad3.py). A point of F_q^3 is a tuple (x1, x2, x3); points(q)
lists them in itertools.product order, index(q, x) = x1 q^2 + x2 q + x3. A map P is a
list of q^3 tuples, P[i] = image of points(q)[i].

    Y_t = P(X) + t X,  X uniform on F_q^3,
    Lambda(P) = sum_t H(X | Y_t),   q^3 Lambda(P) = log2 score_int(q, P),
    score_int = prod_t prod_{fibres F of Y_t} |F|^|F|.
Conjecture C_q(3): score_int(q, P) <= 2^(3 (q-1) q^3).

A type-(b) structure (m, c, a, v, s) of P: m a nonzero linear form, m(c) != 0, and
    P(x) - P(0) - [ m(x) x + m(x)^2 a + m(x) v + s x ]  lies in F_q c  for every x.
Theorem 41 (a165): up to the Lambda-preserving moves, a degree-2 map with two type-(b)
structures whose kernels ker m1 != ker m2 is F_{rho,delta} below.
"""

import itertools
from collections import Counter


# ---------------------------------------------------------------- arithmetic

def points(q):
    return list(itertools.product(range(q), repeat=3))


def index(q, x):
    return (x[0] % q) * q * q + (x[1] % q) * q + (x[2] % q)


def dot(q, x, y):
    return sum(a * b for a, b in zip(x, y)) % q


def cross(q, x, y):
    return ((x[1] * y[2] - x[2] * y[1]) % q,
            (x[2] * y[0] - x[0] * y[2]) % q,
            (x[0] * y[1] - x[1] * y[0]) % q)


def rank(q, vecs):
    """Rank over F_q (q prime) of a list of equal-length vectors."""
    rows = [[c % q for c in v] for v in vecs]
    if not rows:
        return 0
    r = 0
    for col in range(len(rows[0])):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][col]:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][col], q - 2, q)
        rows[r] = [(v * inv) % q for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def directions(q):
    """Points of PG(2, q): nonzero vectors whose first nonzero coordinate is 1."""
    out = []
    for v in itertools.product(range(q), repeat=3):
        nz = [c for c in v if c]
        if nz and nz[0] == 1:
            out.append(v)
    return out


def tabulate(q, f):
    """List of f(x) mod q over points(q); f returns a 3-tuple of integers."""
    return [tuple(c % q for c in f(x)) for x in points(q)]


# ---------------------------------------------------------------- the family

def family(q, rho, delta):
    """F_{rho,delta}(x) =
        ( (2x1+x2)x3 - rho (x1+x2)^2 - 2x1^2 - 3x1x2 - x2^2 - delta (x1+x2),
          x1 (x1 + x2),
          x1 x3 ).
    Structures (Theorem 41): S1 = (m1, c1, a1, v1, s1) = (x1, e1, e2, 0, 0) and
    S2 = (m2, c2, a2, v2, s2) = (-(x1+x2), (1,0,1), (-1,1,rho), (delta,0,0), 0)."""
    def f(x):
        x1, x2, x3 = x
        p1 = ((2 * x1 + x2) * x3 - rho * (x1 + x2) ** 2 - 2 * x1 * x1 - 3 * x1 * x2
              - x2 * x2 - delta * (x1 + x2))
        return (p1, x1 * (x1 + x2), x1 * x3)
    return tabulate(q, f)


def half(q):
    return pow(2, q - 2, q)


def exceptional(q):
    """E = F_{-1/2, 0}. Its first coordinate is (2x1+x2)x3 - (3x1+x2)(x1+x2)/2."""
    return family(q, (-half(q)) % q, 0)


def structures(q, rho, delta):
    """The two type-(b) structures of F_{rho,delta}, as (m, c, a, v, s)."""
    s1 = ((1, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 0), 0)
    s2 = (((q - 1) % q, (q - 1) % q, 0), (1, 0, 1), ((q - 1) % q, 1, rho % q),
          (delta % q, 0, 0), 0)
    return s1, s2


def has_structure(q, P, st):
    """True iff P(x) - P(0) - [m(x) x + m(x)^2 a + m(x) v + s x] is in F_q c for all x,
    and m(c) != 0."""
    m, c, a, v, s = st
    if dot(q, m, c) == 0:
        return False
    pts = points(q)
    p0 = P[index(q, (0, 0, 0))]
    for i, x in enumerate(pts):
        mx = dot(q, m, x)
        r = tuple((P[i][j] - p0[j] - (mx * x[j] + mx * mx * a[j] + mx * v[j] + s * x[j])) % q
                  for j in range(3))
        if cross(q, r, c) != (0, 0, 0):
            return False
    return True


# ---------------------------------------------------------------- Lambda

def fibre_sizes(q, P, t):
    pts = points(q)
    return Counter(tuple((a + t * b) % q for a, b in zip(P[i], x))
                   for i, x in enumerate(pts)).values()


def score_int(q, P):
    """prod_t prod_F |F|^|F| = 2^(q^3 Lambda(P))."""
    s = 1
    for t in range(q):
        for m in fibre_sizes(q, P, t):
            s *= m ** m
    return s


def bound_int(q):
    return 2 ** (3 * (q - 1) * q ** 3)


def predicted_hist_E(q):
    """Proposition 49: for EVERY t, the fibres of E + tI are (q-1)^3/2 pairs,
    3(q-1) fibres of size q-1 and one fibre of size 3q-2."""
    h = Counter()
    h[2] += (q - 1) ** 3 // 2
    h[q - 1] += 3 * (q - 1)
    h[3 * q - 2] += 1
    return h


def predicted_score_E(q):
    """Proposition 49: score_int(E) =
    [2^((q-1)^3) (3q-2)^(3q-2) (q-1)^(3 (q-1)^2)]^q, i.e.
    Lambda(E) = [(q-1)^3 + (3q-2) log2(3q-2) + 3 (q-1)^2 log2(q-1)] / q^2."""
    per_t = 2 ** ((q - 1) ** 3) * (3 * q - 2) ** (3 * q - 2) * (q - 1) ** (3 * (q - 1) ** 2)
    return per_t ** q


def lam_E_float(q):
    import math
    return ((q - 1) ** 3 + (3 * q - 2) * math.log2(3 * q - 2)
            + 3 * (q - 1) ** 2 * math.log2(q - 1)) / q ** 2


# ---------------------------------------------------------------- directions

def val(q, P, x):
    return P[index(q, x)]


def beta(q, P, x, y):
    """Polar form of a degree-2 map: P(x+y) - P(x) - P(y) + P(0)."""
    s = tuple((a + b) % q for a, b in zip(x, y))
    a_, b_, c_, z_ = val(q, P, s), val(q, P, x), val(q, P, y), val(q, P, (0, 0, 0))
    return tuple((u - v - w + z) % q for u, v, w, z in zip(a_, b_, c_, z_))


def lin(q, P, w):
    """Linear part (q odd): L w = (P(w) - P(-w)) / 2."""
    a_, b_ = val(q, P, w), val(q, P, tuple((-c) % q for c in w))
    return tuple(((u - v) * half(q)) % q for u, v in zip(a_, b_))


def rank_data(q, P, w):
    """(r_w, active): r_w = rank of x -> beta(x, w) mod F_q w; active iff L w mod w is
    in its image (a164, Prop 47)."""
    cols = [beta(q, P, e, w) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    r1 = rank(q, cols + [w])
    r2 = rank(q, cols + [w, lin(q, P, w)])
    return r1 - 1, r2 == r1


def cylinder_set(q, P):
    """D = directions with r_w = 1 and active (a164)."""
    return set(w for w in directions(q) if rank_data(q, P, w) == (1, True))


def witness_set(q, P):
    """Directions w having a nonzero phi with phi(w) = 0 and phi o P constant along
    every line in direction w (brute force; Lemma 115 of a164)."""
    pts = points(q)
    dirs = directions(q)
    out = set()
    for w in dirs:
        for phi in dirs:
            if dot(q, phi, w):
                continue
            ok = True
            for i, x in enumerate(pts):
                y = tuple((a + b) % q for a, b in zip(x, w))
                if dot(q, phi, P[index(q, y)]) != dot(q, phi, P[i]):
                    ok = False
                    break
            if ok:
                out.add(w)
                break
    return out


def pi_w(q, P, w):
    """Pi_w = #{(x, lam) : lam != 0, P(x + lam w) - P(x) in F_q w} (brute force)."""
    pts = points(q)
    n = 0
    for i, x in enumerate(pts):
        px = P[i]
        for lam in range(1, q):
            y = tuple((a + lam * b) % q for a, b in zip(x, w))
            d = tuple((u - v) % q for u, v in zip(P[index(q, y)], px))
            if cross(q, d, w) == (0, 0, 0):
                n += 1
    return n


def predicted_D(q, exceptional_case):
    """Theorem 41: D = {w1 = 0} u {w1 + w2 = 0}, plus the line {w1 + w2 = 2 w3} for E."""
    out = set()
    for w in directions(q):
        if w[0] % q == 0 or (w[0] + w[1]) % q == 0:
            out.add(w)
        elif exceptional_case and (w[0] + w[1] - 2 * w[2]) % q == 0:
            out.add(w)
    return out


# ---------------------------------------------------------------- invariance

def invariant_lines(q, P):
    """Directions w with P(x + lam w) - P(x) in F_q w for all x, lam."""
    return [w for w in directions(q) if pi_w(q, P, w) == q ** 3 * (q - 1)]


def invariant_planes(q, P):
    """Normals n such that n.P(x) depends only on n.x."""
    pts = points(q)
    out = []
    for n in directions(q):
        seen = {}
        ok = True
        for i, x in enumerate(pts):
            if seen.setdefault(dot(q, n, x), dot(q, n, P[i])) != dot(q, n, P[i]):
                ok = False
                break
        if ok:
            out.append(n)
    return out


def theorem40_conditions(q, D, Z0):
    """(cond_b, cond_c) of a164 Theorem 40."""
    dirs = directions(q)
    cond_c = (q - 1) * len(D) <= (2 * q + 1) * (q - 1) + len(Z0)
    cond_b = any((q - 1) * sum(1 for w in D if dot(q, n, w))
                 <= sum(1 for w in Z0 if dot(q, n, w)) for n in dirs)
    return cond_b, cond_c


if __name__ == "__main__":
    for q in (3, 5, 7):
        E = exceptional(q)
        ok = score_int(q, E) == predicted_score_E(q)
        print(q, "Lambda(E) =", round(lam_E_float(q), 5), "bound", 3 * (q - 1),
              "formula ok" if ok else "FORMULA MISMATCH")
