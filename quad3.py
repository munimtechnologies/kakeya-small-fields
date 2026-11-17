# SPDX-License-Identifier: Apache-2.0
"""quad3.py - degree-2 Kakeya blocks in dimension 3 (note a164: Theorem 39, Prop 47,
Theorem 40).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only. Prime q only (arithmetic mod q).

A point of F_q^3 is a tuple (x1, x2, x3); points(q) lists them in itertools.product
order, so index(q, x) = x1 q^2 + x2 q + x3. A map P of F_q^3 is a list of q^3 tuples:
P[i] is the image of points(q)[i].

    Y_t = P(X) + t X,  X uniform on F_q^3,
    Lambda(P) = sum_t H(X | Y_t) = q^-3 sum_t sum_{fibres F of Y_t} |F| log2 |F|.

Everything is exact integer arithmetic:
    q^3 Lambda(P) = log2 score_int(q, P),   score_int = prod_t prod_F |F|^|F|.
Conjecture C_q(3) is score_int(q, P) <= bound_int(q) = 2^(3 (q-1) q^3).
"""

import itertools
from collections import Counter

K = 3
E3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
MONS = ((0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2))  # x_i x_j, i <= j


def is_prime(q):
    return q >= 2 and all(q % d for d in range(2, q))


def points(q, k=K):
    return list(itertools.product(range(q), repeat=k))


def index(q, x):
    i = 0
    for c in x:
        i = i * q + c
    return i


def add(q, x, y):
    return tuple((a + b) % q for a, b in zip(x, y))


def sub(q, x, y):
    return tuple((a - b) % q for a, b in zip(x, y))


def smul(q, c, x):
    return tuple((c * a) % q for a in x)


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
    for c in range(len(rows[0])):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c]:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], q - 2, q)
        rows[r] = [(v * inv) % q for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


def directions(q, k=K):
    """Points of PG(k-1, q): nonzero vectors whose first nonzero coordinate is 1."""
    out = []
    for v in itertools.product(range(q), repeat=k):
        nz = [c for c in v if c]
        if nz and nz[0] == 1:
            out.append(v)
    return out


# ---------------------------------------------------------------- maps

def quad_map3(q, Qc, Lm):
    """P(x)_c = sum_m Qc[c][m] * mon_m(x) + sum_i Lm[c][i] x_i, monomials MONS."""
    out = []
    for x in points(q):
        mons = [x[i] * x[j] for i, j in MONS]
        v = []
        for c in range(K):
            s = sum(a * b for a, b in zip(Qc[c], mons))
            s += sum(Lm[c][i] * x[i] for i in range(K))
            v.append(s % q)
        out.append(tuple(v))
    return out


def matvec(q, A, x):
    return tuple(sum(A[r][c] * x[c] for c in range(K)) % q for r in range(K))


def conjugate(q, P, A):
    """P'(x) = A P(A^-1 x), A invertible. Lambda(P') = Lambda(P)."""
    if rank(q, A) != K:
        raise ValueError("A is singular")
    pts = points(q)
    out = [None] * len(pts)
    for i, x in enumerate(pts):
        out[index(q, matvec(q, A, x))] = matvec(q, A, P[i])
    return out


def frame3(q, a, b):
    """P(x) = (a0 x1^2 + b0 x1, a1 x2^2 + b1 x2, a2 x3^2 + b2 x3)."""
    return [tuple((a[i] * x[i] * x[i] + b[i] * x[i]) % q for i in range(K))
            for x in points(q)]


def type_b(q, psi, l1, lam, l21, l31):
    """The 'type (b)' family of a164, Section 4:
    P(x) = psi(x) e1 + (0, x1 x2, x1 x3) + L x, with
    L = [[l1[0], l1[1], l1[2]], [l21, lam, 0], [l31, 0, lam]].
    Every direction w with w1 = 0 lies on the cylinder locus Z."""
    Qc = [list(psi), [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]]
    Lm = [list(l1), [l21, lam, 0], [l31, 0, lam]]
    return quad_map3(q, Qc, Lm)


def veronese(q, a, b, c, d):
    """Q(x) = (x1^2, x1 x2, x2^2) and L = [[a, 2b, 0], [c, d, b], [0, 2c, e]] with
    e = 2d - a (so a - 2d + e = 0). Every direction (1, s, s^2) lies on Z."""
    e = (2 * d - a) % q
    Qc = [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0]]
    Lm = [[a, 2 * b % q, 0], [c, d, b], [0, 2 * c % q, e]]
    return quad_map3(q, Qc, Lm)


def upper_triangular(q, coeffs):
    """Coordinate c depends only on x_c, ..., x_3 (degree <= 2). Respects span(e1)
    and span(e1, e2). coeffs: 27 numbers (3 x (6 quadratic + 3 linear))."""
    Qc, Lm = [], []
    for c in range(K):
        qc = list(coeffs[9 * c: 9 * c + 6])
        lc = list(coeffs[9 * c + 6: 9 * c + 9])
        for m, (i, j) in enumerate(MONS):
            if i < c or j < c:
                qc[m] = 0
        for i in range(c):
            lc[i] = 0
        Qc.append(qc)
        Lm.append(lc)
    return quad_map3(q, Qc, Lm)


# ---------------------------------------------------------------- Lambda

def score_int(q, P):
    """prod_t prod_F |F|^|F| = 2^(q^3 Lambda(P))."""
    pts = points(q)
    s = 1
    for t in range(q):
        cnt = Counter(tuple((a + t * b) % q for a, b in zip(P[i], x))
                      for i, x in enumerate(pts))
        for m in cnt.values():
            s *= m ** m
    return s


def bound_int(q, k=K):
    """2^(k (q-1) q^k): the conjectured maximum of score_int (C_q(k))."""
    return 2 ** (k * (q - 1) * q ** k)


def lam_float(q, P):
    import math
    return math.log2(score_int(q, P)) / q ** K


# ---------------------------------------------------------------- pairs

def pi_w(q, P, w):
    """Pi_w = #{(x, lam) : lam != 0, P(x + lam w) - P(x) in F_q w} (brute force)."""
    pts = points(q)
    n = 0
    for i, x in enumerate(pts):
        px = P[i]
        for lam in range(1, q):
            y = add(q, x, smul(q, lam, w))
            if cross(q, sub(q, P[index(q, y)], px), w) == (0, 0, 0):
                n += 1
    return n


def all_pi(q, P):
    return {w: pi_w(q, P, w) for w in directions(q)}


# ---------------------------------------------------------------- Prop 47

def val(q, P, x):
    return P[index(q, x)]


def beta(q, P, x, y):
    """Polar form of a degree-2 map: P(x+y) - P(x) - P(y) + P(0)."""
    a, b, c, z = val(q, P, add(q, x, y)), val(q, P, x), val(q, P, y), val(q, P, (0, 0, 0))
    return tuple((a_ - b_ - c_ + z_) % q for a_, b_, c_, z_ in zip(a, b, c, z))


def lin(q, P, w):
    """Linear part of a degree-2 map (q odd): L w = (P(w) - P(-w)) / 2."""
    inv2 = pow(2, q - 2, q)
    a, b = val(q, P, w), val(q, P, smul(q, q - 1, w))
    return tuple(((a_ - b_) * inv2) % q for a_, b_ in zip(a, b))


def rank_data(q, P, w):
    """(r_w, active, z_rank): r_w = rank of x -> beta(x, w) mod F_q w; active iff
    L w mod w lies in its image; z_rank = rank of [M_w | w | L w]."""
    cols = [beta(q, P, e, w) for e in E3]
    r1 = rank(q, cols + [w])
    r2 = rank(q, cols + [w, lin(q, P, w)])
    return r1 - 1, r2 == r1, r2


def predicted_pi(q, P, w):
    """Proposition 47 (q odd, degree <= 2): Pi_w = (q-1) q^(3 - r_w) if w is active,
    else 0."""
    r, act, _ = rank_data(q, P, w)
    return (q - 1) * q ** (K - r) if act else 0


# ---------------------------------------------------------------- invariance

def invariant_lines(q, pis):
    """Directions w with P(x + lam w) - P(x) in F_q w for all x, lam."""
    return [w for w, v in pis.items() if v == q ** K * (q - 1)]


def invariant_planes(q, P):
    """Normals n such that P respects U = ker n: n.P(x) depends only on n.x."""
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


# ---------------------------------------------------------------- Theorem 39

def split_terms(q, P, n, pis):
    """Theorem 39 for the plane U = ker n. Returns (coset_scores, out_pairs):
    coset_scores[a] = 2^(q^2 Lambda_2(pi P_a)) for each coset x_a + U, where pi is the
    projection onto U along e_j (n_j != 0); out_pairs = sum of Pi_w over w not in U.
    Theorem 39: score_int(P) <= prod(coset_scores) * 2^out_pairs."""
    j = next(i for i in range(K) if n[i])
    invn = pow(n[j], q - 2, q)

    def proj(y):
        s = (dot(q, n, y) * invn) % q
        y = list(y)
        y[j] = (y[j] - s) % q
        return tuple(y)

    pts = points(q)
    cos = {}
    for i, x in enumerate(pts):
        cos.setdefault(dot(q, n, x), []).append(i)
    scores = []
    for a in sorted(cos):
        pairs = [(proj(P[i]), proj(pts[i])) for i in cos[a]]
        s = 1
        for t in range(q):
            cnt = Counter(tuple((u + t * v) % q for u, v in zip(pp, xx)) for pp, xx in pairs)
            for m in cnt.values():
                s *= m ** m
        scores.append(s)
    out_pairs = sum(v for w, v in pis.items() if dot(q, n, w))
    return scores, out_pairs


# ---------------------------------------------------------------- Theorem 40

def classify(q, P, pis=None):
    """Data for Theorem 40 (q odd, degree <= 2). Returns a dict with
    inv (P respects a nonzero proper subspace), D (cylinder directions: r_w = 1 and
    active), Z0 (directions with Pi_w = 0), cond_b, cond_c, residual."""
    if pis is None:
        pis = all_pi(q, P)
    dirs = directions(q)
    rd = {w: rank_data(q, P, w) for w in dirs}
    inv_l = invariant_lines(q, pis)
    inv_p = invariant_planes(q, P)
    D = [w for w in dirs if rd[w][0] == 1 and rd[w][1]]
    Z0 = [w for w in dirs if pis[w] == 0]
    cond_c = (q - 1) * len(D) <= (2 * q + 1) * (q - 1) + len(Z0)
    cond_b = any((q - 1) * sum(1 for w in D if dot(q, n, w))
                 <= sum(1 for w in Z0 if dot(q, n, w)) for n in dirs)
    inv = bool(inv_l or inv_p)
    return {"inv": inv, "inv_lines": inv_l, "inv_planes": inv_p, "D": D, "Z0": Z0,
            "cond_b": cond_b, "cond_c": cond_c,
            "residual": (not inv) and not (cond_b or cond_c), "rank_data": rd}
