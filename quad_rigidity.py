# SPDX-License-Identifier: Apache-2.0
"""quad_rigidity.py - degree-2 blocks never beat the Kakeya bound (note a163, Theorem 38).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only.

Fields: prime q (elements 0..q-1, arithmetic mod q) and q = 4, 8, 16 (elements are
bit vectors of polynomials over F_2 modulo x^2+x+1, x^3+x+1, x^4+x+1).

A point of F_q^2 is (x1, x2); points(q) lists them in lexicographic order, so the index
of (x1, x2) is x1 * q + x2. A map P of F_q^2 is a list of q^2 points: P[i] is the
image of points(q)[i].

    Y_t = P(X) + t X,  X uniform on F_q^2,
    Lambda(P) = sum_t H(X | Y_t) = q^-2 sum_t sum_{fibres F of Y_t} |F| log2 |F|.

Conjecture C_q(2): Lambda(P) <= 2 (q - 1). Theorem 38 (note a163) proves it, with
equality exactly for frame products, for every P whose coordinates are polynomials of
total degree <= 2 and every q >= 3. Everything here is exact integer arithmetic:
    Lambda(P) q^2 = log2 score_int(P),  score_int(P) = prod_t prod_F |F|^|F|.
"""

import itertools
from collections import Counter

IRRED = {4: (2, 0b111), 8: (3, 0b1011), 16: (4, 0b10011)}


def _gf2m_mul(a, b, m, mod):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if (a >> m) & 1:
            a ^= mod
    return r


class Field:
    """F_q with addition table A, multiplication table M, negation N and inverse I."""

    def __init__(self, q):
        self.q = q
        if q in IRRED:
            m, mod = IRRED[q]
            self.p = 2
            self.A = [[a ^ b for b in range(q)] for a in range(q)]
            self.M = [[_gf2m_mul(a, b, m, mod) for b in range(q)] for a in range(q)]
        elif q >= 2 and all(q % d for d in range(2, q)):
            self.p = q
            self.A = [[(a + b) % q for b in range(q)] for a in range(q)]
            self.M = [[(a * b) % q for b in range(q)] for a in range(q)]
        else:
            raise ValueError("q must be a prime or one of 4, 8, 16")
        self.N = [next(b for b in range(q) if self.A[a][b] == 0) for a in range(q)]
        self.I = [0] + [next(b for b in range(q) if self.M[a][b] == 1) for a in range(1, q)]

    def sub(self, a, b):
        return self.A[a][self.N[b]]

    def two(self):
        """The field element 2 (0 in characteristic 2)."""
        return self.A[1][1]


def points(q):
    return list(itertools.product(range(q), repeat=2))


def quad_map(F, c1, c2):
    """P(x) = (Q1(x), Q2(x)) with cj = (a, b, c, d, e) meaning
    a x1^2 + b x1 x2 + c x2^2 + d x1 + e x2 (constants never change Lambda)."""
    A, M = F.A, F.M
    out = []
    for x1, x2 in points(F.q):
        mons = (M[x1][x1], M[x1][x2], M[x2][x2], x1, x2)
        v = []
        for c in (c1, c2):
            s = 0
            for coef, mon in zip(c, mons):
                s = A[s][M[coef][mon]]
            v.append(s)
        out.append(tuple(v))
    return out


def conjugate(F, P, g):
    """x -> g P(g^-1 x) for g = ((g00, g01), (g10, g11)) invertible. Lambda is unchanged
    and the degree stays <= 2."""
    A, M, q = F.A, F.M, F.q
    det = F.sub(M[g[0][0]][g[1][1]], M[g[0][1]][g[1][0]])
    if det == 0:
        raise ValueError("singular")
    di = F.I[det]
    h = ((M[di][g[1][1]], M[di][F.N[g[0][1]]]), (M[di][F.N[g[1][0]]], M[di][g[0][0]]))

    def apply(m, x):
        return (A[M[m[0][0]][x[0]]][M[m[0][1]][x[1]]], A[M[m[1][0]][x[0]]][M[m[1][1]][x[1]]])

    out = []
    for x in points(q):
        y = apply(h, x)
        out.append(apply(g, P[y[0] * q + y[1]]))
    return out


# ---------------------------------------------------------------- Lambda, exactly

def fibre_sizes(F, P, t):
    A, M = F.A, F.M
    return Counter(
        (A[P[i][0]][M[t][x[0]]], A[P[i][1]][M[t][x[1]]]) for i, x in enumerate(points(F.q))
    ).values()


def score_int(F, P):
    """prod_t prod_F |F|^|F| = 2^(q^2 Lambda(P))."""
    s = 1
    for t in range(F.q):
        for n in fibre_sizes(F, P, t):
            s *= n ** n
    return s


def bound_int(F):
    return 2 ** (2 * (F.q - 1) * F.q * F.q)


def is_max(F, P):
    return score_int(F, P) == bound_int(F)


def exceeds(F, P):
    return score_int(F, P) > bound_int(F)


def oned_max(F, f):
    """Lambda(f) = q - 1 for f : F_q -> F_q (a list of q values), exactly."""
    A, M, q = F.A, F.M, F.q
    s = 1
    for t in range(q):
        for n in Counter(A[f[x]][M[t][x]] for x in range(q)).values():
            s *= n ** n
    return s == 2 ** ((q - 1) * q)


# ---------------------------------------------------------------- Lemma 114 (directions)

def directions(q):
    """Representatives of the q + 1 points of PG(1, q)."""
    return [(1, m) for m in range(q)] + [(0, 1)]


def pi_w(F, P, w):
    """Pi_w = #{(x, lam) : lam != 0, P(x + lam w) - P(x) in F_q w}."""
    A, M, q = F.A, F.M, F.q
    cnt = 0
    for x1, x2 in points(q):
        p = P[x1 * q + x2]
        for lam in range(1, q):
            y1 = A[x1][M[lam][w[0]]]
            y2 = A[x2][M[lam][w[1]]]
            r = P[y1 * q + y2]
            d0 = F.sub(r[0], p[0])
            d1 = F.sub(r[1], p[1])
            if M[d0][w[1]] == M[d1][w[0]]:
                cnt += 1
    return cnt


def full_directions(F, P):
    """Directions w with Pi_w = q^2 (q - 1): P respects the quotient by F_q w."""
    q = F.q
    return [w for w in directions(q) if pi_w(F, P, w) == q * q * (q - 1)]


def nonfull_cap(F):
    """Lemma 114: for a degree <= 2 map and a non-full direction w,
    Pi_w <= q (q - 1) if q is odd and Pi_w <= q^2 if q is even."""
    q = F.q
    return q * (q - 1) if F.p != 2 else q * q


# ---------------------------------------------------------------- frame products

def frame_of(F, P):
    """A frame (e1, e2, f, g) with P(x) = f(l1 x) e1 + g(l2 x) e2 and f, g 1D maximisers,
    or None. (l1, l2) is the dual basis of (e1, e2)."""
    q, M = F.q, F.M
    pts = points(q)
    for e1, e2 in itertools.combinations(directions(q), 2):
        det = F.sub(M[e1[0]][e2[1]], M[e2[0]][e1[1]])
        inv = F.I[det]
        f = [None] * q
        g = [None] * q
        ok = True
        for i, x in enumerate(pts):
            a = M[inv][F.sub(M[e2[1]][x[0]], M[e2[0]][x[1]])]
            b = M[inv][F.sub(M[e1[0]][x[1]], M[e1[1]][x[0]])]
            y = P[i]
            u = M[inv][F.sub(M[e2[1]][y[0]], M[e2[0]][y[1]])]
            v = M[inv][F.sub(M[e1[0]][y[1]], M[e1[1]][y[0]])]
            if f[a] is None:
                f[a] = u
            elif f[a] != u:
                ok = False
                break
            if g[b] is None:
                g[b] = v
            elif g[b] != v:
                ok = False
                break
        if ok and oned_max(F, f) and oned_max(F, g):
            return (e1, e2, tuple(f), tuple(g))
    return None


# ---------------------------------------------------------------- triangular family

def triangular(F, al, be, ga, de, ze, et, ep=0):
    """P = (al x1^2 + ga x1 x2 + de x2^2 + ep x1 + ze x2,  be x2^2 + et x2)."""
    return quad_map(F, (al, ga, de, ep, ze), (0, 0, be, 0, et))


def predicted_max(F, al, be, ga, de, ze, et):
    """Propositions 45 (odd q) and 46 (even q), with ep = 0: the triangular map is a
    maximiser iff al, be != 0 and it is the frame product in the basis
    (e1, e2 + kappa e1) of f(y) = al y^2 and g(y) = be y^2 + et y, i.e.
        de = al kappa^2 + kappa be,  ze = kappa et,
    with kappa = -ga / (2 al) when q is odd, and ga = 0 (kappa free) when q is even."""
    A, M = F.A, F.M
    if al == 0 or be == 0:
        return False

    def fits(k):
        return de == A[M[al][M[k][k]]][M[k][be]] and ze == M[k][et]

    if F.p != 2:
        kappa = M[F.N[ga]][F.I[M[F.two()][al]]]
        return fits(kappa)
    if ga != 0:
        return False
    return any(fits(k) for k in range(F.q))


def predicted_count(q):
    """Number of maximisers in the triangular family with ep = 0 (a163, Section 4)."""
    if q % 2 == 1:
        return q * q * (q - 1) ** 2
    return (q - 1) ** 2 * q * (2 * q - 1) // 2


if __name__ == "__main__":
    for q in (3, 4, 5):
        F = Field(q)
        n = 0
        for al, be, ga, de, ze, et in itertools.product(range(q), repeat=6):
            if is_max(F, triangular(F, al, be, ga, de, ze, et)):
                n += 1
        print("q", q, "triangular maximisers", n, "predicted", predicted_count(q))
