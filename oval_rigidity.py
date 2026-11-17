# SPDX-License-Identifier: Apache-2.0
"""oval_rigidity.py - equality cases of the Kakeya block conjecture (note a162).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0.

Only prime fields q (2, 3, 5, 7, ...) are used here: field elements are 0..q-1 and
arithmetic is mod q. A point of F_q^k is a tuple; points are listed in lexicographic
order by points(q, k). A map P of F_q^k is a list of q^k points: P[i] is the image of
points(q, k)[i].

Definitions (as in notes a159-a161):
    Y_t = P(X) + t X, X uniform on F_q^k,
    Lambda(P) = sum_t H(X | Y_t) = q^(-k) * sum_t sum_{fibres F of Y_t} |F| log2 |F|.
C_q(k) says Lambda(P) <= k (q - 1). Equality is decided exactly in integers:
    Lambda(P) = k (q - 1)  <=>  prod_t prod_F |F|^|F| = 2^(k (q - 1) q^k).
"""

import itertools
import math
from collections import Counter


def points(q, k):
    return list(itertools.product(range(q), repeat=k))


def lift1(f):
    """A function F_q -> F_q given as a list of q values, as a map of F_q^1."""
    return [(v % len(f),) for v in f]


def fibre_sizes(P, q, k, t):
    pts = points(q, k)
    c = Counter(
        tuple((P[i][j] + t * pts[i][j]) % q for j in range(k)) for i in range(len(pts))
    )
    return list(c.values())


def score_int(P, q, k):
    """prod over t and fibres of |F|^|F| (an exact integer)."""
    prod = 1
    for t in range(q):
        for n in fibre_sizes(P, q, k, t):
            prod *= n ** n
    return prod


def loss(P, q, k):
    """Lambda(P) in bits (float)."""
    s = 0.0
    for t in range(q):
        for n in fibre_sizes(P, q, k, t):
            if n > 1:
                s += n * math.log2(n)
    return s / q ** k


def is_max(P, q, k):
    """Exact test of Lambda(P) == k (q - 1)."""
    return score_int(P, q, k) == 2 ** (k * (q - 1) * q ** k)


def exceeds(P, q, k):
    """Exact test of Lambda(P) > k (q - 1), i.e. a counterexample to C_q(k)."""
    return score_int(P, q, k) > 2 ** (k * (q - 1) * q ** k)


# ---------------------------------------------------------------- Lemma 112 (pointwise form)

def parallel(w, u, q):
    """True iff w lies in F_q u (u != 0)."""
    return any(all((w[j] - c * u[j]) % q == 0 for j in range(len(u))) for c in range(q))


def pointwise(P, q, k):
    """For every x: (phi(x), sum_t (z_t(x) - 1), N(x)), where z_t(x) is the size of the
    fibre of Y_t through x, phi(x) = sum_t log2 z_t(x), and
    N(x) = #{u != 0 : P(x + u) - P(x) in F_q u}."""
    pts = points(q, k)
    index = {p: i for i, p in enumerate(pts)}
    out = []
    for i, x in enumerate(pts):
        phi = 0.0
        excess = 0
        for t in range(q):
            yx = tuple((P[i][j] + t * x[j]) % q for j in range(k))
            z = sum(
                1
                for m, y in enumerate(pts)
                if tuple((P[m][j] + t * y[j]) % q for j in range(k)) == yx
            )
            phi += math.log2(z)
            excess += z - 1
        n = 0
        for u in pts:
            if all(c == 0 for c in u):
                continue
            xu = tuple((x[j] + u[j]) % q for j in range(k))
            d = tuple((P[index[xu]][j] - P[i][j]) % q for j in range(k))
            if parallel(d, u, q):
                n += 1
        out.append((phi, excess, n))
    return out


# ---------------------------------------------------------------- Proposition 42 (ovals)

def is_arc_graph(f, q):
    """True iff no three points (x, f(x)) of the graph of f are collinear (q prime)."""
    for a, b, c in itertools.combinations(range(q), 3):
        if ((f[b] - f[a]) * (c - a) - (f[c] - f[a]) * (b - a)) % q == 0:
            return False
    return True


def maps_1d_fixed0(q):
    """Every f : F_q -> F_q with f(0) = 0, as a tuple of q values."""
    for rest in itertools.product(range(q), repeat=q - 1):
        yield (0,) + rest


def quadratics_fixed0(q):
    """{a y^2 + b y : a != 0} as tuples of values (q odd: the 1D maximisers with f(0) = 0)."""
    return {
        tuple((a * y * y + b * y) % q for y in range(q))
        for a in range(1, q)
        for b in range(q)
    }


# ---------------------------------------------------------------- frame products (k = 2)

def directions(q):
    """Representatives of the q + 1 points of PG(1, q)."""
    return [(1, m) for m in range(q)] + [(0, 1)]


def frame_products(q, oned):
    """Every map x -> f(l1(x)) e1 + g(l2(x)) e2 with {F_q e1, F_q e2} an unordered pair of
    distinct lines, (l1, l2) the dual basis of (e1, e2), and f, g in oned.
    Returns a dict: map (tuple of points) -> (e1, e2, f, g)."""
    pts = points(q, 2)
    out = {}
    for e1, e2 in itertools.combinations(directions(q), 2):
        det = (e1[0] * e2[1] - e2[0] * e1[1]) % q
        inv = pow(det, q - 2, q)

        def l1(x, e2=e2, inv=inv):
            return (inv * (e2[1] * x[0] - e2[0] * x[1])) % q

        def l2(x, e1=e1, inv=inv):
            return (inv * (-e1[1] * x[0] + e1[0] * x[1])) % q

        for f in oned:
            for g in oned:
                P = tuple(
                    tuple((f[l1(x)] * e1[j] + g[l2(x)] * e2[j]) % q for j in range(2))
                    for x in pts
                )
                out[P] = (e1, e2, f, g)
    return out


def frame_product_count(q):
    """C(q + 1, 2) * (q (q - 1))^2: the number of frame products of nondegenerate
    quadratics with P(0) = 0 (q odd)."""
    return (q + 1) * q // 2 * (q * (q - 1)) ** 2


def zero_slack(P, q, e1, e2):
    """Lemma 111 with l = l1 (the functional with l1(e1) = 1, l1(e2) = 0) and v = e1:
    True iff, for every t, l(Y_t) is a function of (pi_v(Y_t), l(X))."""
    pts = points(q, 2)
    det = (e1[0] * e2[1] - e2[0] * e1[1]) % q
    inv = pow(det, q - 2, q)

    def l1(y):
        return (inv * (e2[1] * y[0] - e2[0] * y[1])) % q

    assert l1(e1) == 1 and l1(e2) == 0
    for t in range(q):
        seen = {}
        for i, x in enumerate(pts):
            y = tuple((P[i][j] + t * x[j]) % q for j in range(2))
            ly = l1(y)
            pi = tuple((y[j] - ly * e1[j]) % q for j in range(2))
            key = (pi, l1(x))
            if seen.setdefault(key, ly) != ly:
                return False
    return True


if __name__ == "__main__":
    for q in (3, 5):
        fp = frame_products(q, sorted(quadratics_fixed0(q)))
        print("q", q, "frame products", len(fp), "expected", frame_product_count(q))
