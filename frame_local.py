# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""frame_local.py -- frame products are strict local maxima of the Kakeya entropy
functional among ALL maps (note notes/a176.md).

Lambda(P) = sum_{t in F_q} H(X | P(X) + tX), X uniform on F_q^k, entropy in bits.
S(P) = q^k Lambda(P) = sum_t sum_{fibres F of A_t} |F| log2 |F|, with A_t(x) = P(x) + t x.
A diagonal frame product is P(x)_i = a_i x_i^2 + b_i x_i + c_i (all a_i != 0, q odd),
possibly conjugated by an invertible linear map; it has S(P) = k(q-1) q^k exactly.

Self-contained (standard library only). In this code q must be an odd PRIME
(the theorems of a176 hold for every odd prime power q).
"""
import itertools
import math

LOG2E = 1.0 / math.log(2.0)


def g(n):
    """n log2 n, with g(0) = g(1) = 0."""
    return n * math.log2(n) if n > 1 else 0.0


def h(m):
    """g(m+1) - g(m): the change in sum |F| log2 |F| when a point joins a fibre of m points."""
    return g(m + 1) - g(m)


def psi(a):
    """psi(a) = h(2^a - 1) (Lemma 137)."""
    return h(2 ** a - 1)


def gamma(q, k):
    """Theorem 62 lower bound on S(P) - S(P') for one-point changes, q >= 5, k >= 2."""
    return (q - 1) * psi(k) - (q + 1) / 2.0 * h(2 ** k)


def radius(q, k):
    """Largest integer s with s < 1 + gamma(q, k)/2 (Corollary 62.1); needs gamma > 0."""
    gm = gamma(q, k)
    if gm <= 0:
        return 0
    s = 1
    while s + 1 < 1 + gm / 2.0:
        s += 1
    return s


Q3_GAP = 0.64  # Proposition 70: one-point gap at q = 3, k >= 2, is at least this (in S units)


def chi(a, q):
    """Legendre symbol mod the odd prime q, chi(0) = 0."""
    a %= q
    if a == 0:
        return 0
    return 1 if pow(a, (q - 1) // 2, q) == 1 else -1


class Space:
    """F_q^k with points encoded as integers 0 .. q^k - 1 (base-q digits)."""

    def __init__(self, q, k):
        self.q, self.k, self.N = q, k, q ** k
        self.digits = [tuple((x // q ** i) % q for i in range(k)) for x in range(self.N)]
        self.add = [[self.enc([a[i] + b[i] for i in range(k)]) for b in self.digits]
                    for a in self.digits]
        self.mul = [[self.enc([t * c for c in self.digits[x]]) for x in range(self.N)]
                    for t in range(q)]

    def enc(self, d):
        q = self.q
        return sum((d[i] % q) * q ** i for i in range(self.k))


def slice_values(sp, P, t):
    return [sp.add[P[x]][sp.mul[t][x]] for x in range(sp.N)]


def score(sp, P):
    """S(P) = q^k Lambda(P), computed from scratch (float)."""
    S = 0.0
    for t in range(sp.q):
        cnt = {}
        for y in slice_values(sp, P, t):
            cnt[y] = cnt.get(y, 0) + 1
        S += sum(g(n) for n in cnt.values())
    return S


def weight(sp, P):
    """Exact integer W(P) = prod over t and fibres of n^n, so S(P) = log2 W(P)."""
    W = 1
    for t in range(sp.q):
        cnt = {}
        for y in slice_values(sp, P, t):
            cnt[y] = cnt.get(y, 0) + 1
        for n in cnt.values():
            W *= n ** n
    return W


def frame_map(sp, coeffs):
    """Diagonal frame product: coordinate i is a x^2 + b x + c, coeffs[i] = (a, b, c), a != 0."""
    return [sp.enc([coeffs[i][0] * d[i] * d[i] + coeffs[i][1] * d[i] + coeffs[i][2]
                    for i in range(sp.k)]) for d in sp.digits]


def matvec(T, d):
    return [sum(T[i][j] * d[j] for j in range(len(d))) for i in range(len(T))]


def conjugate(sp, P, T, Tinv):
    """x -> T P(T^{-1} x); Lambda is invariant under this."""
    return [sp.enc(matvec(T, sp.digits[P[sp.enc(matvec(Tinv, d))]])) for d in sp.digits]


class OnePoint:
    """Counts for one-point changes of a fixed map P: N_t = |fibre of x0 under A_t|,
    M_t = #{y : A_t(y) = v + t x0} (Lemma 135)."""

    def __init__(self, sp, P):
        self.sp, self.P = sp, P
        self.vals = [slice_values(sp, P, t) for t in range(sp.q)]
        self.cnt = []
        for vs in self.vals:
            c = {}
            for y in vs:
                c[y] = c.get(y, 0) + 1
            self.cnt.append(c)

    def counts(self, x0, v):
        sp = self.sp
        Ns, Ms = [], []
        for t in range(sp.q):
            Ns.append(self.cnt[t][self.vals[t][x0]])
            Ms.append(self.cnt[t].get(sp.add[v][sp.mul[t][x0]], 0))
        return Ns, Ms


def gap(Ns, Ms):
    """Lemma 135: S(P) - S(P') = sum_t [h(N_t - 1) - h(M_t)] for a one-point change."""
    return sum(h(N - 1) - h(M) for N, M in zip(Ns, Ms))


def exact_one_point_sign(Ns, Ms):
    """Sign of S(P') - S(P) for a one-point change, by exact integer comparison."""
    new = old = 1
    for N, M in zip(Ns, Ms):
        new *= (N - 1) ** (N - 1) * (M + 1) ** (M + 1)
        old *= N ** N * M ** M
    return (new > old) - (new < old)


def formula_counts(q, coeffs, x0, v):
    """Closed form for a diagonal frame product (a176, Section 2):
    N_t = prod_i (1 + [u_i(t) != 0]), M_t = prod_i (1 + chi(u_i(t)^2 + delta_i)),
    u_i(t) = x0_i + (b_i + t)/(2 a_i), delta_i = (v_i - p_i(x0_i))/a_i."""
    Ns, Ms = [], []
    for t in range(q):
        N = M = 1
        for i, (a, b, c) in enumerate(coeffs):
            u = (x0[i] + (b + t) * pow(2 * a, q - 2, q)) % q
            delta = ((v[i] - (a * x0[i] * x0[i] + b * x0[i] + c)) * pow(a, q - 2, q)) % q
            N *= 2 if u else 1
            M *= 1 + chi(u * u + delta, q)
        Ns.append(N)
        Ms.append(M)
    return Ns, Ms


def config_counts(q, types):
    """Counts for an abstract configuration: coordinate i has u_i(t) = t - t_i and delta_i
    (the slope of u_i is absorbed into delta_i because chi(l^2 w) = chi(w))."""
    Ns, Ms = [], []
    for t in range(q):
        N = M = 1
        for ti, di in types:
            u = (t - ti) % q
            N *= 2 if u else 1
            M *= 1 + chi(u * u + di, q)
        Ns.append(N)
        Ms.append(M)
    return Ns, Ms


def min_config_gap(q, k):
    """Minimum of sum_t [h(N_t - 1) - h(M_t)] over all configurations with some delta != 0.
    Every one-point change of every diagonal frame product is such a configuration."""
    types = [(ti, di) for ti in range(q) for di in range(q)]
    best = None
    for combo in itertools.combinations_with_replacement(types, k):
        if all(d == 0 for _, d in combo):
            continue
        gp = gap(*config_counts(q, combo))
        best = gp if best is None else min(best, gp)
    return best


def lemma136_bound(sp, P, changes):
    """Lemma 136: for P' = P changed on the set S = changes.keys() (all values new),
    S(P) - S(P') >= sum_{x in S} [S(P) - S(P^(x))] - 2 s (s - 1)."""
    op = OnePoint(sp, P)
    s = len(changes)
    return sum(gap(*op.counts(x, v)) for x, v in changes.items()) - 2 * s * (s - 1)


def apply_changes(P, changes):
    Q = list(P)
    for x, v in changes.items():
        Q[x] = v
    return Q
