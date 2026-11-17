# SPDX-License-Identifier: Apache-2.0
"""slice4.py -- code for note a167 (kakeya-small-fields).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Apache-2.0. Standard library only; self-contained (imports no other repository module).

Contents
- Brute-force Lambda(P) = sum_t H(X | P(X) + tX) (bits), pair counts and Pibar.
- Proposition 52: Pibar = (q-1) * E_y e(R_y + L) for degree-2 maps (q odd), where
  e(T) is the number of eigendirections of T in PG(k-1, q).
- Proposition 53: the dual form Pibar = q^(1-k) * sum_{psi != 0} |V_psi| [psi L = 0 on V_psi].
- The family G_n(w, tau) = (tau w, Phi(w)) on F_q^(n+1), Phi(w) = w_1^2 + ... + w_n^2
  (Theorem 44: it respects no subspace and Pibar = (q-1) + (q^n - 1)/q, so the Jensen
  bound of a166 fails for it when q is large).
- Theorem 45 (sliced Jensen bound, any map, any slicing) and its closed form for G_n
  (Theorem 46: C_q(n+1) holds for G_n).
All q used in the tests are primes, so arithmetic mod q is field arithmetic.
"""

import itertools
import math
from collections import defaultdict
from fractions import Fraction


# ---------------------------------------------------------------- basics

def points(q, k):
    return list(itertools.product(range(q), repeat=k))


def proj_points(q, k):
    """Normalised representatives of PG(k-1, q): first nonzero coordinate is 1."""
    out = []
    for x in itertools.product(range(q), repeat=k):
        for v in x:
            if v:
                if v == 1:
                    out.append(x)
                break
    return out


def inv(a, q):
    return pow(a % q, q - 2, q)


def legendre(a, q):
    a %= q
    if a == 0:
        return 0
    return 1 if pow(a, (q - 1) // 2, q) == 1 else -1


def in_line(d, v, q):
    """True if the vector d lies in F_q v (v nonzero)."""
    p = next(i for i, c in enumerate(v) if c)
    mu = d[p] * inv(v[p], q) % q
    return all((a - mu * b) % q == 0 for a, b in zip(d, v))


def matvec(T, w, q):
    return tuple(sum(T[i][j] * w[j] for j in range(len(w))) % q for i in range(len(T)))


def table_of(f, q, k):
    return {x: tuple(f(x)) for x in points(q, k)}


def fibres(tab, q, t):
    """Fibres of P_t(x) = P(x) + t x, as a dict output -> list of points."""
    fib = defaultdict(list)
    for x, y in tab.items():
        fib[tuple((a + t * b) % q for a, b in zip(y, x))].append(x)
    return fib


def lam(tab, q, k):
    """Lambda(P) in bits (float)."""
    terms = []
    for t in range(q):
        for xs in fibres(tab, q, t).values():
            n = len(xs)
            if n > 1:
                terms.append(n * math.log2(n))
    return math.fsum(terms) / q ** k


def pair_total(tab, q):
    """Number of ordered pairs x != x' that collide at some t (each collides at most once)."""
    total = 0
    for t in range(q):
        for xs in fibres(tab, q, t).values():
            total += len(xs) * (len(xs) - 1)
    return total


def pibar(tab, q, k):
    return Fraction(pair_total(tab, q), q ** k)


def jensen_bound(pb, q):
    """Theorem 42 (a166): Lambda <= q log2(1 + Pibar/q)."""
    return q * math.log2(1 + float(pb) / q)


def pi_direction(tab, q, v):
    """Pi_v = #{(x, lambda): lambda != 0, P(x + lambda v) - P(x) in F_q v}."""
    cnt = 0
    for x, y in tab.items():
        for lm in range(1, q):
            xv = tuple((a + lm * b) % q for a, b in zip(x, v))
            d = tuple((a - b) % q for a, b in zip(tab[xv], y))
            if in_line(d, v, q):
                cnt += 1
    return cnt


# ---------------------------------------------------------------- respected subspaces

def subspaces(q, k):
    """All nonzero proper subspaces of F_q^k (each as a frozenset of vectors), via RREF."""
    for d in range(1, k):
        for piv in itertools.combinations(range(k), d):
            free = [(r, c) for r in range(d) for c in range(piv[r] + 1, k) if c not in piv]
            for vals in itertools.product(range(q), repeat=len(free)):
                rows = [[0] * k for _ in range(d)]
                for r in range(d):
                    rows[r][piv[r]] = 1
                for (r, c), val in zip(free, vals):
                    rows[r][c] = val
                span = set()
                for cf in itertools.product(range(q), repeat=d):
                    span.add(tuple(sum(cf[r] * rows[r][c] for r in range(d)) % q
                                   for c in range(k)))
                yield frozenset(span)


def respects(tab, q, V):
    """P respects V: P(x + v) - P(x) lies in V for every x and every v in V."""
    for v in V:
        if not any(v):
            continue
        for x, y in tab.items():
            xv = tuple((a + b) % q for a, b in zip(x, v))
            d = tuple((a - b) % q for a, b in zip(tab[xv], y))
            if d not in V:
                return False
    return True


def respected_subspaces(tab, q, k):
    return [V for V in subspaces(q, k) if respects(tab, q, V)]


# ---------------------------------------------------------------- degree-2 maps

def random_quadratic(q, k, rng):
    """P = Q + L + c with Q_i(x) = sum_{j <= l} A[i, j, l] x_j x_l."""
    A = {(i, j, l): rng.randrange(q) for i in range(k) for j in range(k) for l in range(j, k)}
    L = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
    c = [rng.randrange(q) for _ in range(k)]
    return A, L, c


def quad_eval(A, L, c, q, k):
    def f(x):
        out = []
        for i in range(k):
            s = c[i]
            for j in range(k):
                s += L[i][j] * x[j]
                for l in range(j, k):
                    s += A[(i, j, l)] * x[j] * x[l]
            out.append(s % q)
        return tuple(out)
    return f


def beta(A, q, k, x, w):
    """beta(x, w) = Q(x + w) - Q(x) - Q(w), symmetric bilinear."""
    return tuple(sum(A[(i, j, l)] * (x[j] * w[l] + w[j] * x[l])
                     for j in range(k) for l in range(j, k)) % q for i in range(k))


def unit(k, j):
    return tuple(1 if i == j else 0 for i in range(k))


def eigen_count(T, q, proj):
    return sum(1 for w in proj if in_line(matvec(T, w, q), w, q))


def mean_eigendirections(A, L, q, k):
    """E_y e(R_y + L) as a Fraction, R_y w = beta(y, w) (Proposition 52)."""
    proj = proj_points(q, k)
    total = 0
    for y in points(q, k):
        cols = [beta(A, q, k, y, unit(k, j)) for j in range(k)]
        T = [[(cols[j][i] + L[i][j]) % q for j in range(k)] for i in range(k)]
        total += eigen_count(T, q, proj)
    return Fraction(total, q ** k)


def dual_sigma(A, L, q, k):
    """Sigma = sum_psi |V_psi| [psi(L v) = 0 for all v in V_psi] (Proposition 53),
    V_psi = {v : psi(v) = 0 and psi(beta(e_j, v)) = 0 for all j}."""
    pts = points(q, k)
    bet = {v: [beta(A, q, k, unit(k, j), v) for j in range(k)] for v in pts}
    Lv = {v: matvec(L, v, q) for v in pts}

    def dot(a, b):
        return sum(x * y for x, y in zip(a, b)) % q

    total = 0
    for psi in pts:
        V = [v for v in pts if dot(psi, v) == 0 and all(dot(psi, b) == 0 for b in bet[v])]
        if all(dot(psi, Lv[v]) == 0 for v in V):
            total += len(V)
    return total


# ---------------------------------------------------------------- the family G_n

def g_map(q, n):
    """G_n(w, tau) = (tau w, Phi(w)), Phi(w) = w_1^2 + ... + w_n^2, on F_q^(n+1)."""
    def f(x):
        tau = x[n]
        return tuple((tau * x[i]) % q for i in range(n)) + (sum(v * v for v in x[:n]) % q,)
    return f


def spin_map(q, n):
    """x o x / 2 for the spin factor (Jordan algebra of Phi): (tau w, Phi(w) + tau^2 / 2)."""
    h = inv(2, q)
    def f(x):
        tau = x[n]
        return (tuple((tau * x[i]) % q for i in range(n))
                + ((sum(v * v for v in x[:n]) + h * tau * tau) % q,))
    return f


def frame_map(q, k):
    def f(x):
        return tuple((v * v) % q for v in x)
    return f


def last_coord(n):
    return lambda x: x[n]


def pibar_G(q, n):
    """Theorem 44: Pibar(G_n) = (q - 1) + (q^n - 1)/q."""
    return Fraction(q - 1) + Fraction(q ** n - 1, q)


def n_zero(q, n):
    """N(0) = #{w in F_q^n : w_1^2 + ... + w_n^2 = 0} (closed form)."""
    if n % 2 == 1:
        return q ** (n - 1)
    nu = legendre((-1) ** (n // 2), q)
    return q ** (n - 1) + nu * (q - 1) * q ** ((n - 2) // 2)


def n_counts(q, n):
    cnt = defaultdict(int)
    for w in itertools.product(range(q), repeat=n):
        cnt[sum(v * v for v in w) % q] += 1
    return cnt


def D_closed(q, n, t):
    """sum over x of the number of distinct tau-values in the Y_t-fibre of x (Lemma 121)."""
    N0 = n_zero(q, n)
    if t % q:
        return (2 * q - 2) * q ** n + (2 - q) * N0 + (q - 1)
    return (2 * q - 1) * q ** n + (q - 1) * (q - 2) * N0 + (q - 1)


def sum_N_squared(q, n):
    """Lemma 120: sum_c N(c)^2 = q^(2n-1) + (q-1) q^(n-1)."""
    return q ** (2 * n - 1) + (q - 1) * q ** (n - 1)


def sliced_closed(q, n):
    """Closed form of the Theorem 45 bound for G_n sliced by tau (Theorem 46)."""
    M = q ** (n + 1)
    cross = (q - 1) * math.log2(D_closed(q, n, 1) / M) + math.log2(D_closed(q, n, 0) / M)
    inner = math.log2(sum_N_squared(q, n) / q ** n)
    return cross + inner


# ---------------------------------------------------------------- Theorem 45

def slice_data(tab, q, slicer):
    """For each t: (D_t, {z: sum over fibre-parts in slice z of size^2}); and slice sizes.
    D_t = sum over x of the number of distinct slices met by the Y_t-fibre of x."""
    size = defaultdict(int)
    for x in tab:
        size[slicer(x)] += 1
    per_t = []
    for t in range(q):
        D = 0
        within = defaultdict(int)
        for xs in fibres(tab, q, t).values():
            cnt = defaultdict(int)
            for x in xs:
                cnt[slicer(x)] += 1
            D += len(xs) * len(cnt)
            for z, c in cnt.items():
                within[z] += c * c
        per_t.append((D, dict(within)))
    return per_t, dict(size)


def sliced_bound(tab, q, k, slicer):
    """Theorem 45: Lambda <= sum_t [log2 m_t + sum_z Pr(z) log2(1 + p_t(z))]."""
    per_t, size = slice_data(tab, q, slicer)
    N = q ** k
    terms = []
    for D, within in per_t:
        terms.append(math.log2(D / N))
        for z, sz in size.items():
            terms.append((sz / N) * math.log2(within[z] / sz))
    return math.fsum(terms)


def jensen_threshold(q, k):
    """Pibar above this value makes the Jensen bound exceed k(q-1)."""
    return q * (2 ** (k * (q - 1) / q) - 1)
