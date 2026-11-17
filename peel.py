# SPDX-License-Identifier: Apache-2.0
"""peel.py: the peeling inequality and the one-coordinate loss (note a168).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Apache-2.0. Standard library only; self-contained (imports no other module of the repo).

Maps of F_q^k (q prime) are dicts {point tuple: image tuple}. For t in F_q,
Y_t = P(X) + t X with X uniform. Entropies are in bits.
"""

import itertools
import math
from collections import Counter, defaultdict


def points(q, k):
    return list(itertools.product(range(q), repeat=k))


def dot(a, b, q):
    return sum(x * y for x, y in zip(a, b)) % q


def ent(counts):
    """Shannon entropy (bits) of the distribution proportional to counts."""
    n = sum(counts)
    return -sum(c / n * math.log2(c / n) for c in counts if c)


def h_terms(tab, q, t, f=None):
    """(H(X|Y_t), H(f(X)|Y_t), H(X|Y_t, f(X))) for the map tab and labels f."""
    N = len(tab)
    groups = defaultdict(list)
    for x, y in tab.items():
        groups[tuple((yi + t * xi) % q for yi, xi in zip(y, x))].append(x)
    hx = hf = hin = 0.0
    for g in groups.values():
        hx += len(g) / N * math.log2(len(g))
        if f is not None:
            cnt = Counter(f[x] for x in g)
            hf += len(g) / N * ent(list(cnt.values()))
            hin += sum(c / N * math.log2(c) for c in cnt.values())
    return hx, hf, hin


def lam(tab, q):
    """Lambda(P) = sum_t H(X | P(X) + tX)."""
    return sum(h_terms(tab, q, t)[0] for t in range(q))


def ell(tab, q, f):
    """One-coordinate loss ell_P(f) = sum_t H(f(X) | Y_t)."""
    return sum(h_terms(tab, q, t, f)[1] for t in range(q))


def inslice(tab, q, f):
    """sum_t H(X | Y_t, f(X))."""
    return sum(h_terms(tab, q, t, f)[2] for t in range(q))


def graph_slicing(q, k, psi, e, g):
    """Graph slicing of F_q^k (Theorem 47).

    psi: a nonzero functional (tuple); e: a vector with psi(e) = 1; g: dict on F_q^(k-1).
    pi(x) = coordinates of x - psi(x) e in the basis b_i = e_i - (psi_i/psi_j) e_j (i != j),
    a linear map with kernel span(e). f(x) = psi(x) - g(pi(x)). sigma(z, u) is the point of
    the slice f = z with pi = u. Returns (f, pi, sigma)."""
    assert dot(psi, e, q) == 1
    j = next(i for i in range(k) if psi[i] % q)
    inv = pow(psi[j], q - 2, q)
    others = [i for i in range(k) if i != j]

    def pi(x):
        s = dot(psi, x, q)
        return tuple((x[i] - s * e[i]) % q for i in others)

    def sigma(z, u):
        s = (g[u] + z) % q
        x = [0] * k
        for a, i in enumerate(others):
            x[i] = (x[i] + u[a]) % q
            x[j] = (x[j] - u[a] * psi[i] * inv) % q
        return tuple((x[i] + s * e[i]) % q for i in range(k))

    f = {x: (dot(psi, x, q) - g[pi(x)]) % q for x in points(q, k)}
    return f, pi, sigma


def projected(tab, q, k, pi, sigma, z):
    """P'_z(u) = pi(P(sigma(z, u))), a map of F_q^(k-1)."""
    return {u: pi(tab[sigma(z, u)]) for u in points(q, k - 1)}


def slice_entropy(tab, q, t, f, z):
    """H(X | Y_t, f(X) = z) with X uniform on the slice f = z."""
    groups = Counter(tuple((yi + t * xi) % q for yi, xi in zip(tab[x], x))
                     for x in tab if f[x] == z)
    n = sum(groups.values())
    return sum(c / n * math.log2(c) for c in groups.values())


def h_single(tab, q, t):
    return h_terms(tab, q, t)[0]


# ---------- example maps ----------

def frame_map(q, k):
    return {x: tuple(v * v % q for v in x) for x in points(q, k)}


def g_map(q, n):
    """G_n(w, tau) = (tau w, w_1^2 + ... + w_n^2) on F_q^(n+1)."""
    tab = {}
    for x in points(q, n + 1):
        w, tau = x[:n], x[n]
        tab[x] = tuple(tau * v % q for v in w) + (sum(v * v for v in w) % q,)
    return tab


def irreducible(q, k):
    """A monic irreducible polynomial x^k + sum c_i x^i over F_q, k in (2, 3) (no roots)."""
    assert k in (2, 3)
    for c in itertools.product(range(q), repeat=k):
        if all((pow(a, k, q) + sum(ci * pow(a, i, q) for i, ci in enumerate(c))) % q
               for a in range(q)):
            return c
    raise ValueError


def fmul(a, b, q, k, c):
    prod = [0] * (2 * k - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            prod[i + j] = (prod[i + j] + ai * bj) % q
    for d in range(2 * k - 2, k - 1, -1):
        co = prod[d]
        if co:
            prod[d] = 0
            for i, ci in enumerate(c):
                prod[d - k + i] = (prod[d - k + i] - co * ci) % q
    return tuple(prod[:k])


def squaring_map(q, k):
    """z -> z^2 on F_(q^k), written in the basis 1, x, ..., x^(k-1)."""
    c = irreducible(q, k)
    return {x: fmul(x, x, q, k, c) for x in points(q, k)}


# ---------- Proposition 55: closed forms for G_n sliced by tau ----------

def n_counts(q, n):
    return Counter(sum(v * v for v in w) % q for w in points(q, n))


def c_q(q):
    """Sum over s in F_q^* of log2 m for one w with Phi(w) != 0 (Lemma 122(i))."""
    if q % 3:
        return (q - 5) / 2 * math.log2(3) + 2
    return (q - 3) / 2 * math.log2(3)


def nh(N):
    """(N + 1) h(1/(N + 1)) in bits, h the binary entropy."""
    if N == 0:
        return 0.0
    p = 1 / (N + 1)
    return (N + 1) * (-p * math.log2(p) - (1 - p) * math.log2(1 - p))


def ell_t_formula(q, n, cnt):
    """H(tau | Y_t) for G_n, t != 0 (Lemma 122)."""
    N0 = cnt[0]
    tot = (q ** n - N0) * c_q(q) + sum(nh(cnt[c]) for c in range(1, q))
    return tot / q ** (n + 1)


def ell_0_formula(q, n, cnt):
    """H(tau | Y_0) for G_n (Lemma 122)."""
    N0 = cnt[0]
    size = q - 1 + N0
    hs = ent([N0] + [1] * (q - 1))
    tot = (q - 1) * (q ** n - N0) + (q - 1) * (N0 - 1) * math.log2(q - 1) + size * hs
    return tot / q ** (n + 1)


def ell_tau_bound(q, n):
    """The upper bound for ell_{G_n}(tau) used in the proof of Proposition 55(b)."""
    lq = math.log2(q)
    case1 = (q - 1) / q * c_q(q)
    typ = ((n - 1) * lq + 1 + math.log2(math.e)) / q ** (n - 1)
    t0 = (q - 1) / q + 2 * (q - 1) * q ** (n - 1) * math.log2(q - 1) / q ** (n + 1) \
        + (q + 2 * q ** (n - 1) + (q - 1) * math.log2(q - 1)) / q ** (n + 1)
    return case1 + typ + t0
