# SPDX-License-Identifier: Apache-2.0
"""avgslice.py: tools for note a169 of kakeya-small-fields (averaged slicing, the
triangle lemma for collisions, the directional decomposition of the plane, and the
record slack of the one-coordinate criterion).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Apache-2.0. Standard library only; self-contained (imports no other module of the repo).

Conventions: q is a prime, points of F_q^k are k-tuples of ints mod q, a map P is a dict
{x: P(x)}. For t in F_q, Y_t = P(X) + tX with X uniform on F_q^k, and
Lambda(P) = sum_t H(X | Y_t) in bits.
"""

import math
from itertools import product


def points(q, k):
    return list(product(range(q), repeat=k))


def dot(a, b, q):
    return sum(x * y for x, y in zip(a, b)) % q


def proj_functionals(q, k):
    """One nonzero vector per projective point (first nonzero coordinate equal to 1).
    There are (q^k - 1)/(q - 1) of them. A functional and its nonzero multiples give the
    same partition of F_q^k, so averages over these equal averages over all nonzero psi."""
    out = []
    for v in product(range(q), repeat=k):
        nz = [c for c in v if c]
        if nz and nz[0] == 1:
            out.append(v)
    return out


def fibres(tab, q, k, t):
    groups = {}
    for x, y in tab.items():
        key = tuple((y[j] + t * x[j]) % q for j in range(k))
        groups.setdefault(key, []).append(x)
    return list(groups.values())


def all_fibres(tab, q, k):
    return [fibres(tab, q, k, t) for t in range(q)]


def slogs(counts):
    """sum n log2 n over the counts."""
    return sum(n * math.log2(n) for n in counts if n > 1)


def lam(tab, q, k, fib=None):
    if fib is None:
        fib = all_fibres(tab, q, k)
    return sum(slogs([len(F)]) for Ft in fib for F in Ft) / q ** k


def fibre_entropy(F, f):
    """H(f(U)) in bits, U uniform on the list of points F."""
    m = len(F)
    cnt = {}
    for x in F:
        c = f(x)
        cnt[c] = cnt.get(c, 0) + 1
    return (slogs([m]) - slogs(cnt.values())) / m


def ell(tab, q, k, f, fib=None):
    """ell_P(f) = sum_t H(f(X) | Y_t)."""
    if fib is None:
        fib = all_fibres(tab, q, k)
    return sum(len(F) * fibre_entropy(F, f) for Ft in fib for F in Ft) / q ** k


def ell_lin(tab, q, k, psi, fib=None):
    return ell(tab, q, k, lambda x, p=psi: dot(p, x, q), fib)


def p_k(q, k):
    """Probability that a uniform nonzero functional of F_q^k kills a fixed nonzero vector."""
    return (q ** (k - 1) - 1) / (q ** k - 1)


def avg_slice_entropy(F, q, k):
    """Average over nonzero psi of H(psi(U)), U uniform on F (Lemma 124)."""
    fs = proj_functionals(q, k)
    return sum(fibre_entropy(F, lambda x, p=psi: dot(p, x, q)) for psi in fs) / len(fs)


def threshold(q, k):
    """q - q^(1-k): Theorem 48 gives (*) with a linear functional below this loss."""
    return q - q ** (1 - k)


def record_slack(q):
    """q log2(2 - 1/q) - (q - 1): how far the constant q - 1 in (*) may be relaxed while
    still beating the Bukh-Chao growth constant q/(2 - 1/q) (Theorem 49)."""
    return q * math.log2(2 - 1 / q) - (q - 1)


def collision_time(tab, q, k, x, y):
    """The unique t with P(x) + t x = P(y) + t y (x != y), or None."""
    d = [(x[j] - y[j]) % q for j in range(k)]
    e = [(tab[x][j] - tab[y][j]) % q for j in range(k)]
    for t in range(q):
        if all((e[j] + t * d[j]) % q == 0 for j in range(k)):
            return t
    return None


def collision_table(tab, q, k):
    pts = sorted(tab)
    col = {}
    for i, x in enumerate(pts):
        for y in pts[i + 1:]:
            t = collision_time(tab, q, k, x, y)
            col[(x, y)] = t
            col[(y, x)] = t
    return col


def ratio(a, b, q):
    """mu with b = mu * a if b is a multiple of the nonzero vector a, else None."""
    j = next(i for i, c in enumerate(a) if c % q)
    mu = b[j] * pow(a[j], q - 2, q) % q
    if all((mu * a[i] - b[i]) % q == 0 for i in range(len(a))):
        return mu
    return None


def triangle_violations(tab, q, k, col=None):
    """Checks Lemma 123 at every cherry y -t- x -t'- z. Returns the list of violations."""
    if col is None:
        col = collision_table(tab, q, k)
    pts = sorted(tab)
    nb = {x: [] for x in pts}
    for (x, y), t in col.items():
        if t is not None:
            nb[x].append((y, t))
    bad = []
    for x in pts:
        lst = nb[x]
        for i in range(len(lst)):
            y, t = lst[i]
            for z, t2 in lst[i + 1:]:
                s = col[(y, z)]
                if t == t2:
                    if s != t:
                        bad.append(("fibre", x, y, z))
                    continue
                a = tuple((x[j] - y[j]) % q for j in range(k))
                b = tuple((x[j] - z[j]) % q for j in range(k))
                mu = ratio(a, b, q)
                if mu is None:
                    if s is not None:
                        bad.append(("noncollinear", x, y, z))
                else:
                    want = (t - mu * t2) * pow((1 - mu) % q, q - 2, q) % q
                    if s != want:
                        bad.append(("collinear", x, y, z))
    return bad


def normal(v, q):
    """For k = 2: the functional nu_v = (v1, -v0), whose kernel is span(v)."""
    return (v[1] % q, (-v[0]) % q)


def directional_loss(tab, q, v, fib=None):
    """Lambda_v = sum_t E log2 |F_t(X) cap (X + F_q v)| for a map of F_q^2."""
    nu = normal(v, q)
    if fib is None:
        fib = all_fibres(tab, q, 2)
    tot = 0.0
    for Ft in fib:
        for F in Ft:
            cnt = {}
            for x in F:
                c = dot(nu, x, q)
                cnt[c] = cnt.get(c, 0) + 1
            tot += slogs(cnt.values())
    return tot / q ** 2


def mean_cluster_excess(tab, q, v):
    """E_x (c_v(x) - 1), c_v(x) = #{y on x + F_q v : nu_v(P(y)) = nu_v(P(x))}."""
    nu = normal(v, q)
    groups = {}
    for x, y in tab.items():
        key = (dot(nu, x, q), dot(nu, y, q))
        groups[key] = groups.get(key, 0) + 1
    return sum(n * (n - 1) for n in groups.values()) / q ** 2


def nonresidue(q):
    for n in range(2, q):
        if pow(n, (q - 1) // 2, q) == q - 1:
            return n
    raise ValueError("q must be an odd prime")


def squaring_plane(q, a=1, b=(0, 0)):
    """z -> a z^2 + b z on F_(q^2) = F_q[s]/(s^2 - n), n a non-residue, as a map of F_q^2.
    a in F_q is nonzero and b = b0 + b1 s. Every fibre of Y_t has at most 2 points."""
    n = nonresidue(q)
    b0, b1 = b
    tab = {}
    for x0, x1 in points(q, 2):
        s0 = (x0 * x0 + n * x1 * x1) % q
        s1 = (2 * x0 * x1) % q
        tab[(x0, x1)] = ((a * s0 + b0 * x0 + n * b1 * x1) % q,
                         (a * s1 + b0 * x1 + b1 * x0) % q)
    return tab
