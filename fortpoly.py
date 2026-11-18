"""fortpoly.py: the fort polynomial of a frame map's support pattern (note a179).

MV2 of Munim, Inc. Made with AI agents working in MV2's name.
SPDX-License-Identifier: Apache-2.0

Standard library only. Field arithmetic is mod q, so q must be an odd PRIME in this file.
A matrix M is a list of k rows with entries in range(q). A digraph on [k] is a list
`outs` of k bitmasks: bit j of outs[i] is set when row i reads column j (j != i, M[i][j] != 0).
"""
from fractions import Fraction
from itertools import product
from math import comb, exp, log2


def popcount(x):
    return bin(x).count("1")


def digraph_of(M):
    """Out-neighbour bitmasks of the digraph of M (arc i -> j when i != j and M[i][j] != 0)."""
    k = len(M)
    outs = []
    for i in range(k):
        mask = 0
        for j in range(k):
            if j != i and M[i][j] != 0:
                mask |= 1 << j
        outs.append(mask)
    return outs


def is_fort(outs, T):
    """True when no vertex outside T has exactly one out-neighbour in T (T = 0 included)."""
    for i in range(len(outs)):
        if not (T >> i) & 1 and popcount(outs[i] & T) == 1:
            return False
    return True


def fort_poly(outs, q):
    """Phi_q(G) = sum over T (empty or a fort) of a^|T|, a = (q-1)/q, as an exact Fraction."""
    k = len(outs)
    total = 0
    for T in range(1 << k):
        if is_fort(outs, T):
            t = popcount(T)
            total += (q - 1) ** t * q ** (k - t)
    return Fraction(total, q ** k)


def pi_m(q, m):
    """Fraction of e in (F_q^*)^m with e_1 + ... + e_m = 0 (pi(0) = 1, pi(1) = 0)."""
    return Fraction((q - 1) ** m + (-1) ** m * (q - 1), q * (q - 1) ** m)


def packing_factor(outs, T, q):
    """Min over packings P of prod_{i in P} pi(|N(i) & T|).

    A packing is a set of rows outside T whose (nonempty) out-neighbourhoods inside T are
    pairwise disjoint. The empty packing gives 1.
    """
    k = len(outs)
    nbs = [outs[i] & T for i in range(k) if not (T >> i) & 1 and outs[i] & T]
    best = Fraction(1)
    n = len(nbs)
    for S in range(1, 1 << n):
        used = 0
        val = Fraction(1)
        ok = True
        for s in range(n):
            if (S >> s) & 1:
                if used & nbs[s]:
                    ok = False
                    break
                used |= nbs[s]
                val *= pi_m(q, popcount(nbs[s]))
        if ok and val < best:
            best = val
    return best


def packing_poly(outs, q):
    """Phi*_q(G) = sum over all T of a^|T| * packing_factor(T) (Proposition 75)."""
    k = len(outs)
    a = Fraction(q - 1, q)
    total = Fraction(0)
    for T in range(1 << k):
        total += a ** popcount(T) * packing_factor(outs, T, q)
    return total


def fibre_counts(fmap, q, k):
    """Sizes of the fibres of fmap on F_q^k, as a dict image -> size."""
    counts = {}
    for y in product(range(q), repeat=k):
        f = fmap(y)
        counts[f] = counts.get(f, 0) + 1
    return counts


def sum_and_product(counts):
    """(sum_y N_y, prod_y N_y) where N_y is the size of the fibre through y."""
    s = 0
    w = 1
    for c in counts.values():
        s += c * c
        w *= c ** c
    return s, w


def frame_map(M, q):
    """y -> y o y + M y over F_q."""
    k = len(M)

    def f(y):
        return tuple((y[i] * y[i] + sum(M[i][j] * y[j] for j in range(k))) % q
                     for i in range(k))
    return f


def frame_stats(M, q):
    """(sum_y N_y, prod_y N_y) for the frame map of M. E N = sum / q^k, H = log2(prod)/q^k."""
    return sum_and_product(fibre_counts(frame_map(M, q), q, len(M)))


def V(M, q, T):
    """Number of d with support exactly T and (M d)_i = 0 for every i outside T."""
    k = len(M)
    idx = [j for j in range(k) if (T >> j) & 1]
    outside = [i for i in range(k) if not (T >> i) & 1]
    cnt = 0
    for vals in product(range(1, q), repeat=len(idx)):
        d = [0] * k
        for j, v in zip(idx, vals):
            d[j] = v
        if all(sum(M[i][j] * d[j] for j in range(k)) % q == 0 for i in outside):
            cnt += 1
    return cnt


def inv(x, q):
    return pow(x, q - 2, q)


def conj_map(A, S, L, c, q, t):
    """x -> A((Sx) o (Sx)) + Lx + c + t x with A, S diagonal (given as lists)."""
    k = len(L)

    def f(x):
        return tuple((A[i] * (S[i] * x[i]) ** 2 + sum(L[i][j] * x[j] for j in range(k))
                      + t * x[i] + c[i]) % q for i in range(k))
    return f


def slice_matrix(A, S, L, q, t):
    """M_t = A^-1 (L + tI) S^-1 for diagonal A, S."""
    k = len(L)
    return [[(inv(A[i], q) * ((L[i][j] + (t if i == j else 0)) % q) * inv(S[j], q)) % q
             for j in range(k)] for i in range(k)]


# ---------------- Theorem 67: random support patterns ----------------

def H2(x):
    return -x * log2(x) - (1 - x) * log2(1 - x)


def r_head(q):
    """2^H2(1/5) a^(1/5) / b."""
    a = (q - 1) / q
    return 2 ** H2(0.2) * a ** 0.2 / 2 ** (1 - 1 / q)


def r_mid(q, m=0.16):
    """(1 + a - m) / b."""
    return (1 + (q - 1) / q - m) / 2 ** (1 - 1 / q)


def r_tail(q):
    """2^H2(13/20) a^(13/20) / b."""
    a = (q - 1) / q
    return 2 ** H2(0.65) * a ** 0.65 / 2 ** (1 - 1 / q)


def h_one(t, p):
    """P(Bin(t, p) = 1)."""
    return t * p * (1 - p) ** (t - 1)


def expected_fort_poly(q, k, p):
    """E_G Phi_q(G) for G ~ D(k, p) (Lemma 142); exact when p is a Fraction."""
    a = Fraction(q - 1, q)
    total = Fraction(0)
    for t in range(k + 1):
        g = Fraction(1) if t == 0 else 1 - t * p * (1 - p) ** (t - 1)
        total += comb(k, t) * a ** t * g ** (k - t)
    return total


def limit_exponent(q, c, tau):
    """Limit of (1/k) log2 of the t = tau k term of E Phi_q at p = c/k (numerical remark)."""
    a = (q - 1) / q
    x = c * tau
    return H2(tau) + tau * log2(a) + (1 - tau) * log2(1 - x * exp(-x))
