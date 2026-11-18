# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""Note a178: annealed pair counts for random frame maps (self-contained, stdlib only).

Frame map of a k x k matrix M over the prime field F_q (q odd prime):
    F(y) = y o y + M y,   H(M) = H(Y | F(Y)) for Y uniform on F_q^k.
N_y is the size of the F-fibre through y, so H(M) = E log2 N_y and
E_y N_y = (sum of squared fibre sizes) / q^k.

Random models (off-diagonal entries independent; the diagonal never matters):
    entry (i, j) is 0 with probability 1 - p_ij and uniform on F_q^* otherwise.
Lemma 141:  E_M E_y N_y = sum_T a^|T| prod_{i not in T} (1 + (q-1) prod_{j in T} lam_ij) / q,
            a = (q-1)/q, lam_ij = 1 - p_ij q/(q-1).
"""
import itertools
import math
from fractions import Fraction


def points(q, k):
    return itertools.product(range(q), repeat=k)


def frame_value(q, M, y):
    k = len(M)
    return tuple((y[i] * y[i] + sum(M[i][j] * y[j] for j in range(k))) % q
                 for i in range(k))


def fibre_sizes(q, M):
    counts = {}
    for y in points(q, len(M)):
        F = frame_value(q, M, y)
        counts[F] = counts.get(F, 0) + 1
    return list(counts.values())


def mean_fibre(q, M):
    """E_y N_y as an exact Fraction."""
    sizes = fibre_sizes(q, M)
    return Fraction(sum(s * s for s in sizes), q ** len(M))


def weight(q, M):
    """W = prod_y N_y = prod over fibres s^s, so H(M) = log2(W) / q^k."""
    W = 1
    for s in fibre_sizes(q, M):
        W *= s ** s
    return W


def entropy(q, M):
    return math.log2(weight(q, M)) / q ** len(M)


def jensen_holds_exactly(q, M):
    """2^H(M) <= E_y N_y, i.e. prod_y N_y * Q^Q <= (sum_y N_y)^Q with Q = q^k."""
    Q = q ** len(M)
    sizes = fibre_sizes(q, M)
    return weight(q, M) * Q ** Q <= sum(s * s for s in sizes) ** Q


def sr_strict_holds_exactly(q, M):
    """H(M) < k (1 - 1/q)  <=>  W^q < 2^(Q k (q-1))."""
    k = len(M)
    return weight(q, M) ** q < 2 ** (q ** k * k * (q - 1))


def entropy_at_least(q, M, s):
    """H(M) >= s for an integer s  <=>  W >= 2^(s Q)."""
    return weight(q, M) >= 2 ** (s * q ** len(M))


def off_diagonal(k):
    return [(i, j) for i in range(k) for j in range(k) if i != j]


def entry_law(q, p, v):
    p = Fraction(p)
    return 1 - p if v == 0 else p / (q - 1)


def annealed_bruteforce(q, k, P, diag=None, values=None):
    """Exact E_M E_y N_y by enumerating every off-diagonal assignment.

    P[i][j] = p_ij (Fractions). diag: fixed diagonal (default 0). values: optional
    dict (i, j) -> allowed values (default all of F_q), used for fixed patterns.
    """
    off = off_diagonal(k)
    choices = [values[(i, j)] if values else range(q) for (i, j) in off]
    total = Fraction(0)
    mass = Fraction(0)
    for vals in itertools.product(*choices):
        w = Fraction(1)
        for (i, j), v in zip(off, vals):
            w *= entry_law(q, P[i][j], v)
        if w == 0:
            continue
        M = [[0] * k for _ in range(k)]
        for i in range(k):
            M[i][i] = diag[i] if diag else 0
        for (i, j), v in zip(off, vals):
            M[i][j] = v
        total += w * mean_fibre(q, M)
        mass += w
    assert mass == 1
    return total


def annealed_formula(q, k, P):
    """Lemma 141, exact."""
    a = Fraction(q - 1, q)
    lam = [[1 - Fraction(P[i][j]) * q / (q - 1) for j in range(k)] for i in range(k)]
    total = Fraction(0)
    for t in range(k + 1):
        for T in itertools.combinations(range(k), t):
            term = a ** t
            for i in range(k):
                if i in T:
                    continue
                prod = Fraction(1)
                for j in T:
                    prod *= lam[i][j]
                term *= (1 + (q - 1) * prod) / q
            total += term
    return total


def S(q, k, p):
    """Lemma 141 for the homogeneous model R(k, p): sum_t C(k,t) a^t pi_t^(k-t)."""
    a = Fraction(q - 1, q)
    lam = 1 - Fraction(p) * q / (q - 1)
    return sum(math.comb(k, t) * a ** t * ((1 + (q - 1) * lam ** t) / q) ** (k - t)
               for t in range(k + 1))


def split_bound(q, k, p):
    """Theorem 66 proof, exact: S <= sum_{t < t0} C(k,t) a^t + (1 + a lam^t0)^k, t0 = ceil(k/5)."""
    a = Fraction(q - 1, q)
    lam = 1 - Fraction(p) * q / (q - 1)
    t0 = -(-k // 5)
    head = sum(math.comb(k, t) * a ** t for t in range(t0))
    return head, (1 + a * lam ** t0) ** k, t0, lam


def H2(x):
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def ratios(q):
    """(r_A, r_B) of Theorem 66: r_A = 2^(H2(1/5) + log2(a)/5) / b, r_B = (1 + a e^(-1/5)) / b."""
    a = (q - 1) / q
    b = 2 ** (1 - 1 / q)
    return 2 ** (H2(0.2) + 0.2 * math.log2(a)) / b, (1 + a * math.exp(-0.2)) / b


def pi_pattern(q, m):
    """Probability that a sum of m independent uniform nonzero elements of F_q is 0."""
    return Fraction(1 + (q - 1) * Fraction(-1, q - 1) ** m, q)


def outdeg_into(arcs, i, T):
    return sum(1 for j in T if (i, j) in arcs)


def is_fort(k, arcs, T):
    """No vertex outside T has exactly one out-neighbour in T."""
    return all(outdeg_into(arcs, i, T) != 1 for i in range(k) if i not in T)


def pattern_sum(q, k, arcs):
    """Proposition 72: Phi_q(G) = sum_T a^|T| prod_{i not in T} pi(m_i(T))."""
    a = Fraction(q - 1, q)
    total = Fraction(0)
    for t in range(k + 1):
        for T in itertools.combinations(range(k), t):
            term = a ** t
            for i in range(k):
                if i not in T:
                    term *= pi_pattern(q, outdeg_into(arcs, i, T))
            total += term
    return total


def arcs_of(M):
    """Arc i -> j when i != j and M_ij != 0 (entries are reduced mod q)."""
    k = len(M)
    return {(i, j) for i in range(k) for j in range(k) if i != j and M[i][j] != 0}


def V(q, M, T):
    """Number of d with support exactly T and M[T^c, T] d_T = 0."""
    k = len(M)
    T = list(T)
    count = 0
    for dT in itertools.product(range(1, q), repeat=len(T)):
        if all(sum(M[i][j] * x for j, x in zip(T, dT)) % q == 0
               for i in range(k) if i not in T):
            count += 1
    return count


def rank_mod(q, rows):
    """Rank over F_q (q prime) of a list of row vectors."""
    rows = [list(r) for r in rows]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    for c in range(ncols):
        piv = next((r for r in range(rank, len(rows)) if rows[r][c] % q), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], q - 2, q)
        rows[rank] = [(x * inv) % q for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][c] % q:
                f = rows[r][c]
                rows[r] = [(x - f * y) % q for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def rho(q, M, T):
    """rank of M[T^c, T]."""
    k = len(M)
    rows = [[M[i][j] for j in T] for i in range(k) if i not in T]
    if not rows or not T:
        return 0
    return rank_mod(q, rows)


def fort_half_expanding(q, M):
    """Proposition 73 hypothesis: rho(T) >= ceil(min(|T|, k-|T|)/2) for every fort T of M."""
    k = len(M)
    arcs = arcs_of(M)
    for t in range(1, k):
        for T in itertools.combinations(range(k), t):
            if is_fort(k, arcs, T) and rho(q, M, T) < -(-min(t, k - t) // 2):
                return False
    return True


def fort_bound(q, k, arcs):
    """Proposition 72 upper bound: sum over forts T (and the empty set) of a^|T| (q-1)^-out(T)."""
    a = Fraction(q - 1, q)
    total = Fraction(0)
    for t in range(k + 1):
        for T in itertools.combinations(range(k), t):
            if not is_fort(k, arcs, T):
                continue
            out = sum(1 for i in range(k) if i not in T and outdeg_into(arcs, i, T) >= 2)
            total += a ** t * Fraction(1, (q - 1) ** out)
    return total
