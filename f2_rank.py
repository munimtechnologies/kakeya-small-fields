"""Kakeya sets of rank r over F_2: the exact growth base (section 11 of the README).

Pure Python, no dependencies. A point of F_2^n is an integer 0 .. 2^n - 1 (bit i is
coordinate i), so addition is XOR. A set of points is a bit mask over the 2^n points.

    python f2_rank.py table      the bounds of section 11 for r = 1 .. 6
    python f2_rank.py small      exact K_r(n, 2) for n <= 4 by exhaustive search

By MV2 of Munim, Inc. Researched and written with AI agents working in his name.
Licence: Apache-2.0.
"""

import itertools
import math
import sys
from collections import Counter


# ---------------------------------------------------------------- subspaces and Kakeya sets

def span(vectors):
    """The subspace of F_2^n spanned by the given vectors, as a sorted tuple of points."""
    points = {0}
    for v in vectors:
        points |= {p ^ v for p in points}
    return tuple(sorted(points))


def subspaces(n, r):
    """All r-dimensional subspaces of F_2^n, each a sorted tuple of its 2^r points."""
    found = set()
    for vectors in itertools.combinations(range(1, 2 ** n), r):
        s = span(vectors)
        if len(s) == 2 ** r:
            found.add(s)
    return sorted(found)


def gaussian_binomial_2(n, r):
    """Number of r-dimensional subspaces of F_2^n."""
    num = den = 1
    for i in range(r):
        num *= 2 ** (n - i) - 1
        den *= 2 ** (i + 1) - 1
    return num // den


def coset_masks(n, sub):
    """Bit masks of the 2^(n - r) cosets a + sub of a subspace of F_2^n."""
    masks = set()
    for a in range(2 ** n):
        m = 0
        for w in sub:
            m |= 1 << (a ^ w)
        masks.add(m)
    return sorted(masks)


def kakeya_tester(n, r):
    """A function telling whether a bit mask of points is a Kakeya set of rank r in F_2^n."""
    families = [coset_masks(n, s) for s in subspaces(n, r)]

    def is_kakeya(mask):
        return all(any((c & mask) == c for c in cosets) for cosets in families)

    return is_kakeya


def mask_of(points):
    m = 0
    for p in points:
        m |= 1 << p
    return m


def min_kakeya(n, r):
    """Exhaustive search from size 0 up: (least size of a rank-r Kakeya set in F_2^n, example)."""
    is_kakeya = kakeya_tester(n, r)
    for size in range(2 ** n + 1):
        for points in itertools.combinations(range(2 ** n), size):
            if is_kakeya(mask_of(points)):
                return size, points
    raise AssertionError("the whole space is always a Kakeya set")


def entropy_floor(n, r):
    """Least integer k with k^(2^r) >= 2^((2^r - 1) n). By Theorem 7, every rank-r Kakeya
    set in F_2^n has at least this many points."""
    k = 1
    while k ** (2 ** r) < 2 ** ((2 ** r - 1) * n):
        k += 1
    return k


# ---------------------------------------------------------------- the entropy inequality

def entropy_of_counts(counts, total):
    return -sum(c / total * math.log2(c / total) for c in counts if c)


def shift_table(n, r):
    """shifts[i][t] = t_1 d_1 + ... + t_r d_r for the i-th tuple d (d_j = bits n j .. n j + n - 1
    of i) and t in F_2^r (bit j of t is t_(j+1))."""
    mask = 2 ** n - 1
    shifts = []
    for i in range(2 ** (n * r)):
        d = [(i >> (n * j)) & mask for j in range(r)]
        row = []
        for t in range(2 ** r):
            s = 0
            for j in range(r):
                if (t >> j) & 1:
                    s ^= d[j]
            row.append(s)
        shifts.append(row)
    return shifts


def entropy_sum(n, r, table, shifts=None):
    """sum over t in F_2^r of H(A + t.d) for d_1..d_r uniform and independent on F_2^n and the
    base point A = table[i] a function of d (i encodes d as in shift_table)."""
    if shifts is None:
        shifts = shift_table(n, r)
    total = len(table)
    result = 0.0
    for t in range(2 ** r):
        counts = Counter(table[i] ^ shifts[i][t] for i in range(total))
        result += entropy_of_counts(counts.values(), total)
    return result


def entropy_sum_random(n, r, laws, shifts=None):
    """As entropy_sum, but A may be random: laws[i] is a dict {point: probability}, the law of A
    given the i-th tuple d."""
    if shifts is None:
        shifts = shift_table(n, r)
    weight = 1.0 / len(laws)
    result = 0.0
    for t in range(2 ** r):
        law = Counter()
        for i, cond in enumerate(laws):
            for a, p in cond.items():
                law[a ^ shifts[i][t]] += weight * p
        result -= sum(p * math.log2(p) for p in law.values() if p > 0)
    return result


def local_minimum(n, r, rng, shifts=None):
    """Steepest descent of entropy_sum over deterministic tables from a random start; returns the
    value at the local minimum and the table."""
    if shifts is None:
        shifts = shift_table(n, r)
    table = [rng.randrange(2 ** n) for _ in range(2 ** (n * r))]
    best = entropy_sum(n, r, table, shifts)
    improved = True
    while improved:
        improved = False
        for i in range(len(table)):
            keep = table[i]
            for v in range(2 ** n):
                if v == keep:
                    continue
                table[i] = v
                value = entropy_sum(n, r, table, shifts)
                if value < best - 1e-12:
                    best, keep, improved = value, v, True
            table[i] = keep
    return best, table


def witness_table(n, r, points):
    """For a rank-r Kakeya set K (a collection of points), the base point A(d): the first a with
    a + span(d_1, ..., d_r) inside K. Raises if K is not Kakeya."""
    members = set(points)
    mask = 2 ** n - 1
    table = []
    for i in range(2 ** (n * r)):
        sub = span([(i >> (n * j)) & mask for j in range(r)])
        for a in range(2 ** n):
            if all((a ^ s) in members for s in sub):
                table.append(a)
                break
        else:
            raise ValueError("not a Kakeya set of rank %d" % r)
    return table


# ---------------------------------------------------------------- bounds

def new_base(r):
    """beta_(2, r) = 2^(1 - 2^(-r)) (Corollary 6)."""
    return 2 ** (1 - 2 ** (-r))


def klss_lower_base(r, q=2):
    """KLSS Theorem 1: beta_(q, r) >= q^(r+1) / (q^r + q - 1)."""
    return q ** (r + 1) / (q ** r + q - 1)


def table_rows(rs=range(1, 7)):
    return [(r, klss_lower_base(r), new_base(r)) for r in rs]


def main(argv):
    command = argv[1] if len(argv) > 1 else "table"
    if command == "table":
        print("r   KLSS lower bound   beta_(2,r) = 2^(1 - 2^-r)")
        for r, low, exact in table_rows():
            print("%d   %.4f             %.4f" % (r, low, exact))
    elif command == "small":
        for n in range(1, 5):
            for r in range(1, n + 1):
                size, example = min_kakeya(n, r)
                print("K_%d(%d, 2) = %d   (entropy floor %d)   e.g. %s"
                      % (r, n, size, entropy_floor(n, r), list(example)))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv)
