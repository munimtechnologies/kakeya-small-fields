"""Translates of cubes in finite groups (section 12 of the README).

Pure Python, no dependencies. A finite group is given by its multiplication table on the
elements 0 .. N - 1 (0 is the identity). A pattern T is a list of 0/1 vectors t of length r; for
d = (d_1, ..., d_r) in G^r its points are the ordered products w_t(d) = d_1^(t_1) ... d_r^(t_r)
(in an abelian group, t_1 d_1 + ... + t_r d_r). A set K is T-universal if for every d in G^r
some left translate {a w_t(d) : t in T} lies in K.

    python cubes.py table      the exponents of section 12 for r = 1 .. 5
    python cubes.py small      least cube-universal sets in some groups of order <= 16

By MV2 of Munim, Inc. Researched and written with AI agents working in his name.
Licence: Apache-2.0.
"""

import itertools
import math
import sys
from collections import Counter


# ---------------------------------------------------------------- groups

class Group:
    """A finite group on the elements 0 .. N - 1 with identity 0; mul[a][b] is the product a b."""

    def __init__(self, name, mul):
        self.name = name
        self.mul = mul
        self.order = len(mul)
        self.inv = [next(b for b in range(self.order) if mul[a][b] == 0)
                    for a in range(self.order)]


def cyclic(n):
    return Group("Z_%d" % n, [[(a + b) % n for b in range(n)] for a in range(n)])


def product(*groups):
    """Direct product; an element is numbered by the mixed-radix value of its coordinates."""
    elements = list(itertools.product(*[range(g.order) for g in groups]))
    index = {e: i for i, e in enumerate(elements)}
    mul = [[index[tuple(g.mul[x][y] for g, x, y in zip(groups, a, b))] for b in elements]
           for a in elements]
    return Group(" x ".join(g.name for g in groups), mul)


def symmetric3():
    """S_3, the smallest non-abelian group. (0, 1, 2) sorts first, so the identity is 0."""
    perms = sorted(itertools.permutations(range(3)))
    index = {p: i for i, p in enumerate(perms)}
    mul = [[index[tuple(p[q[x]] for x in range(3))] for q in perms] for p in perms]
    return Group("S_3", mul)


def small_groups():
    c2, c3, c4, c8 = cyclic(2), cyclic(3), cyclic(4), cyclic(8)
    s3 = symmetric3()
    return ([cyclic(n) for n in range(2, 17)]
            + [product(c2, c2), product(c2, c2, c2), product(c2, c2, c2, c2), product(c3, c3),
               product(c2, c4), product(c4, c4), product(c2, c8), product(c2, c2, c4),
               s3, product(s3, c2)])


# ---------------------------------------------------------------- patterns

def cube(r):
    """The pattern {0,1}^r. Its images are the r-dimensional cubes {sum of d_i over i in S}."""
    return list(itertools.product((0, 1), repeat=r))


def simplex(r):
    """The pattern 0, e_1, ..., e_r. Its images are all sets {e, d_1, ..., d_r}, so a set containing
    a translate of each is (r + 1)-universal in the sense of Alon, Bukh and Sudakov."""
    return [tuple(int(i == j) for i in range(r)) for j in range(-1, r)]


def word(group, d, t):
    """w_t(d) = d_1^(t_1) d_2^(t_2) ... d_r^(t_r)."""
    w = 0
    for x, bit in zip(d, t):
        if bit:
            w = group.mul[w][x]
    return w


def tuples(group, r):
    return list(itertools.product(range(group.order), repeat=r))


def word_table(group, r, pattern):
    """words[i][k] = w_t(d) for the i-th tuple d of tuples(group, r) and t = pattern[k]."""
    return [[word(group, d, t) for t in pattern] for d in tuples(group, r)]


# ---------------------------------------------------------------- universal sets

def pattern_sets(group, r, pattern):
    """The distinct point sets {w_t(d) : t in pattern} over all d, largest first."""
    found = {frozenset(row) for row in word_table(group, r, pattern)}
    return sorted(found, key=lambda s: (-len(s), sorted(s)))


def universal_tester(group, r, pattern):
    """A function telling whether a collection of elements K contains a left translate of
    {w_t(d) : t in pattern} for every d in G^r."""
    sets = [tuple(s) for s in pattern_sets(group, r, pattern)]
    mul, inv, n = group.mul, group.inv, group.order

    def is_universal(points):
        # starts[g] is the bit mask of the a with a g in K, that is a = k g^(-1) with k in K.
        starts = []
        for g in range(n):
            m = 0
            gi = inv[g]
            for k in points:
                m |= 1 << mul[k][gi]
            starts.append(m)
        for s in sets:
            m = -1
            for g in s:
                m &= starts[g]
                if not m:
                    return False
        return True

    return is_universal


def is_universal_naive(group, r, pattern, points):
    """The definition, checked directly (slow; for cross-checks)."""
    members = set(points)
    for d in tuples(group, r):
        ws = [word(group, d, t) for t in pattern]
        if not any(all(group.mul[a][w] in members for w in ws) for a in range(group.order)):
            return False
    return True


def min_universal(group, r, pattern):
    """Exhaustive search from size 1 up: (least size of a T-universal set, example). A left
    translate of a T-universal set is T-universal, so the search keeps the identity in the set."""
    is_universal = universal_tester(group, r, pattern)
    others = range(1, group.order)
    for size in range(1, group.order + 1):
        for rest in itertools.combinations(others, size - 1):
            points = (0,) + rest
            if is_universal(points):
                return size, points
    raise AssertionError("the whole group is always T-universal")


# ---------------------------------------------------------------- bounds

def size_floor(order, m):
    """Least integer k with k^m >= order^(m - 1). By Theorem 8 every T-universal set of a group
    of this order, for a pattern of m points, has at least this many points."""
    k = 1
    while k ** m < order ** (m - 1):
        k += 1
    return k


def lower_exponent(m):
    """Theorem 8: |K| >= N^(1 - 1/m)."""
    return 1 - 1 / m


def counting_exponent(r):
    """Counting the cubes inside K: N^r <= |K|^(r + 1), so only |K| >= N^(r/(r+1))."""
    return r / (r + 1)


def random_upper(order, m):
    """Proposition 4: some set of at most this many points contains a left translate of every set
    of at most m elements."""
    if m > order:
        return order
    return min(order, 2 * order ** (1 - 1 / m) * (m * m * (m * math.log(order) + 1)) ** (1 / m))


# ---------------------------------------------------------------- the entropy inequality

def entropy_of_counts(counts, total):
    return -sum(c / total * math.log2(c / total) for c in counts if c)


def slice_entropies(group, table, words):
    """H(Y_t) for each column of words, where Y_t = A w_t(d), d is uniform on G^r and the base
    point A = table[i] is a function of the i-th tuple d."""
    total = len(table)
    mul = group.mul
    result = []
    for k in range(len(words[0])):
        counts = Counter(mul[table[i]][words[i][k]] for i in range(total))
        result.append(entropy_of_counts(counts.values(), total))
    return result


def entropy_sum(group, table, words):
    return sum(slice_entropies(group, table, words))


def exhaustive_minima(group, r):
    """For every nonempty pattern T in {0,1}^r, the least sum over t in T of H(Y_t) over all
    deterministic base points A : G^r -> G. Returns {T as a tuple of vectors: least sum}."""
    pattern = cube(r)
    words = word_table(group, r, pattern)
    subsets = [s for k in range(1, len(pattern) + 1)
               for s in itertools.combinations(range(len(pattern)), k)]
    best = {s: float("inf") for s in subsets}
    for table in itertools.product(range(group.order), repeat=len(words)):
        h = slice_entropies(group, table, words)
        for s in subsets:
            v = sum(h[k] for k in s)
            if v < best[s]:
                best[s] = v
    return {tuple(pattern[k] for k in s): v for s, v in best.items()}


def local_minimum(group, words, rng):
    """Steepest descent of entropy_sum over deterministic base points from a random start; returns
    the value at the local minimum and the table."""
    table = [rng.randrange(group.order) for _ in range(len(words))]
    best = entropy_sum(group, table, words)
    improved = True
    while improved:
        improved = False
        for i in range(len(table)):
            keep = table[i]
            for v in range(group.order):
                if v == keep:
                    continue
                table[i] = v
                value = entropy_sum(group, table, words)
                if value < best - 1e-12:
                    best, keep, improved = value, v, True
            table[i] = keep
    return best, table


def inverse_base_point(group, r, s):
    """The base point A(d) = w_s(d)^(-1), which makes Y_s the identity (the equality case)."""
    return [group.inv[word(group, d, s)] for d in tuples(group, r)]


# ---------------------------------------------------------------- main

def table_rows(rs=range(1, 6)):
    return [(r, counting_exponent(r), lower_exponent(2 ** r)) for r in rs]


def main(argv):
    command = argv[1] if len(argv) > 1 else "table"
    if command == "table":
        print("r   counting cubes r/(r+1)   Theorem 8: 1 - 2^-r")
        for r, count, exact in table_rows():
            print("%d   %.4f                   %.4f" % (r, count, exact))
    elif command == "small":
        for group in small_groups():
            size, example = min_universal(group, 2, cube(2))
            print("%-14s N = %2d   least 2-cube-universal set %2d   (Theorem 8 floor %d)   e.g. %s"
                  % (group.name, group.order, size, size_floor(group.order, 4), list(example)))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv)
