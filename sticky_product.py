# sticky_product.py -- note a188: the growth constant of sticky Kakeya sets over F_3 is the cube root of
# the slice-product constant of full sticky trees (Theorem 78).  So the open question S7 (is the sticky
# Kakeya base below 2?) has a finite certificate: ONE full sticky tree of some height k whose three
# slices have product below 8^k.  Lemma 161 (products and slice symmetries of full trees), Lemma 162
# (one node multiplies the slice product by at least 27/4, and an affine node by at least 9) and
# Proposition 83 (pi_1 = 8, pi_2 = 64 exactly, by exhausting all 27^4 trees of height 2).
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only; uses sticky_planes.py (a186) and sticky_break.py (a187).
#
# Conventions are those of sticky_planes.py: a full tree of height k is a dict of node maps, prefix
# (tuple of length j < k) -> 3-tuple (g(0), g(1), g(2)); P(d)_j = g_{d[:j]}(d_j); its slices are
# S_t = {P(d) + t d : d in F_3^k} for t = 0, 1, 2 (d = 0 included).

import functools
import itertools
import json
import sys

from sticky_planes import slices, classical_maps
from sticky_break import tree_T

ALL_MAPS = list(itertools.product(range(3), repeat=3))
POP = [bin(i).count("1") for i in range(8)]

# ----------------------------------------------------------------------------- Lemma 161


def rotate(maps, c):
    """P'(d) = P(d) + c d.  Sticky, and S_t(P') = S_(t+c)(P)."""
    return {a: tuple((g[y] + c * y) % 3 for y in range(3)) for a, g in maps.items()}


def reflect(maps):
    """P'(d) = P(-d).  Sticky, and S_t(P') = S_(-t)(P)."""
    out = {}
    for a in maps:
        g = maps[tuple((-v) % 3 for v in a)]
        out[a] = tuple(g[(-y) % 3] for y in range(3))
    return out


def product(mapsA, ka, mapsB, kb):
    """Product of a tree A of height ka and a tree B of height kb (height ka + kb):
    P(d) = (P_A(d_1..d_ka), P_B(d_(ka+1)..d_(ka+kb))).  Sticky, and S_t = S_t(A) x S_t(B)."""
    out = dict(mapsA)
    for b, g in mapsB.items():
        for a in itertools.product(range(3), repeat=ka):
            out[a + b] = g
    return out


def balanced(maps, k):
    """T x rotate(T, 1) x rotate(T, 2), of height 3k.  Its slice t is S_t x S_(t+1) x S_(t+2), so every
    slice has exactly |S_0| |S_1| |S_2| points."""
    m = product(maps, k, rotate(maps, 1), k)
    return product(m, 2 * k, rotate(maps, 2), k)


def slice_sizes(maps, k):
    return [len(s) for s in slices(maps, k)]


def slice_product(maps, k):
    a, b, c = slice_sizes(maps, k)
    return a * b * c


# ----------------------------------------------------------------------------- Lemma 162


def is_affine_map(g):
    return (g[2] - g[1]) % 3 == (g[1] - g[0]) % 3


def node_bound_holds(maps, k):
    """Lemma 162 at the root of a full tree of height k >= 1, with children T_x = sub(maps, x):
    affine root:    prod(T)^3 >= 9^3 * prod(T_0) prod(T_1) prod(T_2);
    quadratic root: 64 prod(T)^3 >= 27^3 * prod(T_0) prod(T_1) prod(T_2)."""
    kids = []
    for x in range(3):
        kids.append({a[1:]: g for a, g in maps.items() if len(a) >= 1 and a[0] == x})
    G = 1
    for m in kids:
        G *= slice_product(m, k - 1)
    P = slice_product(maps, k)
    if is_affine_map(maps[()]):
        return P ** 3 >= 729 * G
    return 64 * P ** 3 >= 19683 * G


# ----------------------------------------------------------------------------- Proposition 83


def _vmask(g, t):
    m = 0
    for z in range(3):
        m |= 1 << ((g[z] + t * z) % 3)
    return m


def exhaustive_height1():
    """All 27 full trees of height 1: (min slice product, min slice sum)."""
    prods, sums = [], []
    for g in ALL_MAPS:
        s = [POP[_vmask(g, t)] for t in range(3)]
        prods.append(s[0] * s[1] * s[2])
        sums.append(s[0] + s[1] + s[2])
    return min(prods), min(sums)


@functools.lru_cache(maxsize=None)
def exhaustive_height2():
    """All 27^4 full trees of height 2 (a root map and three child maps):
    (min slice product, min slice sum).  Plane v of slice t holds the union of the child slices
    {h_x(z) + t z} over the children x with r(x) + t x = v."""
    V = [[_vmask(g, t) for t in range(3)] for g in ALL_MAPS]
    best_p = None
    best_s = None
    for r in ALL_MAPS:
        planes = [[(r[x] + t * x) % 3 for x in range(3)] for t in range(3)]
        for h0, h1, h2 in itertools.product(range(27), repeat=3):
            p = 1
            s = 0
            for t in range(3):
                pl = planes[t]
                acc = [0, 0, 0]
                acc[pl[0]] |= V[h0][t]
                acc[pl[1]] |= V[h1][t]
                acc[pl[2]] |= V[h2][t]
                st = POP[acc[0]] + POP[acc[1]] + POP[acc[2]]
                p *= st
                s += st
            if best_p is None or p < best_p:
                best_p = p
            if best_s is None or s < best_s:
                best_s = s
    return best_p, best_s


# ----------------------------------------------------------------------------- results


def results():
    p1, s1 = exhaustive_height1()
    p2, s2 = exhaustive_height2()
    T = tree_T()
    return {
        "note": "a188",
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "pi": {"1": p1, "2": p2},
        "sigma": {"1": s1, "2": s2},
        "eight_to_the_k": {"1": 8, "2": 64, "3": 512},
        "classical_slices": {str(k): slice_sizes(classical_maps(k), k) for k in range(1, 6)},
        "tree_T_slices": slice_sizes(T, 3),
        "tree_T_product": slice_product(T, 3),
        "tree_T_balanced_slices": slice_sizes(balanced(T, 3), 9),
        "criterion": ("beta_s = lim U*(n)^(1/n) = tau^(1/3) with tau = inf_k pi_k^(1/k); "
                      "beta_s < 2 iff some full sticky tree of some height k has slice product < 8^k"),
    }


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "sticky_product.json"
    with open(out, "w") as fh:
        json.dump(results(), fh, indent=1)
