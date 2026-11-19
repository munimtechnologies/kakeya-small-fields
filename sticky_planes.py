# sticky_planes.py -- note a186: a sticky Kakeya set over F_3 splits exactly along its first
# coordinate (Theorem 74).  Consequences: the smallest sticky Kakeya sets in F_3^n have exactly
# 3, 7, 15 points for n = 1, 2, 3 and at least 29 for n = 4 (Theorem 75), so the smallest Kakeya
# sets in F_3^3 (13 points) and F_3^4 (at most 27 points) are not sticky in any basis.
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only, self-contained.
#
# Conventions.  A sticky family in F_3^n is given by node maps: for every prefix a (a tuple over
# {0,1,2} of length j < n) a map g_a: F_3 -> F_3, stored as a 3-tuple.  The base point of
# direction d has coordinates P(d)_j = g_{d[:j]}(d_j).  The line of d is {P(d) + t d : t in F_3}.
#   kakeya_set(maps, n): union of the lines of all d != 0 (a sticky Kakeya set).
#   slices(maps, k):     a FULL tree of height k uses every d in F_3^k, including d = 0;
#                        S_t = {P(d) + t d : d}.
# The selection game (a183/a184): leaf (1,1,1); affine(s): L_s = max, L_t = sum (t != s);
# triangle: L_t = L_t(iso(t)) + max of the other two.  A_k = game vectors of height k.

import itertools
import json
import random
import sys

LEAF = (1, 1, 1)

# ----------------------------------------------------------------------------- the game


def affine(children, s):
    p = []
    for t in range(3):
        vals = [c[t] for c in children]
        p.append(max(vals) if t == s else sum(vals))
    return tuple(p)


def triangle(children):
    """Triangle with iso = identity (ordered children cover every bijection)."""
    p = []
    for t in range(3):
        others = [children[x][t] for x in range(3) if x != t]
        p.append(children[t][t] + max(others))
    return tuple(p)


def leq(a, b):
    return a[0] <= b[0] and a[1] <= b[1] and a[2] <= b[2]


def pareto_min(vectors):
    front = []
    for v in sorted(set(vectors)):
        if not any(leq(f, v) for f in front):
            front.append(v)
    return front


def node_outputs(front):
    out = []
    for c in itertools.product(front, repeat=3):
        out.append(triangle(c))
        out.append(affine(c, 0))
        out.append(affine(c, 1))
        out.append(affine(c, 2))
    return out


def fronts(hmax):
    fr = [[LEAF]]
    for _ in range(hmax):
        fr.append(pareto_min(node_outputs(fr[-1])))
    return fr


def plane_bound(a, U):
    """Corollary 74.1: min over the hidden slice h of max(U, a_h) + sum_{t != h} a_t."""
    return min(max(U, a[h]) + sum(a) - a[h] for h in range(3))


def g_bounds(nmax=4):
    """G(0) = 0, G(k+1) = min over A_k of plane_bound(a, G(k)).  U*(n) >= G(n) (Theorem 75).
    A_k may be replaced by its Pareto front, or by node outputs over the front of A_{k-1},
    because plane_bound is nondecreasing in every coordinate and every node is monotone."""
    fr = fronts(max(nmax - 2, 0))
    G = [0]
    for k in range(nmax):
        if k < len(fr):
            cand = fr[k]
        else:
            cand = node_outputs(fr[k - 1])
        G.append(min(plane_bound(a, G[k]) for a in cand))
    return G


# ----------------------------------------------------------------------------- real sets


def P_of(maps, d):
    return tuple(maps[d[:j]][d[j]] for j in range(len(d)))


def kakeya_set(maps, n):
    K = set()
    for d in itertools.product(range(3), repeat=n):
        if not any(d):
            continue
        p = P_of(maps, d)
        for t in range(3):
            K.add(tuple((p[j] + t * d[j]) % 3 for j in range(n)))
    return K


def is_kakeya(K, n):
    """Every direction d != 0 has some line {b + t d} inside K."""
    pts = list(itertools.product(range(3), repeat=n))
    for d in pts:
        if not any(d):
            continue
        ok = False
        for b in K:
            if all(tuple((b[j] + t * d[j]) % 3 for j in range(n)) in K for t in range(3)):
                ok = True
                break
        if not ok:
            return False
    return True


def slices(maps, k):
    S = [set(), set(), set()]
    for d in itertools.product(range(3), repeat=k):
        p = P_of(maps, d)
        for t in range(3):
            S[t].add(tuple((p[j] + t * d[j]) % 3 for j in range(k)))
    return S


def random_maps(k, rng):
    maps = {}
    for j in range(k):
        for a in itertools.product(range(3), repeat=j):
            maps[a] = tuple(rng.randrange(3) for _ in range(3))
    return maps


def classical_maps(n):
    """g(x) = x^2 at every node: P(d) = (d_j^2), K = {0,1}^n u {0,2}^n."""
    maps = {}
    for j in range(n):
        for a in itertools.product(range(3), repeat=j):
            maps[a] = (0, 1, 1)
    return maps


def sub(maps, x):
    return {a[1:]: g for a, g in maps.items() if len(a) >= 1 and a[0] == x}


def decomposition_size(maps, n):
    """Theorem 74 (exact split).  Plane u of the first coordinate holds K^(0) (if u = g(0)) and,
    for x = 1, 2, slice t_x(u) = (u - g(x)) / x of the full subtree T_x."""
    root = maps[()]
    c0 = root[0]
    K0 = kakeya_set(sub(maps, 0), n - 1)
    S1 = slices(sub(maps, 1), n - 1)
    S2 = slices(sub(maps, 2), n - 1)

    def tx(x, u):
        return ((u - root[x]) * x) % 3      # x^(-1) = x in F_3

    total = 0
    for u in range(3):
        part = set(S1[tx(1, u)]) | set(S2[tx(2, u)])
        if u == c0:
            part |= K0
        total += len(part)
    return total


def construct(mapsK, mapsT, h, w, m):
    """Theorem 74 (construction).  From a sticky family in F_3^m (mapsK), a full tree of height m
    (mapsT), a hidden slice h and a shift w, build a sticky family in F_3^(m+1) whose Kakeya set
    has exactly formula_size(mapsK, mapsT, h, w, m) points."""
    maps = {(): (0, (-h) % 3, 0)}
    for a, g in mapsK.items():
        maps[(0,) + a] = g
    for a, g in mapsT.items():
        j = len(a)
        maps[(1,) + a] = tuple((g[y] + w[j]) % 3 for y in range(3))
    for a in mapsT:
        j = len(a)
        gT = mapsT[tuple((-v) % 3 for v in a)]
        maps[(2,) + a] = tuple((gT[(-y) % 3] + w[j] - h * y) % 3 for y in range(3))
    return maps


def formula_size(mapsK, mapsT, h, w, m):
    K = kakeya_set(mapsK, m)
    S = slices(mapsT, m)
    Sw = [set(tuple((z[j] + w[j]) % 3 for j in range(m)) for z in S[t]) for t in range(3)]
    return len(K | Sw[h]) + sum(len(Sw[t]) for t in range(3) if t != h)


def game_vector(maps, k, prefix=()):
    """Game vector of a full tree, by the general rule L_t = sum over value classes of the max."""
    if len(prefix) == k:
        return LEAF
    g = maps[prefix]
    kids = [game_vector(maps, k, prefix + (x,)) for x in range(3)]
    out = []
    for t in range(3):
        classes = {}
        for x in range(3):
            classes.setdefault((g[x] + t * x) % 3, []).append(kids[x][t])
        out.append(sum(max(c) for c in classes.values()))
    return tuple(out)


def min_sticky_dim2():
    """Exhaustive U*(2).  The map at prefix (0,) only serves the directions (0, y), y != 0, whose
    lines fill the row {g(0)} x F_3 for every choice of that map (checked in the tests), so it
    is fixed to (0, 0, 0) here."""
    best = None
    allmaps = list(itertools.product(range(3), repeat=3))
    for r in allmaps:
        for g1 in allmaps:
            for g2 in allmaps:
                maps = {(): r, (0,): (0, 0, 0), (1,): g1, (2,): g2}
                s = len(kakeya_set(maps, 2))
                if best is None or s < best:
                    best = s
    return best


# ----------------------------------------------------------------------------- results

KAKEYA_MIN_ALL = {"3": "13 (exact)", "4": "at most 27", "5": "at most 56",
                  "source": "munimtechnologies/kakeya-conjecture v1.1.0"}

WITNESS_CHILDREN = {
    "triangle_8_6_14": [[3, 3, 9], [3, 3, 9], [5, 3, 5]],
    "triangle_7_7_13": [[3, 3, 9], [3, 3, 9], [4, 4, 4]],
    "affine0_5_9_15": [[5, 3, 5], [5, 3, 5], [5, 3, 5]],
}


def witness_vectors():
    out = {}
    for name, kids in WITNESS_CHILDREN.items():
        c = [tuple(v) for v in kids]
        v = triangle(c) if name.startswith("triangle") else affine(c, 0)
        out[name] = list(v)
    return out


def results():
    G = g_bounds(4)
    classical = {str(n): len(kakeya_set(classical_maps(n), n)) for n in range(1, 5)}
    return {
        "note": "a186",
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "G": G,
        "classical_sizes": classical,
        "exhaustive_min_dim2": min_sticky_dim2(),
        "witness_vectors_n4": witness_vectors(),
        "witness_plane_bound_n4": {k: plane_bound(tuple(v), G[3])
                                   for k, v in witness_vectors().items()},
        "sticky_min_bounds": {str(n): [G[n], 2 ** (n + 1) - 1] for n in range(1, 5)},
        "kakeya_min_all": KAKEYA_MIN_ALL,
    }


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "sticky_planes.json"
    with open(out, "w") as fh:
        json.dump(results(), fh, indent=1)
