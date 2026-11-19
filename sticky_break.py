# sticky_break.py -- note a187: a sticky Kakeya set in F_3^4 with 30 points, one fewer than the
# classical set {0,1}^4 u {0,2}^4 (31 points), and a colour-lifting lemma that carries the saving
# to every dimension: U*(n) <= 31 * 2^(n-4) - 1 < 2^(n+1) - 1 for every n >= 4.
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only; uses sticky_planes.py (note a186) from this repository.
#
# Conventions are those of sticky_planes.py: a sticky family in F_3^n is a dict of node maps,
# prefix (tuple of length j < n) -> 3-tuple (g(0), g(1), g(2)); P(d)_j = g_{d[:j]}(d_j).
#
# Colours.  A colouring gives every point of the Kakeya set one of three colours, read as the
# three 2-subsets COLS of F_3.  It is GOOD for a family if every line of the family (one line per
# direction d != 0) shows exactly two colours.  Lemma 160 (lift): a good colouring of a sticky
# family in F_3^n gives a sticky family in F_3^(n+1) with exactly 2|K| + 1 points and again a good
# colouring.  The fibre over a point p is the colour set of p, except over P(0), where it is F_3.

import itertools
import json
import sys

from sticky_planes import (P_of, kakeya_set, is_kakeya, slices, construct, formula_size,
                           game_vector, classical_maps)

COLS = ((0, 1), (0, 2), (1, 2))
ALL_MAPS = list(itertools.product(range(3), repeat=3))

# ----------------------------------------------------------------------------- the n = 4 set

# K'' : a sticky Kakeya set in F_3^2 (all lines through the origin; it fills the plane).
MAPS_K2 = {(): (0, 0, 0), (0,): (0, 0, 0), (1,): (0, 0, 0), (2,): (0, 0, 0)}

# Y : full tree of height 2 with P(f) = (-f1, 0).  Slices: graph {(a,0)}, row {0} x F_3, plane.
MAPS_Y = {(): (0, 2, 1), (0,): (0, 0, 0), (1,): (0, 0, 0), (2,): (0, 0, 0)}

# X : full tree of height 2 with P(f) = (1, -f2).  Slices: row {1} x F_3, graph {(a,0)}, plane.
MAPS_X = {(): (1, 1, 1), (0,): (0, 2, 1), (1,): (0, 2, 1), (2,): (0, 2, 1)}

# Z : full tree of height 2 with P(f) = (f1^2, -f1 f2).  Every slice is a row plus one point.
MAPS_Z = {(): (0, 1, 1), (0,): (0, 0, 0), (1,): (0, 2, 1), (2,): (0, 1, 2)}


def tree_T():
    """Full tree of height 3: root x -> x^2 over the subtrees (Y, X, Z).  Slices 7, 7, 13."""
    maps = {(): (0, 1, 1)}
    for x, sub in enumerate((MAPS_Y, MAPS_X, MAPS_Z)):
        for a, g in sub.items():
            maps[(x,) + a] = g
    return maps


def family_K3():
    """K' in F_3^3: Theorem 74's construction from K'', the tree Y, hidden slice 2, shift 0.
    Planes y = 0, 1, 2 hold the whole plane, the graph {(a,0)} and the row {0} x F_3: 15 points."""
    return construct(MAPS_K2, MAPS_Y, 2, (0, 0), 2)


def family_K4():
    """The 30-point sticky Kakeya set in F_3^4: Theorem 74's construction from K', T, h = 2, w = 0.
    |K| = |K' u S_2(T)| + |S_0(T)| + |S_1(T)| = 16 + 7 + 7."""
    return construct(family_K3(), tree_T(), 2, (0, 0, 0), 3)


def colouring_K4():
    """An explicit good colouring of the 30-point set (colour indices into COLS)."""
    col = {}
    for p in kakeya_set(family_K4(), 4):
        y1, y2, y3, y4 = p
        if y1 != 0:
            c = 0                                  # planes 1 and 2
        elif y2 == 0:
            c = 1 if (y3, y4) == (0, 0) else 2     # the full plane of K'
        elif y2 == 1:
            c = 1
        else:
            c = 2
        col[p] = c
    return col


# ----------------------------------------------------------------------------- checks


def is_full_family(maps, n):
    """Exactly one map for every prefix of length < n (so the family is sticky by construction)."""
    want = {a for j in range(n) for a in itertools.product(range(3), repeat=j)}
    if set(maps) != want:
        return False
    return all(len(g) == 3 and all(v in (0, 1, 2) for v in g) for g in maps.values())


def line_points(maps, d):
    p = P_of(maps, d)
    n = len(d)
    return [tuple((p[j] + t * d[j]) % 3 for j in range(n)) for t in range(3)]


def is_good_colouring(maps, n, col):
    for d in itertools.product(range(3), repeat=n):
        if not any(d):
            continue
        pts = line_points(maps, d)
        if any(q not in col for q in pts):
            return False
        if len({col[q] for q in pts}) != 2:
            return False
    return True


# ----------------------------------------------------------------------------- Lemma 160


def label_for(targets):
    """A map g: F_3 -> F_3 with {g(z) + t z : z} = targets[t] for t = 0, 1, 2, or None."""
    for g in ALL_MAPS:
        if all({(g[z] + t * z) % 3 for z in range(3)} == targets[t] for t in range(3)):
            return g
    return None


def lift(maps, n, col):
    """Lemma 160.  Returns (maps of a sticky family in F_3^(n+1), its good colouring)."""
    new = dict(maps)
    for d in itertools.product(range(3), repeat=n):
        if not any(d):
            new[d] = (0, 0, 0)                    # the vertical line over P(0) is {P(0)} x F_3
            continue
        targets = [set(COLS[col[q]]) for q in line_points(maps, d)]
        g = label_for(targets)
        if g is None:
            raise ValueError("colouring is not good on direction %r" % (d,))
        new[d] = g
    p0 = P_of(maps, (0,) * n)
    c0 = col[p0]
    newcol = {}
    for q in kakeya_set(new, n + 1):
        p, gam = q[:n], q[n]
        if p == p0 and gam not in COLS[c0]:
            newcol[q] = (c0 + 1) % 3
        else:
            newcol[q] = col[p]
    return new, newcol


def lifted_sizes(nmax=7):
    maps, col, n = family_K4(), colouring_K4(), 4
    out = {4: len(kakeya_set(maps, 4))}
    while n < nmax:
        maps, col = lift(maps, n, col)
        n += 1
        out[n] = len(kakeya_set(maps, n))
    return out


# ----------------------------------------------------------------------------- results


def results():
    T = tree_T()
    S = slices(T, 3)
    K3 = kakeya_set(family_K3(), 3)
    K4 = kakeya_set(family_K4(), 4)
    planes = [sum(1 for p in K4 if p[0] == u) for u in range(3)]
    sizes = lifted_sizes(7)
    return {
        "note": "a187",
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "n4": {
            "size": len(K4),
            "classical_size": len(kakeya_set(classical_maps(4), 4)),
            "proved_lower_bound_a186": 29,
            "K_prime_size": len(K3),
            "K_prime_union_hidden_slice": len(K3 | S[2]),
            "T_slice_sizes": [len(S[t]) for t in range(3)],
            "T_game_vector": list(game_vector(T, 3)),
            "plane_sizes": planes,
            "formula_size": formula_size(family_K3(), T, 2, (0, 0, 0), 3),
            "points": [list(p) for p in sorted(K4)],
        },
        "lifted_sizes": {str(n): s for n, s in sorted(sizes.items())},
        "classical_sizes": {str(n): 2 ** (n + 1) - 1 for n in range(4, 8)},
        "formula": "U*(n) <= 31 * 2^(n-4) - 1 for n >= 4",
    }


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "sticky_break.json"
    with open(out, "w") as fh:
        json.dump(results(), fh, indent=1)
