# sticky_minmax.py -- note a184: the min-plus-max criterion for the sticky selection game over F_3,
# the exact value f(3) = 8, and why finite up-set certificates cannot certify any base above sqrt(3).
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only, self-contained.
#
# The game (a182, notes/prereg-sticky-front.md, Lemma 149): vectors L in Z^3 indexed by slices
# t in F_3.  Leaf: (1, 1, 1).
#   affine(s):  L_s = max_x L_s(x),   L_t = sum_x L_t(x)  (t != s)
#   triangle:   L_t = L_t(iso(t)) + max_{x != iso(t)} L_t(x)   (iso a bijection)
# A_h = vectors reachable at height h; f(h) = min over A_h of max_t L_t.

import itertools
import json
import sys

LEAF = (1, 1, 1)


def affine(children, s):
    p = []
    for t in range(3):
        vals = [c[t] for c in children]
        p.append(max(vals) if t == s else sum(vals))
    return tuple(p)


def triangle(children, iso=(0, 1, 2)):
    p = []
    for t in range(3):
        i = iso[t]
        others = [children[x][t] for x in range(3) if x != i]
        p.append(children[i][t] + max(others))
    return tuple(p)


def leq(a, b):
    return a[0] <= b[0] and a[1] <= b[1] and a[2] <= b[2]


def pareto_min(vectors):
    """Minimal elements in the componentwise order (sorted lexicographically)."""
    front = []
    for v in sorted(set(vectors)):
        if not any(leq(f, v) for f in front):
            front.append(v)
    return front


def next_front(front, U=None):
    """Minimal vectors one level up.  Children range over the front (enough, since every node is
    monotone); ordered triples with the identity bijection cover all six triangle bijections."""
    out = []
    for c in itertools.product(front, repeat=3):
        for p in (triangle(c), affine(c, 0), affine(c, 1), affine(c, 2)):
            if U is None or max(p) <= U:
                out.append(p)
    return pareto_min(out)


def fronts(hmax, U=None):
    fr = [[LEAF]]
    for _ in range(hmax):
        fr.append(next_front(fr[-1], U))
    return fr


def min_plus_max(v):
    return min(v) + max(v)


def cyclic_children(v):
    """Lemma 154 / Proposition 79: three slice relabellings of v.  Child x carries the smallest
    value of v at slot x, the middle value at slot x+1 and the largest at slot x+2 (mod 3).
    The triangle with iso = identity over them gives (min + max) in every slice."""
    m, mid, M = sorted(v)
    kids = []
    for x in range(3):
        c = [0, 0, 0]
        c[x % 3], c[(x + 1) % 3], c[(x + 2) % 3] = m, mid, M
        kids.append(tuple(c))
    return kids


def zero_chain(g, beta_num, beta_den, steps):
    """Proposition 81: start from g = (0, y, z).  Two affine steps (constant slices 1 then 2) send
    (0, y, z) to (0, 3y, 3z) over two levels.  Returns the sequence of exact parent vectors divided
    by beta^2 per double step, as fractions (num, den) of the original coordinates."""
    from fractions import Fraction
    b = Fraction(beta_num, beta_den)
    cur = tuple(Fraction(x) for x in g)
    seq = [cur]
    for _ in range(steps):
        p1 = affine([cur] * 3, 1)
        p2 = affine([p1] * 3, 2)
        cur = tuple(x / (b * b) for x in p2)
        seq.append(cur)
    return seq


# Hand-derived height-2 front (note a184, Proposition 80): permutations of six shapes.
SHAPES_H2 = [(4, 4, 4), (3, 5, 5), (2, 6, 6), (1, 9, 9), (3, 3, 9), (3, 4, 8)]


def perms(v):
    return sorted(set(tuple(v[p[t]] for t in range(3)) for p in itertools.permutations(range(3))))


def hand_front_h2():
    out = []
    for s in SHAPES_H2:
        out.extend(perms(s))
    return sorted(out)


def results():
    fr = fronts(2)
    f3_low = next_front(fr[2], U=7)          # every height-3 vector with max <= 7 (none)
    f3_eight = next_front(fr[2], U=8)
    return {
        "note": "a184",
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "front_sizes": {"1": len(fr[1]), "2": len(fr[2])},
        "front_h1": [list(v) for v in fr[1]],
        "front_h2_shapes": [list(s) for s in SHAPES_H2],
        "f": {"0": 1, "1": min(max(v) for v in fr[1]), "2": min(max(v) for v in fr[2]),
              "3": min(max(v) for v in f3_eight)},
        "height3_vectors_with_max_at_most_7": len(f3_low),
        "min_plus_max": {"0": 2, "1": min(min_plus_max(v) for v in fr[1]),
                         "2": min(min_plus_max(v) for v in fr[2])},
        "minplusmax_line_h2": [list(v) for v in fr[2] if min_plus_max(v) == 8 and v[0] <= v[1] == v[2]],
        "sqrt3_threshold": 3 ** 0.5,
        "a183_base": 1.904997,
    }


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "sticky_minmax.json"
    with open(out, "w") as fh:
        json.dump(results(), fh, indent=1)
