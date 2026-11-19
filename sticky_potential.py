# sticky_potential.py -- Theorem 72 (note a183): every sticky Kakeya set in F_3^n has
# |K| >= 1.90499^n - 1, above the KLSS growth base 3 * 2^(-2/3) = 1.889882 of the smallest
# known Kakeya sets over F_3.
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# No human mathematician has checked the proof yet. Licence: Apache-2.0.
#
# Setting (Lemma 149, notes/prereg-sticky-front.md): a sticky configuration in F_3^n is a ternary
# tree of depth n. Every node is AFFINE with a constant slice s or a TRIANGLE with a bijection
# iso: slice -> isolated child. Vectors L in R^3 are built from the leaves (1, 1, 1) by
#   affine(s):  L_s = max_x L_s(x),            L_t = sum_x L_t(x)  (t != s)
#   triangle:   L_t = L_t(iso(t)) + max_{x != iso(t)} L_t(x)
# and every sticky Kakeya set K has |K| >= max_t L_t(root) - 1.
#
# Lemma 153 (potential). For 0 <= c <= 1/2 put
#   phi_c(v) = (1 + c) * sum_t log v_t - 3c * max_t log v_t.
# At every node, for ANY positive child vectors,
#   phi_c(parent) >= lambda(c, u) + min_x phi_c(child_x),
#   lambda(c, u) = min( (2 - c) log 3 ,  2(1 + c) h2(u) + (1 - 2c) h2(1 - 2u) ),  0 < u < 1/2,
# where h2 is the binary entropy in nats. Since phi_c(1,1,1) = 0 and phi_c(v) <= 3 log max v,
# max_t L_t(root) >= exp(lambda h / 3) for a tree of height h (Theorem 72).
# With c = 0.24, u = 0.38: lambda = 1.9334406 > log(27/4) = 1.9095425, base 1.9049966.
#
# Stdlib only. Running this file writes results/sticky_potential_bound.json.

import itertools
import json
import math
import os
import sys

C_STAR = 0.24
U_STAR = 0.38
LN3 = math.log(3.0)
LEAF = (1, 1, 1)

# Reference growth bases (per coordinate, i.e. |K| ~ base^n), all from earlier notes or KLSS.

def _a180_base():
    """a180 (Theorem 68): |K| >= (3^n - 1)^(6/11), base 3^(6/11)."""
    return 3.0 ** (6.0 / 11.0)


BASE_ALL_KAKEYA_LOWER_A180 = _a180_base()
BASE_KLSS = 3.0 * 2.0 ** (-2.0 / 3.0)          # KLSS Theorem 8 at q = 3, = (27/4)^(1/3)
BASE_STICKY_LOWER_A182 = (27.0 / 4.0) ** (1.0 / 3.0)  # Corollary 71.3
BASE_STICKY_UPPER = 2.0                          # {0,1}^n u {0,2}^n


def h2(x):
    """Binary entropy in nats."""
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -x * math.log(x) - (1.0 - x) * math.log(1.0 - x)


def affine_rate(c):
    """Guaranteed growth of phi_c at an affine node: (2 - c) log 3."""
    return (2.0 - c) * LN3


def triangle_rate(c, u):
    """Guaranteed growth of phi_c at a triangle node with child weights (u, u, 1 - 2u)."""
    return 2.0 * (1.0 + c) * h2(u) + (1.0 - 2.0 * c) * h2(1.0 - 2.0 * u)


def rate(c=C_STAR, u=U_STAR):
    return min(affine_rate(c), triangle_rate(c, u))


def base(c=C_STAR, u=U_STAR):
    """Per-coordinate growth base exp(lambda / 3) guaranteed by Theorem 72."""
    return math.exp(rate(c, u) / 3.0)


def phi(v, c=C_STAR):
    logs = [math.log(x) for x in v]
    return (1.0 + c) * sum(logs) - 3.0 * c * max(logs)


# ----- the selection game --------------------------------------------------------------------

def affine(children, s):
    p = []
    for t in range(3):
        vals = [ch[t] for ch in children]
        p.append(max(vals) if t == s else sum(vals))
    return tuple(p)


def triangle(children, iso=(0, 1, 2)):
    p = []
    for t in range(3):
        i = iso[t]
        others = [children[x][t] for x in range(3) if x != i]
        p.append(children[i][t] + max(others))
    return tuple(p)


def all_parents(children):
    """Every parent vector a node with these (ordered) children can have: 3 affine + 6 triangles."""
    out = [affine(children, s) for s in range(3)]
    out.extend(triangle(children, iso) for iso in itertools.permutations(range(3)))
    return out


def node_gain(children, c=C_STAR):
    """min over node types of phi(parent) - min_x phi(child_x)."""
    lo = min(phi(ch, c) for ch in children)
    return min(phi(p, c) - lo for p in all_parents(children))


def leq(a, b):
    return a[0] <= b[0] and a[1] <= b[1] and a[2] <= b[2]


def pareto_min(vectors):
    front = []
    for v in sorted(set(vectors)):
        if not any(leq(f, v) for f in front):
            front.append(v)
    return front


def pareto_min_fast(vectors):
    """Same result as pareto_min for positive integer vectors (Fenwick tree of prefix minima of
    the 3rd coordinate over the 2nd; lexicographic order puts every v' <= v, v' != v, before v)."""
    pts = sorted(set(vectors))
    if not pts:
        return []
    ymax = max(v[1] for v in pts)
    inf = float("inf")
    tree = [inf] * (ymax + 2)
    front = []
    for v in pts:
        i, best = v[1] + 1, inf
        while i > 0:
            if tree[i] < best:
                best = tree[i]
            i -= i & -i
        if best <= v[2]:
            continue
        front.append(v)
        i = v[1] + 1
        while i < len(tree):
            if v[2] < tree[i]:
                tree[i] = v[2]
            i += i & -i
    return front


def next_level(vectors):
    """All parent vectors over ordered triples (identity bijection covers every triangle)."""
    out = set()
    for ch in itertools.product(vectors, repeat=3):
        out.add(triangle(ch))
        for s in range(3):
            out.add(affine(ch, s))
    return out


def fronts(hmax):
    """Exact Pareto fronts (componentwise minimal achievable vectors) for h = 0..hmax."""
    fr = [[LEAF]]
    for _ in range(hmax):
        fr.append(pareto_min_fast(next_level(fr[-1])))
    return fr


# ----- results file --------------------------------------------------------------------------

def results():
    lam = rate()
    return {
        "theorem": "a183 Theorem 72: every sticky Kakeya set in F_3^n has |K| >= exp(lambda n / 3) - 1",
        "potential": "phi_c(v) = (1 + c) sum_t log v_t - 3 c max_t log v_t",
        "c": C_STAR,
        "u": U_STAR,
        "affine_rate": round(affine_rate(C_STAR), 9),
        "triangle_rate": round(triangle_rate(C_STAR, U_STAR), 9),
        "lambda": round(lam, 9),
        "log_27_over_4": round(math.log(27.0 / 4.0), 9),
        "gain_over_entropy_bound": round(lam - math.log(27.0 / 4.0), 9),
        "base_new_sticky_lower": round(math.exp(lam / 3.0), 9),
        "bases": [
            {"label": "All Kakeya sets, best lower bound (a180)",
             "value": round(BASE_ALL_KAKEYA_LOWER_A180, 6)},
            {"label": "Smallest known Kakeya sets (KLSS upper bound)",
             "value": round(BASE_KLSS, 6)},
            {"label": "Sticky sets, earlier lower bound (a182)",
             "value": round(BASE_STICKY_LOWER_A182, 6)},
            {"label": "Sticky sets, new lower bound (a183)",
             "value": round(math.exp(lam / 3.0), 6)},
            {"label": "Best sticky construction",
             "value": BASE_STICKY_UPPER},
        ],
        "made_with": "AI agents working in the name of MV2 of Munim, Inc.; no human has checked the proof",
    }


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join("results", "sticky_potential_bound.json")
    d = os.path.dirname(out)
    if d:
        os.makedirs(d, exist_ok=True)
    with open(out, "w") as fh:
        json.dump(results(), fh, indent=1)
    print(json.dumps(results(), indent=1))
