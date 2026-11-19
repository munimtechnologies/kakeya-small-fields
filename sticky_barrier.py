# sticky_barrier.py -- note a185: the potential barrier for the sticky selection game over F_3,
# and why Conjecture S2 (f(h) = 2^h for every h) is false.
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# No human mathematician has checked the proofs yet. Licence: Apache-2.0.
# Stdlib only, self-contained.
#
# The game (a182, a183, a184): vectors L indexed by slices t in F_3, leaf (1, 1, 1),
#   affine(s):  L_s = max_x L_s(x),  L_t = sum_x L_t(x)  (t != s)
#   triangle:   L_t = L_t(iso(t)) + max_{x != iso(t)} L_t(x)   (iso a bijection)
# f(h) = min over trees of height h of max_t L_t(root); beta_s = lim f(h)^(1/h).
#
# Proposition 82 (barrier). Let phi on log-vectors be monotone, satisfy phi(l + s(1,1,1)) =
# phi(l) + s, and grow by mu at every node: phi(parent) >= mu + min_x phi(child_x) for ALL
# positive real children. Then mu <= mu_star, where, for a probability vector beta,
#   A(beta) = (1 - max_t beta_t) log 3                      (affine trees with equal children)
#   V(beta) = max_{w in simplex} sum_t beta_t h2(w_t)      (triangle trees, Lemma 157)
#   mu_star = max_beta min(A(beta), V(beta)) = 0.644488...,  base e^mu_star = 1.905012...
# Theorem 73. mu_star < log 2, so Conjecture S2 is false: beta_s < 2.
#
# This file computes the finite-dimensional quantities in those statements and the explicit
# "tight" configurations used in the proof. Running it writes results/sticky_barrier.json.

import json
import math
import os
import sys

LN2 = math.log(2.0)
LN3 = math.log(3.0)
B0 = 1.0 - LN2 / LN3          # A(beta) >= log 2 forces max beta <= B0 = 0.36907 < 1/2


def h2(x):
    """Binary entropy in nats (0 at the end points)."""
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -x * math.log(x) - (1.0 - x) * math.log(1.0 - x)


def _logistic(z):
    """1 / (1 + e^z) without overflow."""
    if z > 700.0:
        return 0.0
    if z < -700.0:
        return 1.0
    return 1.0 / (1.0 + math.exp(z))


def kkt_weights(beta, iters=200):
    """For beta with every entry > 0: the maximiser w of sum_t beta_t h2(w_t) on the simplex.
    It is interior and satisfies beta_t log((1 - w_t) / w_t) = nu for every t, i.e.
    w_t = 1 / (1 + exp(nu / beta_t)); nu > 0 is found by bisection so that sum_t w_t = 1."""
    if min(beta) <= 0.0:
        raise ValueError("kkt_weights needs every beta_t > 0")
    lo, hi = 0.0, 60.0 * max(beta)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if sum(_logistic(mid / b) for b in beta) > 1.0:
            lo = mid
        else:
            hi = mid
    nu = 0.5 * (lo + hi)
    return nu, [_logistic(nu / b) for b in beta]


def V(beta):
    """max over probability vectors w of sum_t beta_t h2(w_t)."""
    if min(beta) <= 0.0:
        # at most two slots carry weight; w = 1/2 on each of them is optimal
        return sum(beta) * LN2
    _, w = kkt_weights(beta)
    return sum(b * h2(x) for b, x in zip(beta, w))


def affine_bound(beta):
    """A(beta) = (1 - max_t beta_t) log 3."""
    return (1.0 - max(beta)) * LN3


def mu(beta):
    """The largest growth per level that a potential with local weights beta can have."""
    return min(affine_bound(beta), V(beta))


def beta_c(c):
    """a183's family phi_c = (1 + c) sum log - 3c max log, divided by 3: weight (1 - 2c)/3 on the
    slot of the largest coordinate (index 0 here) and (1 + c)/3 on the other two."""
    return ((1.0 - 2.0 * c) / 3.0, (1.0 + c) / 3.0, (1.0 + c) / 3.0)


def optimum(iters=100):
    """mu_star: maximise min(A, V) over the family beta_c (Proposition 82 shows the family is
    enough). A decreases and V increases in c, so bisect on the sign of A - V."""
    lo, hi = 0.0, 0.5
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        b = beta_c(mid)
        if affine_bound(b) > V(b):
            lo = mid
        else:
            hi = mid
    c = 0.5 * (lo + hi)
    b = beta_c(c)
    m = mu(b)
    _, w = kkt_weights(b)
    return {"c": c, "u": w[1], "mu": m, "lambda": 3.0 * m, "base": math.exp(m)}


# ----- the game and the tight configurations of the proof -------------------------------------

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


def triangle_children(p, r):
    """Children for which the triangle with iso = identity gives back exactly p: child x has
    r_x p_x in slot x and (1 - r_t) p_t in each other slot t (0 < r_t < 1)."""
    return [tuple(r[t] * p[t] if t == x else (1.0 - r[t]) * p[t] for t in range(3))
            for x in range(3)]


def linear_phi(beta, v):
    return sum(b * math.log(x) for b, x in zip(beta, v))


def triangle_gaps(beta, r):
    """phi_beta(p) - phi_beta(child_x) for the children of triangle_children(p, r); it does not
    depend on p. Slot x contributes -beta_x log r_x, slot t != x contributes -beta_t log(1 - r_t)."""
    out = []
    for x in range(3):
        g = 0.0
        for t in range(3):
            g += beta[t] * (-math.log(r[t]) if t == x else -math.log(1.0 - r[t]))
        out.append(g)
    return out


def cross_entropy(w, r):
    return -w * math.log(r) - (1.0 - w) * math.log(1.0 - r)


# ----- results file ----------------------------------------------------------------------------

def results():
    opt = optimum()
    vertex = V((B0, B0, 1.0 - 2.0 * B0))
    a183 = beta_c(0.24)
    a183_lambda = min((2.0 - 0.24) * LN3,
                      2.48 * h2(0.38) + 0.52 * h2(0.24))   # a183's fixed u = 0.38
    return {
        "note": "a185",
        "made_with": "AI agents working in the name of MV2 of Munim, Inc.; no human has checked the proofs",
        "proposition_82": "a monotone potential with phi(l + s) = phi(l) + s that grows by mu at every "
                          "node of the sticky selection game has mu <= mu_star",
        "theorem_73": "Conjecture S2 is false: the sticky selection game over F_3 has growth constant "
                      "beta_s < 2",
        "c_star": round(opt["c"], 6),
        "u_star": round(opt["u"], 6),
        "mu_star": round(opt["mu"], 6),
        "lambda_star": round(opt["lambda"], 6),
        "base_star": round(opt["base"], 6),
        "ln2": round(LN2, 6),
        "affine_threshold_b0": round(B0, 6),
        "vertex_V_at_b0": round(vertex, 6),
        "product_potential_V": round(V((1 / 3.0, 1 / 3.0, 1 / 3.0)), 6),
        "a183_lambda": round(a183_lambda, 6),
        "a183_base": round(math.exp(a183_lambda / 3.0), 6),
        "a183_family_mu_at_c_0_24": round(mu(a183), 6),
        "bases": [
            {"label": "a182 sticky lower bound", "value": round((27.0 / 4.0) ** (1.0 / 3.0), 6)},
            {"label": "a183 sticky lower bound", "value": round(math.exp(a183_lambda / 3.0), 6)},
            {"label": "Barrier for all potentials", "value": round(opt["base"], 6)},
            {"label": "Classical sticky construction", "value": 2.0},
        ],
    }


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join("results", "sticky_barrier.json")
    d = os.path.dirname(out)
    if d:
        os.makedirs(d, exist_ok=True)
    with open(out, "w") as fh:
        json.dump(results(), fh, indent=1)
    print(json.dumps(results(), indent=1))
