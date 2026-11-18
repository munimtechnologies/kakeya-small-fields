# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Note a180: Kakeya sets over F_3 from the Katz-Tao sum-difference inequality.

Theorem 68 (notes/a180.md): every Kakeya set K in F_3^n has |K|^11 >= (3^n - 1)^6,
so |K| >= 3^(6n/11 - o(n)) = 1.82074...^n, above the polynomial-method base 9/5.
Corollary 68.1: every map P of F_3^k has Lambda(P) <= (15/11) k log2 3, i.e.

    prod over t in F_3 and over the fibres of Y_t = P(X) + tX of c^c  <=  3^(15 k 3^k / 11),

checked here as the exact integer inequality prod^11 <= 3^(15 k 3^k).

Standard library only; self-contained (no other repo module is imported).
"""
import itertools
import math
import random


def entropy(weights):
    """Shannon entropy in bits of the distribution proportional to the given weights."""
    vals = list(weights.values()) if isinstance(weights, dict) else list(weights)
    tot = float(sum(vals))
    return -sum((v / tot) * math.log2(v / tot) for v in vals if v > 0)


def marginal(joint, f):
    out = {}
    for key, w in joint.items():
        k2 = f(key)
        out[k2] = out.get(k2, 0) + w
    return out


def vadd(a, b, m):
    return tuple((u + v) % m for u, v in zip(a, b))


def vsub(a, b, m):
    return tuple((u - v) % m for u, v in zip(a, b))


def group_elements(m, d):
    """All elements of (Z_m)^d as tuples."""
    return list(itertools.product(range(m), repeat=d))


def kt_slack(joint, m):
    """4H(X) + 4H(Y) + 3H(X+Y) - 5H(X,Y) - H(X-Y) for (X, Y) on (Z_m)^d.

    joint maps (x, y) (two tuples) to a positive weight. Lemma 143 (Katz-Tao, entropy
    form) says this is >= 0 in every abelian group."""
    hxy = entropy(joint)
    hx = entropy(marginal(joint, lambda k: k[0]))
    hy = entropy(marginal(joint, lambda k: k[1]))
    hs = entropy(marginal(joint, lambda k: vadd(k[0], k[1], m)))
    hd = entropy(marginal(joint, lambda k: vsub(k[0], k[1], m)))
    return 4 * hx + 4 * hy + 3 * hs - 5 * hxy - hd


def random_joint(m, d, support, rng):
    elems = group_elements(m, d)
    joint = {}
    for _ in range(support):
        key = (rng.choice(elems), rng.choice(elems))
        joint[key] = joint.get(key, 0) + rng.randint(1, 9)
    return joint


def f3_vectors(k):
    return group_elements(3, k)


def fibre_product(P, k):
    """Exact integer prod over t in F_3 and over the fibres of Y_t = P(X) + tX of c^c.

    P maps each vector of F_3^k (a tuple) to a vector. log2 of the result is
    S(P) = 3^k Lambda(P)."""
    prod = 1
    vecs = f3_vectors(k)
    for t in range(3):
        cnt = {}
        for x in vecs:
            y = tuple((p + t * u) % 3 for p, u in zip(P[x], x))
            cnt[y] = cnt.get(y, 0) + 1
        for c in cnt.values():
            prod *= c ** c
    return prod


def satisfies_corollary_68_1(P, k):
    """Exact form of Lambda(P) <= (15/11) k log2 3."""
    return fibre_product(P, k) ** 11 <= 3 ** (15 * k * 3 ** k)


def frame_map(k):
    return {x: tuple((u * u) % 3 for u in x) for x in f3_vectors(k)}


def random_map(k, rng):
    vecs = f3_vectors(k)
    return {x: rng.choice(vecs) for x in vecs}


def is_kakeya_f3(K, n):
    """True iff K (a set of tuples in F_3^n) contains a line in every direction."""
    for d in f3_vectors(n):
        if not any(d):
            continue
        if not any(vadd(a, d, 3) in K and vadd(vadd(a, d, 3), d, 3) in K for a in K):
            return False
    return True


def theorem_68_holds(size, n):
    """Exact form of |K| >= (3^n - 1)^(6/11)."""
    return size ** 11 >= (3 ** n - 1) ** 6


def beats_bukh_chao(n):
    """Exact: (3^n - 1)^(6/11) > 3^n / (5/3)^(n-1) = 3^(2n-1) / 5^(n-1)."""
    return (3 ** n - 1) ** 6 * 5 ** (11 * (n - 1)) > 3 ** (11 * (2 * n - 1))


def first_n_beating_bukh_chao(limit=200):
    for n in range(1, limit + 1):
        if beats_bukh_chao(n):
            return n
    return None


if __name__ == "__main__":
    print("3^(6/11) =", 3 ** (6 / 11))
    print("first n where (3^n-1)^(6/11) beats Bukh-Chao:", first_n_beating_bukh_chao())
