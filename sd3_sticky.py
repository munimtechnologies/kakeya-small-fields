# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Note a182: Conjecture R3 holds in dimension one, survives extensions, and so holds
for every triangular ("sticky") configuration in every F_3^N.

A configuration in F_3^N is a law mu on directions d with a base point P(d) for each
direction; its slices are Y_t = P(D) + t D (t in F_3). Conjecture R3 (note a181) says
    H(D) <= (R0 / 3) * sum_t H(Y_t),   R0 = log 27 / log(27/4),
equivalently (since each Y_t is a function of D)
    sum_t H(D | Y_t) <= C3 * H(D),     C3 = 3 - 3/R0 = log 4 / log 3.

Theorem 70 (N = 1): R3 holds for every configuration in F_3 (any law, any map).
  Its core is Lemma 148: G(p) = sum_i psi(1 - p_i) - C_TRI psi(p_i) >= 0 on the simplex,
  C_TRI = log(9/4)/log 3. Proof ingredients checked here: triangle_gap, phi, phi_prime,
  m_func, U_STAR, u_root.
Theorem 71 (extensions): if a linear quotient of the configuration is again a
  configuration (the map descends) and the quotient and all fibres satisfy R3, so does
  the whole. With Theorem 70 this gives R3 for every triangular configuration:
  coordinate j of P(d) depends only on d_1..d_j (is_triangular, random_triangular).
Proposition 77 (robust form): for any map and any random variables Z_j such that
  P_j(D) is a function of (D_1..D_j, Z_j),
  sum_t H(D | Y_t) <= C3 H(D) + 3 sum_j H(Z_j | D_<j).
  defect_terms evaluates the choice Z_j = P_j(D); triangular maps allow Z_j constant.
Standard library only; self-contained.
"""

import itertools
import math

LOG3 = math.log(3.0)
R0 = math.log(27.0) / math.log(27.0 / 4.0)            # 1.7259824...
C3 = 2.0 * math.log(2.0) / math.log(3.0)              # 3 - 3/R0 = 1.2618595...
C_TRI = math.log(9.0 / 4.0) / math.log(3.0)           # 3/R0 - 1 = 0.7381405...
U_STAR = C_TRI / (1.0 - C_TRI)                        # 2.818842..., minimum of m_func


def psi(x):
    """-x log x, with psi(0) = 0."""
    return 0.0 if x <= 0.0 else -x * math.log(x)


def triangle_gap(p):
    """G(p) = sum_i psi(1 - p_i) - C_TRI * psi(p_i) for a law p on three points.
    Lemma 148: G >= 0 on the simplex, zero only at the vertices and the uniform law."""
    return sum(psi(1.0 - x) - C_TRI * psi(x) for x in p)


def phi(a):
    """G restricted to the segment (a, a, 1 - 2a), 0 <= a <= 1/2."""
    return triangle_gap((a, a, 1.0 - 2.0 * a))


def m_func(u):
    """M(u) = log((1 + u)/2) - C_TRI log u for u > 0. phi'(a) = 2 M((1 - 2a)/a)."""
    return math.log((1.0 + u) / 2.0) - C_TRI * math.log(u)


def phi_prime(a):
    """Closed form of phi'(a) for 0 < a < 1/2."""
    return 2.0 * m_func((1.0 - 2.0 * a) / a)


def u_root(lo=None, hi=100.0, iters=200):
    """The zero u1 of M on (U_STAR, infinity), by bisection (M(U_STAR) < 0 < M(100))."""
    lo = U_STAR if lo is None else lo
    flo = m_func(lo)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        fm = m_func(mid)
        if (fm < 0.0) == (flo < 0.0):
            lo, flo = mid, fm
        else:
            hi = mid
    return 0.5 * (lo + hi)


# ---------------------------------------------------------------- configurations

def f3_vectors(k):
    return list(itertools.product(range(3), repeat=k))


def entropy(weights):
    """Shannon entropy in nats of the law proportional to the given weights."""
    vals = list(weights.values()) if isinstance(weights, dict) else list(weights)
    tot = float(sum(vals))
    return -sum((float(v) / tot) * math.log(float(v) / tot) for v in vals if v > 0)


def slice_value(base, d, t):
    return tuple((b + t * x) % 3 for b, x in zip(base, d))


def joint_entropy(config, fn):
    """Entropy of fn(d, base) under the configuration's law (zero weights ignored)."""
    law = {}
    for d, (b, w) in config.items():
        if w > 0:
            k = fn(d, b)
            law[k] = law.get(k, 0.0) + float(w)
    return entropy(law)


def r3_terms(config):
    """(H(D), sum_t H(D | Y_t)). R3 says the second is at most C3 times the first."""
    hd = joint_entropy(config, lambda d, b: d)
    lost = sum(hd - joint_entropy(config, lambda d, b, t=t: slice_value(b, d, t))
               for t in range(3))
    return hd, lost


def r3_slack(config):
    """C3 * H(D) - sum_t H(D | Y_t); R3 is the statement that this is >= 0."""
    hd, lost = r3_terms(config)
    return C3 * hd - lost


def ruzsa_product(n):
    """rho^n: base point d o d (coordinatewise square), uniform law."""
    w = 1.0 / 3 ** n
    return {d: (tuple((x * x) % 3 for x in d), w) for d in f3_vectors(n)}


def n1_merge_slices(pmap):
    """For a map P: F_3 -> F_3 (tuple P(0), P(1), P(2)), the list over the pairs
    (0,1), (0,2), (1,2) of the slices t in which the pair has equal values."""
    out = []
    for d, e in ((0, 1), (0, 2), (1, 2)):
        out.append([t for t in range(3)
                    if (pmap[d] + t * d) % 3 == (pmap[e] + t * e) % 3])
    return out


def is_triangular(config):
    """True if, on the support, coordinate j of P(d) depends only on d_1..d_j."""
    n = len(next(iter(config)))
    for j in range(n):
        seen = {}
        for d, (b, w) in config.items():
            if w <= 0:
                continue
            if seen.setdefault(d[:j + 1], b[j]) != b[j]:
                return False
    return True


def random_triangular(n, rng, zero_prob=0.0):
    """A random triangular configuration on F_3^n with random (skewed) weights."""
    tables = [dict() for _ in range(n)]
    config = {}
    for d in f3_vectors(n):
        b = tuple(tables[j].setdefault(d[:j + 1], rng.randrange(3)) for j in range(n))
        w = 0.0 if rng.random() < zero_prob else rng.random() ** 3
        config[d] = (b, w)
    if all(w <= 0 for (_, w) in config.values()):
        d0 = next(iter(config))
        config[d0] = (config[d0][0], 1.0)
    return config


def random_map_config(n, rng, zero_prob=0.0):
    """A configuration with a uniformly random map P (not necessarily triangular)."""
    config = {}
    for d in f3_vectors(n):
        b = tuple(rng.randrange(3) for _ in range(n))
        w = 0.0 if rng.random() < zero_prob else rng.random() ** 3
        config[d] = (b, w)
    if all(w <= 0 for (_, w) in config.values()):
        d0 = next(iter(config))
        config[d0] = (config[d0][0], 1.0)
    return config


def apply_linear(config, mat):
    """Push a configuration through an invertible 3-ary matrix (rows of mat)."""
    def mul(v):
        return tuple(sum(r * x for r, x in zip(row, v)) % 3 for row in mat)
    return {mul(d): (mul(b), w) for d, (b, w) in config.items()}


def chain_terms(config):
    """(sum_t H(D|Y_t), sum_t sum_j H(D_j | Y_t,j, D_<j)). The first is at most the
    second for every configuration; for triangular ones Theorem 70 bounds the second
    by C3 H(D) (proof of Theorem 71)."""
    n = len(next(iter(config)))
    _, lost = r3_terms(config)
    mid = 0.0
    for t in range(3):
        for j in range(n):
            h_all = joint_entropy(config, lambda d, b, j=j, t=t:
                                  (d[:j + 1], (b[j] + t * d[j]) % 3))
            h_cond = joint_entropy(config, lambda d, b, j=j, t=t:
                                   (d[:j], (b[j] + t * d[j]) % 3))
            mid += h_all - h_cond
    return lost, mid


def defect_terms(config):
    """sum_j H(P_j(D) | D_<j): the defect of Proposition 77 for the choice Z_j = P_j(D)."""
    n = len(next(iter(config)))
    total = 0.0
    for j in range(n):
        total += (joint_entropy(config, lambda d, b, j=j: (d[:j], b[j]))
                  - joint_entropy(config, lambda d, b, j=j: d[:j]))
    return total


def invariant_functionals(config):
    """Nonzero functionals phi (first nonzero coefficient 1) such that phi(P(d)) is a
    function of phi(d) on the support. In F_3^2 the configuration is reducible
    (Theorem 71 applies) exactly when this list is nonempty."""
    n = len(next(iter(config)))
    out = []
    for f in f3_vectors(n):
        nz = [x for x in f if x]
        if not nz or nz[0] != 1:
            continue
        seen = {}
        ok = True
        for d, (b, w) in config.items():
            if w <= 0:
                continue
            k = sum(a * x for a, x in zip(f, d)) % 3
            v = sum(a * x for a, x in zip(f, b)) % 3
            if seen.setdefault(k, v) != v:
                ok = False
                break
        if ok:
            out.append(f)
    return out


def pair_maps_invariant_count(a, b):
    """Number of pairs (f, g) of maps F_3 -> F_3 such that a f(x) + b g(y) is a function
    of a x + b y (a, b nonzero). Used for the triple intersections in the count of
    reducible maps of F_3^2; the answer is 27 (f, g affine with a common slope)."""
    funcs = list(itertools.product(range(3), repeat=3))
    count = 0
    for f in funcs:
        for g in funcs:
            seen = {}
            ok = True
            for x in range(3):
                for y in range(3):
                    k = (a * x + b * y) % 3
                    v = (a * f[x] + b * g[y]) % 3
                    if seen.setdefault(k, v) != v:
                        ok = False
            if ok:
                count += 1
    return count


def reducible_count_f3_2():
    """Maps P: F_3^2 -> F_3^2 (full support) with an invariant line, by inclusion-exclusion
    over the 4 lines: 4*3^12 - 6*3^6 + 4*27 - 27."""
    return 4 * 3 ** 12 - 6 * 3 ** 6 + 4 * 27 - 27


def binary_kakeya(n):
    """{0,1}^n union {0,2}^n, a Kakeya set of size 2^(n+1) - 1 whose lines
    d o d + F_3 d form a triangular (diagonal) configuration."""
    pts = set()
    for v in itertools.product((0, 1), repeat=n):
        pts.add(v)
        pts.add(tuple(2 * x for x in v))
    return pts


if __name__ == "__main__":
    u1 = u_root()
    print("R0", R0, "C3", C3, "C_TRI", C_TRI)
    print("U_STAR", U_STAR, "M(U_STAR)", m_func(U_STAR), "u1", u1, "a1", 1.0 / (u1 + 2.0))
    print("reducible maps of F_3^2:", reducible_count_f3_2(), "of", 9 ** 9)
