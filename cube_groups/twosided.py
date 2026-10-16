# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for robust-cubes-v5p (draft for kakeya-small-fields 1.7): two-sided peeling and class sizes.

Lemma 34 (two-sided cube). With w_i = A d_i A^-1,
    A d_1^(t_1) ... d_r^(t_r) = w_1^(t_1) ... w_r^(t_r) A,
so the cube can be peeled losslessly from the right (last d) or from the left (first w). Any
"outside-in" word x_1, ..., x_(r-1) (each x_i is the last remaining d or the first remaining w) gives
    sum_t H(Y_t) >= H(A, d) + sum_(i < r) (2^(r-i) - 1) H(x_i | x_1, ..., x_(i-1)),
for EVERY random (A, d) in EVERY finite group. For r = 3: H(A, d) + 2 H(x_1) + H(x_1, x_2) with
(x_1, x_2) in {(d_3, d_2), (d_3, w_1), (w_1, d_3), (w_1, w_2)}.

Theorem 34 (class sizes). Every lossy pair c = s^-1 d_j s loses H(d_j | c) <= log b(G), where b(G)
is the largest conjugacy class size, and b(G) <= |G'|. So |G'| may be replaced by b(G) in
Theorems 9', 25, 27, 29, 29' and Proposition 28 (L g L = union of (l g l^-1) L, so |LgL| <= |L| b).
S_4: b = 8 < |G'| = 12. Free class-2 exponent-3 group on 3 generators: b = 9 < |G'| = 27.

Also checked: in Proposition 6(b)'s G(p, k), the right stabiliser of K is H, and H is core-free.

    python twosided.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os
import random
from collections import defaultdict

from prop31_cubes import closure, cube_in, generated, groups, inverses, perm_group, table_from


# ---- more groups ---------------------------------------------------------------------------

def gpk(p, k):
    """G(p, k) of Proposition 6(b): (e, h, z)(e', h', z') = (e + e', h + h', z + z' + e h')."""
    vecs = list(itertools.product(range(p), repeat=k))
    elems = [(e, h, z) for e in range(p) for h in vecs for z in vecs]

    def mul(a, b):
        return ((a[0] + b[0]) % p, tuple((x + y) % p for x, y in zip(a[1], b[1])),
                tuple((x + y + a[0] * v) % p for x, y, v in zip(a[2], b[2], b[1])))
    return elems, table_from(elems, mul)


def free_class2_exp3():
    """Free nilpotent class-2 group of exponent 3 on 3 generators, order 3^6 = 729."""
    pairs = ((0, 1), (0, 2), (1, 2))
    vecs = list(itertools.product(range(3), repeat=3))
    elems = [(x, z) for x in vecs for z in vecs]

    def mul(a, b):
        return (tuple((u + v) % 3 for u, v in zip(a[0], b[0])),
                tuple((a[1][n] + b[1][n] + a[0][i] * b[0][j]) % 3 for n, (i, j) in enumerate(pairs)))
    return table_from(elems, mul)


def agl(q, root):
    return perm_group([tuple(root * x % q for x in range(q)), tuple((x + 1) % q for x in range(q))])


def commutator_subgroup(T):
    inv, n = inverses(T), len(T)
    comms = {T[T[T[inv[a]][inv[b]]][a]][b] for a in range(n) for b in range(n)}
    return generated(T, comms)


def max_class(T):
    inv, n = inverses(T), len(T)
    return max(len({T[T[g][x]][inv[g]] for g in range(n)}) for x in range(n))


def right_stabiliser(T, K):
    return frozenset(y for y in range(len(T)) if frozenset(T[k][y] for k in K) == K)


def core(T, H):
    inv, out = inverses(T), set(H)
    for g in range(len(T)):
        out &= {T[T[g][h]][inv[g]] for h in H}
    return frozenset(out)


def gpk_stabiliser(p, k, S):
    """Returns (|Stab_R(K)|, Stab_R(K) == H, |core|) for Proposition 6(b)'s K = {(t, h, t h) : t in S}."""
    elems, T = gpk(p, k)
    index = {x: n for n, x in enumerate(elems)}
    vecs = list(itertools.product(range(p), repeat=k))
    zero = tuple([0] * k)
    H = frozenset(index[(0, h, zero)] for h in vecs)
    K = frozenset(index[(t, h, tuple(t * x % p for x in h))] for t in S for h in vecs)
    R = right_stabiliser(T, K)
    return len(R), R == H, len(core(T, R))


# ---- entropies of laws on (A, d_1, ..., d_r) ------------------------------------------------

def entropy(law, f):
    acc = defaultdict(float)
    for p, o in law:
        acc[f(o)] += p
    return -sum(p * math.log2(p) for p in acc.values() if p > 0)


def cube_points(T, o):
    pts = [o[0]]
    for x in o[1:]:
        pts = pts + [T[y][x] for y in pts]
    return pts                                  # index = t_1 + 2 t_2 + 4 t_3 + ...


def conj(T, inv, A, x):
    return T[T[A][x]][inv[A]]


def schemes(T, law):
    """Left side and the outside-in right sides (r = 2 or 3), plus the 'wrong' d_1-first side."""
    inv = inverses(T)
    r = len(law[0][1]) - 1
    lhs = sum(entropy(law, lambda o, n=n: cube_points(T, o)[n]) for n in range(2 ** r))
    total = entropy(law, lambda o: o)
    d = lambda i: (lambda o: o[i])
    w = lambda i: (lambda o: conj(T, inv, o[0], o[i]))
    if r == 2:
        sides = {"2R": total + entropy(law, d(2)), "1L": total + entropy(law, w(1))}
        wrong = total + entropy(law, d(1))
    else:
        words = {"3R2R": (d(3), d(2)), "3R1L": (d(3), w(1)), "1L3R": (w(1), d(3)), "1L2L": (w(1), w(2))}
        sides = {k: total + 2 * entropy(law, f) + entropy(law, lambda o, f=f, g=g: (f(o), g(o)))
                 for k, (f, g) in words.items()}
        wrong = total + 2 * entropy(law, d(1)) + entropy(law, lambda o: (o[1], o[2]))
    return lhs, sides, wrong


def class_losses(T, law):
    """(H(d_1 | c), H(d_1 | w_1)) for r = 2, with c = d_2^-1 d_1 d_2 and w_1 = A d_1 A^-1."""
    inv = inverses(T)
    c = lambda o: conj(T, inv, inv[o[2]], o[1])
    w1 = lambda o: conj(T, inv, o[0], o[1])
    h = lambda f: entropy(law, lambda o: (f(o), o[1])) - entropy(law, f)
    return h(c), h(w1)


def random_law(n, r, rng, size):
    support = [tuple(rng.randrange(n) for _ in range(r + 1)) for _ in range(size)]
    weights = [rng.random() for _ in support]
    s = sum(weights)
    return [(x / s, o) for x, o in zip(weights, support)]


def design_law(T, K, D):
    """Uniform on D, with the first base point A in K whose left cube lies in K."""
    law = []
    for d in D:
        A = next(A for A in sorted(K) if cube_in(T, K, A, d))
        law.append((1 / len(D), (A,) + d))
    return law


def agl_design(q, root, r):
    """AGL(1, q), K = H u (x -> x + 1) H, D = G x H^(r-1) (Proposition 5(b))."""
    T = agl(q, root)
    L = generated(T, (1,))
    K = L | frozenset(T[2][l] for l in L)
    D = [(g,) + h for g in range(len(T)) for h in itertools.product(sorted(L), repeat=r - 1)]
    return T, K, D


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    rng, report = random.Random(1), {}

    named = dict(groups())
    named["S_4"] = perm_group([(1, 0, 2, 3), (1, 2, 3, 0)])
    named["free2(3,3)"] = free_class2_exp3()
    sizes = {}
    for name, T in named.items():
        sizes[name] = {"order": len(T), "derived": len(commutator_subgroup(T)), "b": max_class(T)}
        print(f"{name}: |G| = {len(T)}, |G'| = {sizes[name]['derived']}, b = {sizes[name]['b']}")
    report["class_sizes"] = sizes

    worst, wrong_hits, loss_ok = {}, {}, True
    for name in ("S_3", "D_4", "Q_8", "A_4", "S_4", "AGL(1,5)"):
        T = named[name]
        logb = math.log2(sizes[name]["b"])
        least, hits = float("inf"), 0
        for trial in range(1500):
            r = 2 + trial % 2
            law = random_law(len(T), r, rng, rng.choice((3, 6, 12, 30)))
            lhs, sides, wrong = schemes(T, law)
            least = min(least, min(lhs - v for v in sides.values()))
            hits += lhs < wrong - 1e-9
            if r == 2:
                hc, hw = class_losses(T, law)
                loss_ok &= hc <= logb + 1e-9 and hw <= logb + 1e-9
        worst[name], wrong_hits[name] = least, hits
        print(f"{name}: least slack of the outside-in schemes {least:.6f}; "
              f"random laws breaking the d_1-first side: {hits}")
    report["random_least_slack"] = worst
    report["random_wrong_hits"] = wrong_hits
    report["class_loss_within_log_b"] = loss_ok

    controls = []
    for q, root, r in ((5, 2, 2), (5, 2, 3), (7, 3, 2), (17, 3, 2)):
        T, K, D = agl_design(q, root, r)
        lhs, sides, wrong = schemes(T, design_law(T, K, D))
        controls.append({"q": q, "r": r, "lhs": lhs, "sides": sides, "wrong": wrong,
                         "cap": 2 ** r * math.log2(len(K))})
        print(f"AGL(1,{q}) r={r}: sum H(Y_t) = {lhs:.4f} (cap {2 ** r * math.log2(len(K)):.4f}), "
              f"d_1-first side {wrong:.4f}, outside-in min {min(sides.values()):.4f}")
    report["agl_controls"] = controls

    stab = {}
    for p, k, S in ((2, 1, (0, 1)), (2, 2, (0, 1)), (3, 1, (0, 1)), (3, 2, (0, 1)),
                    (5, 1, (0, 1, 2)), (7, 1, (0, 1, 3))):
        size, is_h, c = gpk_stabiliser(p, k, S)
        stab[f"{p},{k}"] = {"stab": size, "equals_H": is_h, "core": c}
        print(f"G({p},{k}): |Stab_R(K)| = {size}, equals H: {is_h}, |core| = {c}")
    report["gpk_stabiliser"] = stab
    with open(os.path.join(args.out_dir, "twosided.json"), "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
