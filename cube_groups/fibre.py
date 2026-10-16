# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Checks for robust-cubes-v5r (draft for kakeya-small-fields 1.7): Theorem 36 (fibre losses) and
Proposition 37 (tensor Heisenberg groups: b(G) is not the right loss, the fibre count is).
Y_t = A d_1^(t_1) ... d_r^(t_r), [a, b] = a^-1 b^-1 a b, b(G) = the largest conjugacy class size.

Peeling with fibre losses. Peel the indices in the order sigma. When j is peeled, its pairs are
(Y, Y c) with c = c_(j,T) = s^-1 d_j s, s = the product of d_i over T (the unpeeled i > j that are
"on" in the pair). Such a pair loses at most H(d_j | c_(j,T)), so for every random (A, d):
    sum_t H(Y_t) >= H(A, d) + sum_(m < r) (2^(r-m) - 1) H(x_m | x_1..x_(m-1)) - sum_pairs H(d_j | c_(j,T)),
x_m = d_(sigma_m). Theorem 36 (set form): with beta_(j,T)(D) = max over c of the number of d_j
values, d in D, with c_(j,T)(d) = c,
    r = 2:  |K|^8 beta_(1,2) >= |D|^3,
    r = 3:  |K|^24 beta_(1,2) beta_(1,3)^2 beta_(1,23) beta_(2,3)^2 >= |D|^7.
beta_(j,T) <= |{[d_j, s]}| (Theorem 29') and <= max_g |g^L|, L = <d_i : i in T> (<= b(G), Theorem 34).
Proposition 37: Gamma(p; j, k) = F_p^j x F_p^k x (F_p^j (x) F_p^k), S = {0, e_1, ..., e_j},
K = {(t, h, t (x) h) : t in S}, H = {(0, h, 0)}, D = (K^-1 K) x H^(r-1). Then |K| = (j + 1) p^k,
|K^-1 K| = N p^(2k) + p^k (N = j(j+1)/2 for p = 2, j^2 + j for p odd), beta_(1,2) = p^k,
|[d_1, d_2] values| = (j(j+1)/2)(p^k - 1) + 1, b(G) = p^(j+k-1), |G'| = p^(jk). For j = k the b form
is off by p^(k-1); in Gamma(3; 4, 4) the abelian r = 2 bound |K|^8 >= |D|^3 genuinely fails.

    python fibre.py --out-dir OUT
"""
import argparse
import itertools
import json
import math
import os
import random
from collections import defaultdict


# ---- small groups as multiplication tables on 0..n-1, identity 0 ----------------------------

def closure(gens, mul, identity):
    elems, seen, frontier = [identity], {identity}, [identity]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in seen:
                    seen.add(y)
                    new.append(y)
                    elems.append(y)
        frontier = new
    return elems


def table_from(elems, mul):
    index = {x: n for n, x in enumerate(elems)}
    return [[index[mul(a, b)] for b in elems] for a in elems]


def perm_mul(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def perm_group(gens):
    identity = tuple(range(len(gens[0])))
    return table_from(closure(gens, perm_mul, identity), perm_mul)


def quat_mul(u, v):
    a1, b1, c1, d1 = u
    a2, b2, c2, d2 = v
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2, a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2, a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


def agl(q, root):
    return perm_group([tuple(root * x % q for x in range(q)), tuple((x + 1) % q for x in range(q))])


def small_groups():
    q8 = closure([(0, 1, 0, 0), (0, 0, 1, 0)], quat_mul, (1, 0, 0, 0))
    return {"S_3": perm_group([(1, 0, 2), (1, 2, 0)]),
            "D_4": perm_group([(1, 2, 3, 0), (0, 3, 2, 1)]),
            "Q_8": table_from(q8, quat_mul),
            "A_4": perm_group([(1, 2, 0, 3), (0, 2, 3, 1)]),
            "S_4": perm_group([(1, 0, 2, 3), (1, 2, 3, 0)]),
            "AGL(1,5)": agl(5, 2)}


def inverses(T):
    return [row.index(0) for row in T]


def generated(T, gens):
    return frozenset(closure(list(gens), lambda a, b: T[a][b], 0))


def max_class(T):
    inv, n = inverses(T), len(T)
    return max(len({T[T[g][x]][inv[g]] for g in range(n)}) for x in range(n))


# ---- entropies and the peeling inequality ---------------------------------------------------

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


def cube_in(T, K, A, d):
    return all(y in K for y in cube_points(T, (A,) + tuple(d)))


def cube_sum(T, law):
    r = len(law[0][1]) - 1
    return sum(entropy(law, lambda o, n=n: cube_points(T, o)[n]) for n in range(2 ** r))


def lossy_pairs(r, sigma):
    """(j, T) for every pair of the order sigma whose suffix T (unpeeled i > j that are on) is non-empty."""
    out, unpeeled = [], set(range(1, r + 1))
    for j in sigma:
        others = sorted(unpeeled - {j})
        for bits in itertools.product((0, 1), repeat=len(others)):
            on = tuple(i for i, b in zip(others, bits) if b and i > j)
            if on:
                out.append((j, on))
        unpeeled.remove(j)
    return out


def c_value(T, inv, o, j, on):
    """c_(j,T) = s^-1 d_j s with s = prod_(i in T) d_i; o = (A, d_1, ..., d_r)."""
    s = 0
    for i in on:
        s = T[s][o[i]]
    return T[T[inv[s]][o[j]]][s]


def order_main(law, sigma):
    r, total, prev = len(sigma), entropy(law, lambda o: o), 0.0
    for m in range(1, r):
        cur = entropy(law, lambda o, m=m: tuple(o[i] for i in sigma[:m]))
        total += (2 ** (r - m) - 1) * (cur - prev)
        prev = cur
    return total


def order_slack(T, law, sigma, lhs=None):
    """sum_t H(Y_t) - (main term - fibre losses) for the order sigma; must be >= 0."""
    inv = inverses(T)
    lhs = cube_sum(T, law) if lhs is None else lhs
    loss = 0.0
    for j, on in lossy_pairs(len(sigma), sigma):
        cf = lambda o, j=j, on=on: c_value(T, inv, o, j, on)
        loss += entropy(law, lambda o, cf=cf, j=j: (cf(o), o[j])) - entropy(law, cf)
    return lhs - order_main(law, sigma) + loss


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
        law.append((1 / len(D), (A,) + tuple(d)))
    return law


# ---- set forms: fibres against commutator sets and b(G) -------------------------------------

FIBRE_TERMS = {2: ((1, (2,), 1),), 3: ((1, (2,), 1), (1, (3,), 2), (1, (2, 3), 1), (2, (3,), 2))}


def served_all(T, K, r):
    inv, out = inverses(T), set()
    for A in K:
        right = sorted(T[inv[A]][k] for k in K)
        for d in itertools.product(right, repeat=r):
            if d not in out and cube_in(T, K, A, d):
                out.add(d)
    return out


def fibre(T, D, j, on):
    inv, seen = inverses(T), defaultdict(set)
    for d in D:
        seen[c_value(T, inv, (0,) + tuple(d), j, on)].add(d[j - 1])
    return max(len(v) for v in seen.values())


def gamma(T, D, j, on):
    """Number of values of [d_j, s] = d_j^-1 c_(j,T)."""
    inv, vals = inverses(T), set()
    for d in D:
        o = (0,) + tuple(d)
        vals.add(T[inv[o[j]]][c_value(T, inv, o, j, on)])
    return len(vals)


def set_form(T, K, D, r, b):
    """(fibre form holds, its log2 slack, every fibre <= its commutator count and <= b)."""
    prod, dominated = 1, True
    for j, on, m in FIBRE_TERMS[r]:
        f = fibre(T, D, j, on)
        dominated &= f <= gamma(T, D, j, on) and f <= b
        prod *= f ** m
    a, c = r * 2 ** r, 2 ** r - 1
    slack = a * math.log2(len(K)) + math.log2(prod) - c * math.log2(len(D))
    return len(K) ** a * prod >= len(D) ** c, slack, dominated


def set_search(T, rng, r, sets=None, subsamples=3):
    n, b = len(T), max_class(T)
    masks = range(1, 2 ** n) if sets is None else [rng.randrange(1, 2 ** n) for _ in range(sets)]
    out = {"sets": 0, "violations": 0, "not_dominated": 0, "least_slack": None, "subsets_checked": 0}
    for mask in masks:
        K = frozenset(x for x in range(n) if mask >> x & 1)
        D = sorted(served_all(T, K, r))
        if not D:
            continue
        families = [D] + [rng.sample(D, rng.randint(1, len(D))) for _ in range(subsamples if len(D) > 1 else 0)]
        for fam in families:
            ok, slack, dom = set_form(T, K, fam, r, b)
            out["sets" if fam is D else "subsets_checked"] += 1
            out["violations"] += not ok
            out["not_dominated"] += not dom
            if out["least_slack"] is None or slack < out["least_slack"][0]:
                out["least_slack"] = (round(slack, 9), sorted(K), len(fam))
    return out


def random_laws(T, rng, r, trials):
    """Least order slack over random laws and laws on cubes inside random sets."""
    n, least = len(T), float("inf")
    orders = list(itertools.permutations(range(1, r + 1)))
    for trial in range(trials):
        if trial % 2:
            law = random_law(n, r, rng, rng.choice((2, 4, 8, 16)))
        else:
            K = frozenset(rng.sample(range(n), rng.randint(2, n)))
            D = sorted(served_all(T, K, r))
            law = design_law(T, K, rng.sample(D, rng.randint(1, min(len(D), 24))))
        lhs = cube_sum(T, law)
        least = min(least, min(order_slack(T, law, s, lhs) for s in orders))
    return least


def agl_control(q=17, root=3):
    """AGL(1, 17), K = L u (x -> x + 1) L, D = G x L: the d_1-first side fails without its loss."""
    T = agl(q, root)
    L = generated(T, (1,))
    K = L | frozenset(T[2][l] for l in L)
    D = [(g, l) for g in range(len(T)) for l in sorted(L)]
    law = design_law(T, K, D)
    lhs = cube_sum(T, law)
    no_loss = entropy(law, lambda o: o) + entropy(law, lambda o: o[1])
    ok, slack, dom = set_form(T, K, D, 2, max_class(T))
    return {"K": len(K), "D": len(D), "lhs": lhs, "T_plus_H_d1": no_loss, "fails_without_loss": lhs < no_loss - 1e-9,
            "slack_12_with_fibre_loss": order_slack(T, law, (1, 2), lhs), "fibre": fibre(T, D, 1, (2,)),
            "set_form_holds": ok, "set_form_slack": slack, "dominated": dom}


# ---- Proposition 37: tensor Heisenberg groups, as tuples (no tables) ------------------------

class Tensor:
    """Gamma(p; j, k): (e, h, z)(e', h', z') = (e + e', h + h', z + z' + e (x) h'), z indexed n = a k + l."""

    def __init__(self, p, j, k):
        self.p, self.j, self.k = p, j, k
        self.one = (tuple([0] * j), tuple([0] * k), tuple([0] * (j * k)))

    def ten(self, e, h):
        return tuple(e[n // self.k] * h[n % self.k] % self.p for n in range(self.j * self.k))

    def mul(self, a, b):
        p, t = self.p, self.ten(a[0], b[1])
        return (tuple((x + y) % p for x, y in zip(a[0], b[0])), tuple((x + y) % p for x, y in zip(a[1], b[1])),
                tuple((x + y + w) % p for x, y, w in zip(a[2], b[2], t)))

    def inv(self, a):
        p, t = self.p, self.ten(a[0], a[1])
        return (tuple(-x % p for x in a[0]), tuple(-x % p for x in a[1]),
                tuple((w - x) % p for x, w in zip(a[2], t)))

    def comm(self, a, b):
        return self.mul(self.mul(self.inv(a), self.inv(b)), self.mul(a, b))

    def conj(self, s, x):
        return self.mul(self.mul(self.inv(s), x), s)          # s^-1 x s

    def vectors(self, m):
        return list(itertools.product(range(self.p), repeat=m))

    def elements(self):
        return [(e, h, z) for e in self.vectors(self.j) for h in self.vectors(self.k)
                for z in self.vectors(self.j * self.k)]


def unit(m, i):
    return tuple(int(n == i) for n in range(m))


def rank_mod_p(rows, p):
    rows, rank = [list(r) for r in rows], 0
    for c in range(len(rows[0]) if rows else 0):
        piv = next((i for i in range(rank, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        f = pow(rows[rank][c], p - 2, p)
        rows[rank] = [x * f % p for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][c] % p:
                g = rows[i][c]
                rows[i] = [(x - g * y) % p for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def class_rank(G, e, h, only_h=False):
    """dim of {[(e, h, .), g]}: g ranges over G, or over H = {(0, h', 0)} if only_h."""
    rows = [G.ten(e, unit(G.k, l)) for l in range(G.k)]
    if not only_h:
        rows += [tuple(-x % G.p for x in G.ten(unit(G.j, i), h)) for i in range(G.j)]
    return rank_mod_p(rows, G.p)


def b_values(G):
    """(b(G), max_g |g^H|) from the ranks of the commutator maps (the group has class 2)."""
    b = max(class_rank(G, e, h) for e in G.vectors(G.j) for h in G.vectors(G.k))
    bh = max(class_rank(G, e, None, True) for e in G.vectors(G.j))
    return G.p ** b, G.p ** bh


def brute_b(G):
    elems = G.elements()
    return max(len({G.conj(g, x) for g in elems}) for x in elems)


def predicted(p, j, k):
    N = j * (j + 1) // 2 if p == 2 else j * j + j
    return {"K": (j + 1) * p ** k, "K^-1K": N * p ** (2 * k) + p ** k, "beta": p ** k,
            "gamma": j * (j + 1) // 2 * (p ** k - 1) + 1, "b": p ** (j + k - 1), "b_H": p ** k, "derived": p ** (j * k)}


def tensor_design(p, j, k, rng, brute_limit=300000, sample=300):
    G = Tensor(p, j, k)
    S = [G.one[0]] + [unit(j, i) for i in range(j)]
    V = G.vectors(k)
    K = {(t, h, G.ten(t, h)) for t in S for h in V}
    H = [(G.one[0], h, G.one[2]) for h in V]
    kinv = [G.inv(a) for a in K]
    diffs = {G.mul(a, c) for a in kinv for c in K}
    b, bh = b_values(G)
    d1 = (unit(j, 0), G.one[1], G.one[2])                   # (e_1, 0, 0) = 1^-1 (e_1, 0, 0) is in K^-1 K
    explicit = len({G.mul(G.mul(eta, d1), G.inv(eta)) for eta in H} & diffs)
    out = {"p": p, "j": j, "k": k, "K": len(K), "K^-1K": len(diffs), "b": b, "b_H": bh,
           "derived": p ** (j * k), "explicit_fibre": explicit, "predicted": predicted(p, j, k)}
    if len(diffs) * len(H) <= brute_limit:
        fib, comms = defaultdict(set), set()
        for x in diffs:
            for eta in H:
                fib[G.conj(eta, x)].add(x)
                comms.add(G.comm(x, eta))
        out["beta"], out["gamma"] = max(len(v) for v in fib.values()), len(comms)
    else:                                                   # explicit fibre <= beta <= b_H; [d_1, eta] = e (x) h
        out["beta"] = explicit if explicit == bh else None
        out["gamma"] = len({G.ten(e, h) for e in {d[0] for d in diffs} for h in V})
    pts = sorted(diffs)
    unserved = 0
    for _ in range(sample):
        x, eta = rng.choice(pts), rng.choice(H)
        unserved += not any(all(y in K for y in (A, G.mul(A, x), G.mul(A, eta), G.mul(G.mul(A, x), eta)))
                            for A in K)
    out["unserved_in_sample"] = unserved
    kk, d2 = len(K), len(diffs) * len(H)
    d3 = d2 * len(H)
    lk, ld2, ld3 = math.log2(kk), math.log2(d2), math.log2(d3)
    out["slack25"] = {name: 8 * lk + math.log2(m) - 3 * ld2 for name, m in
                      (("abelian", 1), ("beta", out["beta"] or bh), ("gamma", out["gamma"]), ("b", b),
                       ("derived", p ** (j * k)))}
    out["abelian25_fails"] = kk ** 8 < d2 ** 3
    out["beta25_holds"] = kk ** 8 * (out["beta"] or bh) >= d2 ** 3
    out["slack29_beta4"] = 24 * lk + 4 * math.log2(out["beta"] or bh) - 7 * ld3
    out["abelian29_fails"] = kk ** 24 < d3 ** 7
    out["matches"] = all(out[key] == out["predicted"][key] for key in ("K", "K^-1K", "b", "b_H", "gamma")) \
        and out["beta"] == out["predicted"]["beta"] and explicit == p ** k
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    rng, report = random.Random(36), {}
    groups = small_groups()

    laws = {}
    for name, T in groups.items():
        laws[name] = {f"r={r}": random_laws(T, rng, r, 300 if r == 2 else 120) for r in (2, 3)}
        print(f"Theorem 36 per-order inequality {name}: least slack {laws[name]}")
    report["per_order_laws"] = laws

    sets = {}
    for name in ("S_3", "D_4", "Q_8"):
        for r in (2, 3):
            sets[f"{name} r={r}"] = set_search(groups[name], rng, r)
            print(f"Theorem 36 set form, every K in {name}, r={r}: {sets[f'{name} r={r}']}")
    for name in ("A_4", "AGL(1,5)"):
        for r, count in ((2, 500), (3, 60)):
            sets[f"{name} r={r}"] = set_search(groups[name], rng, r, sets=count, subsamples=2)
            print(f"Theorem 36 set form, random K in {name}, r={r}: {sets[f'{name} r={r}']}")
    report["set_forms"] = sets

    report["agl17_control"] = agl_control()
    print(f"AGL(1,17) control: {report['agl17_control']}")

    tensor = {}
    for p, j, k in ((2, 2, 1), (2, 2, 2), (3, 2, 1), (2, 3, 2), (2, 3, 3), (3, 2, 2), (2, 4, 4), (3, 3, 3), (3, 4, 4)):
        res = tensor_design(p, j, k, rng)
        tensor[f"{p},{j},{k}"] = res
        print(f"Proposition 37 Gamma({p}; {j}, {k}): matches {res['matches']}, K {res['K']}, K^-1K {res['K^-1K']}, "
              f"beta {res['beta']}, gamma {res['gamma']}, b {res['b']}, b_H {res['b_H']}, "
              f"unserved {res['unserved_in_sample']}, abelian25_fails {res['abelian25_fails']}, "
              f"beta25_holds {res['beta25_holds']}, slack25 "
              + ", ".join(f"{a} {v:.4f}" for a, v in res["slack25"].items()))
    for p, j, k in ((2, 2, 1), (2, 2, 2), (3, 2, 1)):
        tensor[f"{p},{j},{k}"]["brute_b"] = brute_b(Tensor(p, j, k))
        print(f"brute b(G) Gamma({p}; {j}, {k}) = {tensor[f'{p},{j},{k}']['brute_b']}")
    report["proposition37_tensor"] = tensor

    with open(os.path.join(args.out_dir, "fibre.json"), "w") as f:
        json.dump(report, f, indent=1, default=str)


if __name__ == "__main__":
    main()
