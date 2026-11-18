# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Pre-registered annealing search over ALL maps P : F_q^k -> F_q^k.

The entropy Kakeya functional of the program (README, a159-a175) is

    Lambda(P) = sum over t in F_q of H(X | P(X) + tX)     (bits, X uniform on F_q^k).

Conjecture C_q(k): Lambda(P) <= k(q - 1) for EVERY map P. Frame products (P(x) = x o x)
reach equality. A map with Lambda(P) > k(q - 1) would refute C_q(k). By Theorem 2 of the
README (beta_q = q 2^(-lambda*/q)) it would then give Kakeya sets in F_q^n smaller than
the frame-product sets for all large n. C_3(2) is settled for all maps (branch and bound,
README). The first open cases are (q, k) = (3, 3) and (5, 2).

The search cannot prove C_q(k). A null result is evidence only. A hit is certified EXACTLY
by `exact_compare`. Since S(P) = q^k Lambda(P) = sum over t and over the fibres of n log2 n,
S(P) > k(q-1) q^k is equivalent to the integer inequality
prod over t and fibres of n^n > 2^(k(q-1) q^k).

Standard library only. Only prime q is supported. Vectors of F_q^k are encoded as integers
x = sum_i x_i q^i.
"""
import argparse
import json
import math
import os
import random
import sys
import time

PRIMES = (3, 5, 7, 11, 13)


class Space:
    """F_q^k with lookup tables (q prime, q^k <= 729)."""

    def __init__(self, q, k):
        if q not in PRIMES:
            raise ValueError("only prime q in %s" % (PRIMES,))
        if k < 1 or q ** k > 729:
            raise ValueError("need 1 <= k and q^k <= 729")
        self.q, self.k = q, k
        self.N = N = q ** k
        self.pw = [q ** i for i in range(k)]
        self.digits = [self.dig(x) for x in range(N)]
        D = self.digits
        self.add = [[self.enc([(u + v) % q for u, v in zip(D[a], D[b])]) for b in range(N)]
                    for a in range(N)]
        self.scal = [[self.enc([(t * u) % q for u in D[x]]) for x in range(N)] for t in range(q)]
        self.neg = self.scal[q - 1]
        self.flog = [0.0] + [n * math.log2(n) for n in range(1, N + 1)]

    def dig(self, x):
        d = []
        for _ in range(self.k):
            d.append(x % self.q)
            x //= self.q
        return d

    def enc(self, d):
        return sum(di * p for di, p in zip(d, self.pw))

    def frame_map(self):
        """P(x) = x o x (coordinatewise squares)."""
        q = self.q
        return [self.enc([(u * u) % q for u in self.digits[x]]) for x in range(self.N)]

    def random_map(self, rng):
        return [rng.randrange(self.N) for _ in range(self.N)]


def slice_counts(sp, P, t):
    c = {}
    for x in range(sp.N):
        y = sp.add[P[x]][sp.scal[t][x]]
        c[y] = c.get(y, 0) + 1
    return c


def score(sp, P):
    """S(P) = q^k Lambda(P) = sum_t sum_fibres n log2 n (fast tables)."""
    return sum(sp.flog[n] for t in range(sp.q) for n in slice_counts(sp, P, t).values())


def lam(sp, P):
    return score(sp, P) / sp.N


def lambda_bruteforce(q, k, P):
    """Independent recomputation of Lambda(P) with tuples (no tables from Space)."""
    vecs = []
    for x in range(q ** k):
        d, y = [], x
        for _ in range(k):
            d.append(y % q)
            y //= q
        vecs.append(tuple(d))
    total = 0.0
    for t in range(q):
        cnt = {}
        for x, xv in enumerate(vecs):
            pv = vecs[P[x]]
            key = tuple((pv[i] + t * xv[i]) % q for i in range(k))
            cnt[key] = cnt.get(key, 0) + 1
        total += sum(n * math.log2(n) for n in cnt.values())
    return total / (q ** k)


def exact_compare(sp, P):
    """Sign of S(P) - k(q-1)q^k, computed in exact integer arithmetic."""
    prod = 1
    for t in range(sp.q):
        for n in slice_counts(sp, P, t).values():
            prod *= n ** n
    ref = 1 << (sp.k * (sp.q - 1) * sp.N)
    return (prod > ref) - (prod < ref)


def is_quadratic(sp, P, samples=None, rng=None):
    """True iff every coordinate of P has total degree <= 2 (all third differences vanish;
    valid for prime q >= 3). Exhaustive if samples is None, else a random sample."""
    N, add = sp.N, sp.add

    def third(x, a, b, c):
        s = [0] * sp.k
        for mask in range(8):
            y = x
            if mask & 1:
                y = add[y][a]
            if mask & 2:
                y = add[y][b]
            if mask & 4:
                y = add[y][c]
            sign = -1 if bin(mask).count("1") % 2 else 1
            d = sp.digits[P[y]]
            for i in range(sp.k):
                s[i] += sign * d[i]
        return all(v % sp.q == 0 for v in s)

    if samples is None:
        return all(third(x, a, b, c) for x in range(N) for a in range(N)
                   for b in range(N) for c in range(N))
    rng = rng or random.Random(0)
    return all(third(rng.randrange(N), rng.randrange(N), rng.randrange(N), rng.randrange(N))
               for _ in range(samples))


class State:
    """Map P with incrementally maintained fibre counts for every slice t."""

    def __init__(self, sp, P):
        self.sp = sp
        self.P = list(P)
        q, N = sp.q, sp.N
        self.v = [[sp.add[self.P[x]][sp.scal[t][x]] for x in range(N)] for t in range(q)]
        self.c = [[0] * N for _ in range(q)]
        for t in range(q):
            ct = self.c[t]
            for y in self.v[t]:
                ct[y] += 1
        self.S = self.recompute()

    def recompute(self):
        fl = self.sp.flog
        return sum(fl[n] for ct in self.c for n in ct)

    def delta(self, x, p):
        sp, fl = self.sp, self.sp.flog
        d = 0.0
        for t in range(sp.q):
            a = self.v[t][x]
            b = sp.add[p][sp.scal[t][x]]
            if a != b:
                ct = self.c[t]
                ca, cb = ct[a], ct[b]
                d += fl[ca - 1] - fl[ca] + fl[cb + 1] - fl[cb]
        return d

    def apply(self, x, p, d):
        sp = self.sp
        for t in range(sp.q):
            a = self.v[t][x]
            b = sp.add[p][sp.scal[t][x]]
            if a != b:
                self.c[t][a] -= 1
                self.c[t][b] += 1
                self.v[t][x] = b
        self.P[x] = p
        self.S += d

    def join_value(self, x, y, t):
        """The value p with p + t x = P(y) + t y (puts x into the t-fibre of y)."""
        sp = self.sp
        return sp.add[self.P[y]][sp.scal[t][sp.add[y][sp.neg[x]]]]


def anneal(sp, rng, steps, start, T0=2.0, T1=0.02):
    """Metropolis annealing on S(P). Moves: join (x joins the t-fibre of a random y),
    one-coordinate change of P(x), or a uniformly random new value P(x).
    Returns (best S, best map)."""
    st = State(sp, start)
    best, bestP = st.S, list(st.P)
    N, q, k = sp.N, sp.q, sp.k
    ratio = (T1 / T0) ** (1.0 / max(1, steps))
    T = T0
    for i in range(steps):
        T *= ratio
        x = rng.randrange(N)
        r = rng.random()
        if r < 0.5:
            y = rng.randrange(N)
            if y == x:
                continue
            p = st.join_value(x, y, rng.randrange(q))
        elif r < 0.85:
            p = sp.add[st.P[x]][rng.randrange(1, q) * sp.pw[rng.randrange(k)]]
        else:
            p = rng.randrange(N)
        if p == st.P[x]:
            continue
        d = st.delta(x, p)
        if d >= 0 or rng.random() < math.exp(d / T):
            st.apply(x, p, d)
            if st.S > best + 1e-9:
                best, bestP = st.S, list(st.P)
        if i % 100000 == 99999:
            st.S = st.recompute()
    return score(sp, bestP), bestP


def perturbed_frame(sp, rng, frac):
    P = sp.frame_map()
    for x in range(sp.N):
        if rng.random() < frac:
            P[x] = rng.randrange(sp.N)
    return P


def fibre_profile(sp, P):
    """For each t, the multiset of fibre sizes as a sorted list of [size, count]."""
    out = []
    for t in range(sp.q):
        h = {}
        for n in slice_counts(sp, P, t).values():
            h[n] = h.get(n, 0) + 1
        out.append(sorted([s, c] for s, c in h.items()))
    return out


def run_case(q, k, minutes, seed, out_dir, log=print):
    sp = Space(q, k)
    target = k * (q - 1)
    rng = random.Random(seed)
    steps = max(200000, 4000 * sp.N)
    t_end = time.time() + 60.0 * minutes
    finals, best, bestP, restarts = [], -1.0, None, 0
    kinds = ["random", "frame10", "frame30", "zero"]
    while time.time() < t_end or restarts < 2:
        kind = kinds[restarts % len(kinds)]
        if kind == "random":
            start = sp.random_map(rng)
        elif kind == "frame10":
            start = perturbed_frame(sp, rng, 0.10)
        elif kind == "frame30":
            start = perturbed_frame(sp, rng, 0.30)
        else:
            start = [0] * sp.N
        S, P = anneal(sp, rng, steps, start)
        restarts += 1
        finals.append([kind, round(S / sp.N, 9)])
        if S > best:
            best, bestP = S, P
        log("q=%d k=%d restart %d (%s): Lambda %.6f  best %.6f  target %d"
            % (q, k, restarts, kind, S / sp.N, best / sp.N, target))
    lam_fast = best / sp.N
    lam_brute = lambda_bruteforce(q, k, bestP)
    cmp_exact = exact_compare(sp, bestP)
    res = {
        "q": q, "k": k, "N": sp.N, "target_k_q_minus_1": target, "restarts": restarts,
        "steps_per_restart": steps, "seed": seed, "minutes": minutes,
        "best_lambda_fast": lam_fast, "best_lambda_bruteforce": lam_brute,
        "exact_compare_best_vs_target": cmp_exact,
        "restarts_reaching_target": sum(1 for _, v in finals if v >= target - 1e-6),
        "final_lambdas": finals,
        "best_is_quadratic_sampled": is_quadratic(sp, bestP, samples=20000,
                                                  rng=random.Random(seed + 1)),
        "best_fibre_profile": fibre_profile(sp, bestP),
        "best_map": bestP,
    }
    if out_dir:
        with open(os.path.join(out_dir, "anneal_q%d_k%d.json" % (q, k)), "w") as f:
            json.dump(res, f)
        if cmp_exact > 0:
            with open(os.path.join(out_dir, "HIT_q%d_k%d.json" % (q, k)), "w") as f:
                json.dump({"q": q, "k": k, "lambda": lam_brute, "map": bestP,
                           "note": "exact_compare > 0: refutes C_q(k)"}, f)
    return res


DEFAULT_CASES = [(3, 3, 35), (3, 4, 30), (5, 2, 20), (5, 3, 15), (3, 5, 15), (7, 2, 10),
                 (3, 6, 15)]


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--scale", type=float, default=1.0, help="multiply every time budget")
    ap.add_argument("--seed", type=int, default=20261118)
    a = ap.parse_args(argv)
    os.makedirs(a.out_dir, exist_ok=True)
    summary = []
    for i, (q, k, minutes) in enumerate(DEFAULT_CASES):
        r = run_case(q, k, minutes * a.scale, a.seed + 1000 * i, a.out_dir,
                     log=lambda s: print(s, flush=True))
        summary.append({key: r[key] for key in (
            "q", "k", "target_k_q_minus_1", "restarts", "best_lambda_fast",
            "best_lambda_bruteforce", "exact_compare_best_vs_target",
            "restarts_reaching_target", "best_is_quadratic_sampled")})
        with open(os.path.join(a.out_dir, "anneal_summary.json"), "w") as f:
            json.dump(summary, f, indent=1)
    hits = [s for s in summary if s["exact_compare_best_vs_target"] > 0]
    print("HITS:", hits if hits else "none")
    return 0


if __name__ == "__main__":
    sys.exit(main())
