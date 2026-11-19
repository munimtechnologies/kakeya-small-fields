#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""sdz.py -- the Katz-Tao sum-difference constant C_3b over the integers (Erdos problem #1097):
can a genuinely two-dimensional (non-product) law beat the best one-dimensional laws?

Setting. A configuration is a finite law P on pairs g = (x, y) with x, y in Z^k such that
x - y is injective on the support. With H = H(P) = H(X - Y) and the three forms
X, Y, S = X + Y, the ratio alpha(P) = H / max(H(X), H(Y), H(S)) is a lower bound for C_3b
(Ruzsa / Lemm entropy formulation; Lemm, Proc. AMS 143 (2015) 3863-3868). Since
P (x) P^T (swap x and y) has entropies (2H, H_X + H_Y, H_X + H_Y, 2H_S), the symmetrised
ratio alpha_s(P) = H / max((H_X + H_Y)/2, H_S) is also a lower bound; it is our score.

Known: Ruzsa 1.725982 (3 points), Lemm 1.77898 (7 points on the 'staircase' x + y in {1, 2}),
AlphaEvolve (2025) +1e-8, Mosaic Intelligence (2026) 1.7789888414 (13 points). All of these
are one-dimensional. Upper bound 1.8263483657 (Farnamfar, arXiv:2611.19594).

What this job does (pre-registration: notes/prereg-sdz.md):
  E0  evaluates Lemm's printed weights (sanity).
  E1  optimises the weights on staircases of 5..15 points (calibration: >= 1.778980 at 7).
  E2  tensor test: for the optimum p on a staircase S, (a) the second-order operator
      T = sum_j lambda_j (A_j (x) A_j) on mean-zero (x) mean-zero functions, A_j = E[ . | form j],
      lambda = KKT weights; the product p (x) p is NOT a local maximum on S x S iff
      alpha * Lambda_max(T) > 1 (kappa > 1); (b) direct optimisation of all weights on S x S.
  E3  simulated annealing over two-dimensional supports: d in a box of Z^2, each d carries a
      sum s(d) of the same parity (x = (d + s)/2, y = (s - d)/2) or is absent.
  E4  the same in one dimension with three admissible sums per difference.
Every reported value is the exact evaluation (50-digit Decimal) of explicit printed weights,
so each one is a valid lower bound for C_3b whatever the optimiser did.

Optimiser. For fixed mu in [0, 1] and the weighted mean M_mu = (1-mu)/2 (H_X + H_Y) + mu H_S,
one minorise-maximise step P_i <- prod_j q_j(form_j(i))^(alpha w_j) (normalised), with
alpha = H(P)/M_mu(P), never decreases H / M_mu (Gibbs' inequality). mu is found by bisection
on the sign of H_S - (H_X + H_Y)/2.

Standard library only.
"""

import argparse
import itertools
import json
import math
import random
import sys
import time
from decimal import Decimal, getcontext
from fractions import Fraction

RUZSA = math.log(27.0) / math.log(27.0 / 4.0)
LEMM_BOUND = 1.77898
LIT_BEST = 1.7789888414206935      # Mosaic Intelligence 2026, 13 points (replayed by Toledo 2026)
RECORD_BAR = 1.7790                # pre-registered bar for RECORD
CALIBRATION_BAR = 1.778980         # the 7-point staircase must reach this
LEMM_P = (0.00024983, 0.028156, 0.22425)
TINY = 1e-300

STAIRS = ((0, 4), (-1, 5), (-2, 6), (-3, 7), (-4, 8), (-5, 9))     # 5, 7, ..., 15 points
TENSOR_STAIRS = ((-1, 5), (-2, 6), (-3, 7), (-4, 8))              # 7, 9, 11, 13 points


# ----------------------------------------------------------------------------- supports
def vadd(a, b):
    return tuple(i + j for i, j in zip(a, b))


def vsub(a, b):
    return tuple(i - j for i, j in zip(a, b))


def staircase(lo, hi):
    """Lemm's staircase: difference d in [lo, hi], sum s = 1 (d odd) or 2 (d even)."""
    pts = []
    for d in range(lo, hi + 1):
        s = 1 if d % 2 else 2
        pts.append((((d + s) // 2,), ((s - d) // 2,)))
    return pts


def lemm_law():
    """Lemm's printed weights on staircase(-1, 5), in the same order."""
    p1, p2, p3 = LEMM_P
    p4 = 1.0 - 2.0 * (p1 + p2 + p3)
    return [p1, p2, p3, p4, p3, p2, p1]


def smap_points(smap):
    """smap: dict difference d (tuple) -> sum s (tuple, same parity). Returns (keys, points)."""
    keys = sorted(smap)
    pts = []
    for d in keys:
        s = smap[d]
        if len(s) != len(d) or any((di - si) % 2 for di, si in zip(d, s)):
            raise ValueError("s must have the parity of d in every coordinate")
        pts.append((tuple((di + si) // 2 for di, si in zip(d, s)),
                    tuple((si - di) // 2 for di, si in zip(d, s))))
    return keys, pts


class Support:
    """Points (x, y) with x - y injective; idx[j][i] = index of form j of point i
    (j = 0: X, 1: Y, 2: S = X + Y)."""

    def __init__(self, pts):
        pts = [(tuple(x), tuple(y)) for x, y in pts]
        if len(set(vsub(x, y) for x, y in pts)) != len(pts):
            raise ValueError("X - Y is not injective on the support")
        self.pts = pts
        self.n = len(pts)
        self.idx = []
        self.sizes = []
        for form in range(3):
            keys = {}
            ix = []
            for x, y in pts:
                if form == 0:
                    k = x
                elif form == 1:
                    k = y
                else:
                    k = vadd(x, y)
                if k not in keys:
                    keys[k] = len(keys)
                ix.append(keys[k])
            self.idx.append(ix)
            self.sizes.append(len(keys))


def product_support(s1, s2):
    return Support([(x1 + x2, y1 + y2) for (x1, y1) in s1.pts for (x2, y2) in s2.pts])


def product_law(p1, p2):
    return [a * b for a in p1 for b in p2]


# ----------------------------------------------------------------------------- entropies
def normalize(ws):
    t = float(sum(ws))
    return [float(w) / t for w in ws]


def ent(ws):
    return -sum(w * math.log(w) for w in ws if w > 0.0)


def project(sup, P, j):
    q = [0.0] * sup.sizes[j]
    ix = sup.idx[j]
    for i in range(sup.n):
        q[ix[i]] += P[i]
    return q


def entropies(sup, P):
    """(H, H_X, H_Y, H_S) in nats."""
    return (ent(P), ent(project(sup, P, 0)), ent(project(sup, P, 1)), ent(project(sup, P, 2)))


def ratio_pair(H, hx, hy, hs):
    """(alpha, alpha_s)."""
    m1 = max(hx, hy, hs)
    m2 = max(0.5 * (hx + hy), hs)
    return (H / m1 if m1 > 0 else 0.0, H / m2 if m2 > 0 else 0.0)


def ratio_mu(sup, P, mu):
    H, hx, hy, hs = entropies(sup, P)
    return H / (0.5 * (1.0 - mu) * (hx + hy) + mu * hs)


def verify(sup, P, digits=50):
    """Exact evaluation of the law proportional to the given (float) weights, read as exact
    binary rationals, with `digits`-digit Decimal logarithms. Returns (alpha, alpha_s) strings."""
    getcontext().prec = digits
    fr = [Fraction(float(p)) for p in P]
    tot = sum(fr)
    ps = [f / tot for f in fr]

    def dent(ws):
        s = Decimal(0)
        for w in ws:
            if w > 0:
                dw = Decimal(w.numerator) / Decimal(w.denominator)
                s -= dw * dw.ln()
        return s

    H = dent(ps)
    hs = []
    for j in range(3):
        q = [Fraction(0)] * sup.sizes[j]
        for i in range(sup.n):
            q[sup.idx[j][i]] += ps[i]
        hs.append(dent(q))
    a = H / max(hs)
    a_s = H / max((hs[0] + hs[1]) / 2, hs[2])
    return str(a), str(a_s)


# ----------------------------------------------------------------------------- optimiser
def mm(sup, P, mu, iters):
    """`iters` minorise-maximise steps for H / M_mu (monotone)."""
    wts = (0.5 * (1.0 - mu), 0.5 * (1.0 - mu), mu)
    n = sup.n
    for _ in range(iters):
        qs = [project(sup, P, j) for j in range(3)]
        H = ent(P)
        M = sum(wts[j] * ent(qs[j]) for j in range(3))
        if M <= 0.0:
            break
        a = H / M
        logs = [0.0] * n
        for j in range(3):
            if wts[j] == 0.0:
                continue
            lq = [math.log(max(v, TINY)) for v in qs[j]]
            c = a * wts[j]
            ix = sup.idx[j]
            for i in range(n):
                logs[i] += c * lq[ix[i]]
        m = max(logs)
        e = [math.exp(v - m) for v in logs]
        z = sum(e)
        P = [v / z for v in e]
    return P


DEFAULT_STAGES = ((18, 300), (10, 2000))


def optimize(sup, P=None, lo=0.0, hi=1.0, stages=DEFAULT_STAGES):
    """Bisection on mu (balance H_S against (H_X + H_Y)/2), MM inside. Returns the best law seen
    (by alpha_s) with the mu that produced it."""
    n = sup.n
    if P is None:
        P = [1.0 / n] * n
    else:
        P = normalize([max(float(v), 1e-12) for v in P])
    best = {"alpha_s": -1.0}

    def consider(Q, mu):
        H, hx, hy, hs = entropies(sup, Q)
        a, a_s = ratio_pair(H, hx, hy, hs)
        if a_s > best["alpha_s"]:
            best.update({"alpha_s": a_s, "alpha": a, "mu": mu, "P": list(Q),
                         "H": H, "HX": hx, "HY": hy, "HS": hs})
        return hx, hy, hs

    first = True
    for nbis, iters in stages:
        if not first:
            mid = 0.5 * (lo + hi)
            w = 4.0 * (hi - lo) + 0.02
            lo, hi = max(0.0, mid - w), min(1.0, mid + w)
        first = False
        for _ in range(nbis):
            mu = 0.5 * (lo + hi)
            P = mm(sup, P, mu, iters)
            hx, hy, hs = consider(P, mu)
            if hs > 0.5 * (hx + hy):
                lo = mu
            else:
                hi = mu
    best["bracket"] = [lo, hi]
    return best


# ----------------------------------------------------------------------------- tensor test
def inner(P, C, D):
    n = len(P)
    return sum(P[a] * P[b] * C[a][b] * D[a][b] for a in range(n) for b in range(n))


def center(P, C):
    """Project C onto mean-zero (x) mean-zero in L2(P (x) P)."""
    n = len(P)
    rowm = [sum(P[b] * C[a][b] for b in range(n)) for a in range(n)]
    C1 = [[C[a][b] - rowm[a] for b in range(n)] for a in range(n)]
    colm = [sum(P[a] * C1[a][b] for a in range(n)) for b in range(n)]
    return [[C1[a][b] - colm[b] for b in range(n)] for a in range(n)]


def cond_exp(sup, P, j, f):
    m = sup.sizes[j]
    ix = sup.idx[j]
    q = [0.0] * m
    s = [0.0] * m
    for i in range(sup.n):
        q[ix[i]] += P[i]
        s[ix[i]] += P[i] * f[i]
    return [s[ix[i]] / q[ix[i]] if q[ix[i]] > 0.0 else 0.0 for i in range(sup.n)]


def apply_aa(sup, P, j, C):
    """(A_j (x) A_j) C, A_j = conditional expectation on form j under P."""
    n = sup.n
    cols = [cond_exp(sup, P, j, [C[a][b] for a in range(n)]) for b in range(n)]
    rows = [[cols[b][a] for b in range(n)] for a in range(n)]
    return [cond_exp(sup, P, j, rows[a]) for a in range(n)]


def tensor_lambda(sup, P, mu, iters=800, seed=1):
    """Power iteration for the top eigenvalue of T = sum_j lambda_j A_j (x) A_j on mean-zero (x)
    mean-zero, lambda = ((1-mu)/2, (1-mu)/2, mu). Returns the Rayleigh quotient of the final
    vector (a lower bound for Lambda_max), its per-form parts and the vector."""
    lam = (0.5 * (1.0 - mu), 0.5 * (1.0 - mu), mu)
    n = sup.n
    rng = random.Random(seed)
    C = center(P, [[rng.gauss(0.0, 1.0) for _ in range(n)] for _ in range(n)])
    nrm = math.sqrt(max(inner(P, C, C), 0.0))
    C = [[v / nrm for v in row] for row in C]
    for _ in range(iters):
        T = [[0.0] * n for _ in range(n)]
        for j in range(3):
            if lam[j] == 0.0:
                continue
            A = apply_aa(sup, P, j, C)
            for a in range(n):
                Ta = T[a]
                Aa = A[a]
                for b in range(n):
                    Ta[b] += lam[j] * Aa[b]
        T = center(P, T)
        nrm = math.sqrt(max(inner(P, T, T), 0.0))
        if nrm == 0.0:
            break
        C = [[v / nrm for v in row] for row in T]
    parts = [inner(P, C, apply_aa(sup, P, j, C)) for j in range(3)]
    ray = sum(lam[j] * parts[j] for j in range(3))
    return {"rayleigh": ray, "parts": parts, "lam": list(lam), "C": C}


# ----------------------------------------------------------------------------- annealing
def anneal(dbox, sbox, start, minutes, rng, quick=((10, 150),), log=None):
    cells = list(itertools.product(*[range(lo, hi + 1) for lo, hi in dbox]))
    svals = list(itertools.product(*[range(lo, hi + 1) for lo, hi in sbox]))
    opts = {}
    for d in cells:
        opts[d] = [None] + [s for s in svals if all((di - si) % 2 == 0 for di, si in zip(d, s))]

    def score(smap, warm):
        keys, pts = smap_points(smap)
        sup = Support(pts)
        P0 = [warm.get(k, 0.0) for k in keys]
        pos = [v for v in P0 if v > 0]
        fill = (sum(pos) / len(pos)) if pos else 1.0
        P0 = [v if v > 0 else 0.5 * fill for v in P0]
        b = optimize(sup, P0, stages=quick)
        return b["alpha_s"], dict(zip(keys, b["P"]))

    cur = dict(start)
    cur_score, cur_w = score(cur, {})
    best = (cur_score, dict(cur), dict(cur_w))
    t_start = time.time()
    t_end = t_start + 60.0 * minutes
    T0, T1 = 2e-3, 1e-6
    steps = accepted = 0
    next_log = t_start + 60.0
    while time.time() < t_end:
        frac = (time.time() - t_start) / max(1e-9, t_end - t_start)
        T = T0 * (T1 / T0) ** frac
        d = rng.choice(cells)
        o = rng.choice(opts[d])
        if (o is None and d not in cur) or cur.get(d) == o:
            continue
        new = dict(cur)
        if o is None:
            del new[d]
        else:
            new[d] = o
        if len(new) < 3:
            continue
        sc, w = score(new, cur_w)
        steps += 1
        if sc >= cur_score or rng.random() < math.exp((sc - cur_score) / T):
            cur, cur_score, cur_w = new, sc, w
            accepted += 1
            if sc > best[0]:
                best = (sc, dict(new), dict(w))
        if log is not None and time.time() > next_log:
            log("  anneal %d steps, %d accepted, cur %.10f, best %.10f, |support| %d"
                % (steps, accepted, cur_score, best[0], len(cur)))
            next_log += 60.0
    return best, steps, accepted


def smap_json(smap, weights):
    return [[list(d), list(smap[d]), weights.get(d, 0.0)] for d in sorted(smap)]


# ----------------------------------------------------------------------------- main
def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--minutes-2d", type=float, default=40.0)
    ap.add_argument("--minutes-1d", type=float, default=15.0)
    ap.add_argument("--tensor-iters", type=int, default=800)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args(argv)
    rng = random.Random(args.seed)
    t0 = time.time()

    def log(msg):
        print("[%7.1fs] %s" % (time.time() - t0, msg))
        sys.stdout.flush()

    out = {"version": "sdz-search-v1", "lit_best": LIT_BEST, "record_bar": RECORD_BAR,
           "lemm_bound": LEMM_BOUND, "ruzsa": RUZSA, "calibration_bar": CALIBRATION_BAR}
    candidates = []        # (verified alpha_s as float, label)

    def dump():
        with open(args.out, "w") as fh:
            json.dump(out, fh, indent=1)

    # E0
    sup7 = Support(staircase(-1, 5))
    H, hx, hy, hs = entropies(sup7, lemm_law())
    a, a_s = ratio_pair(H, hx, hy, hs)
    out["E0_lemm_printed_weights"] = {"H": H, "HX": hx, "HY": hy, "HS": hs, "alpha": a,
                                      "alpha_s": a_s, "verified": verify(sup7, lemm_law())}
    log("E0 Lemm printed weights: alpha %.8f" % a)
    dump()

    # E1
    e1 = []
    opt1d = {}
    for lo, hi in STAIRS:
        sup = Support(staircase(lo, hi))
        b = optimize(sup, None, stages=((20, 500), (12, 4000), (6, 20000)))
        v = verify(sup, b["P"])
        e1.append({"lo": lo, "hi": hi, "n": sup.n, "alpha_s": b["alpha_s"], "alpha": b["alpha"],
                   "mu": b["mu"], "H": b["H"], "HX": b["HX"], "HY": b["HY"], "HS": b["HS"],
                   "verified_alpha": v[0], "verified_alpha_s": v[1], "P": b["P"]})
        opt1d[(lo, hi)] = (sup, b)
        candidates.append((float(v[1]), "E1 staircase %d..%d" % (lo, hi)))
        log("E1 staircase %d..%d (%d pts): alpha_s %s mu %.6f" % (lo, hi, sup.n, v[1], b["mu"]))
        out["E1_staircases"] = e1
        dump()
    calib = [r for r in e1 if (r["lo"], r["hi"]) == (-1, 5)][0]
    calibration_ok = float(calib["verified_alpha_s"]) >= CALIBRATION_BAR
    out["calibration_ok"] = calibration_ok

    # E2
    e2 = []
    for lo, hi in TENSOR_STAIRS:
        sup, b = opt1d[(lo, hi)]
        P, mu, a1 = b["P"], b["mu"], b["alpha_s"]
        lams = [tensor_lambda(sup, P, mu, iters=args.tensor_iters, seed=s) for s in (1, 2)]
        lam = max(lams, key=lambda r: r["rayleigh"])
        kappa = a1 * lam["rayleigh"]
        log("E2 staircase %d..%d: Lambda %.9f kappa %.9f parts %s"
            % (lo, hi, lam["rayleigh"], kappa, ["%.6f" % x for x in lam["parts"]]))
        sup2 = product_support(sup, sup)
        n = sup.n
        base = product_law(P, P)
        C = lam["C"]
        cmax = max(abs(c) for row in C for c in row) or 1.0
        starts = [("product", base),
                  ("eigen", [base[i * n + k] * (1.0 + 0.5 * C[i][k] / cmax)
                             for i in range(n) for k in range(n)])]
        for r in range(2):
            starts.append(("random%d" % r, [w * math.exp(0.05 * rng.gauss(0.0, 1.0)) for w in base]))
        runs = {}
        for name, P0 in starts:
            bb = optimize(sup2, P0, lo=max(0.0, mu - 0.15), hi=min(1.0, mu + 0.15),
                          stages=((10, 300), (8, 2000)))
            vv = verify(sup2, bb["P"])
            runs[name] = {"alpha_s": bb["alpha_s"], "gain": bb["alpha_s"] - a1,
                          "verified_alpha_s": vv[1], "mu": bb["mu"]}
            candidates.append((float(vv[1]), "E2 %d..%d %s" % (lo, hi, name)))
            log("   2-D start %-8s alpha_s %.12f gain %.3e" % (name, bb["alpha_s"], bb["alpha_s"] - a1))
            if bb["alpha_s"] - a1 > 1e-9:
                runs[name]["P"] = bb["P"]
                runs[name]["points"] = [[list(x), list(y)] for x, y in sup2.pts]
        gain = max(r["gain"] for r in runs.values())
        if kappa > 1.0 + 1e-6 and gain > 1e-9:
            verdict = "UNSTABLE"
        elif kappa < 1.0 - 1e-6 and gain <= 1e-9:
            verdict = "STABLE"
        else:
            verdict = "UNCLEAR"
        e2.append({"lo": lo, "hi": hi, "n": n, "alpha_1d": a1, "mu": mu, "Lambda": lam["rayleigh"],
                   "Lambda_seeds": [r["rayleigh"] for r in lams], "parts": lam["parts"],
                   "lambda_weights": lam["lam"], "kappa": kappa, "runs": runs,
                   "max_gain": gain, "verdict": verdict})
        out["E2_tensor"] = e2
        dump()

    # E3: two-dimensional supports
    start2 = {}
    for d1 in range(-1, 6):
        for d2 in range(-1, 6):
            start2[(d1, d2)] = (1 if d1 % 2 else 2, 1 if d2 % 2 else 2)
    log("E3 start (product of Lemm staircases, %d points)" % len(start2))
    best3, st3, ac3 = anneal([(-2, 6), (-2, 6)], [(0, 3), (0, 3)], start2, args.minutes_2d, rng, log=log)
    keys, pts = smap_points(best3[1])
    sup3 = Support(pts)
    pol3 = optimize(sup3, [best3[2].get(k, 0.0) for k in keys], stages=((16, 1000), (10, 6000)))
    v3 = verify(sup3, pol3["P"])
    candidates.append((float(v3[1]), "E3 best 2-D support"))
    out["E3_anneal_2d"] = {"steps": st3, "accepted": ac3, "quick_best": best3[0],
                           "polished_alpha_s": pol3["alpha_s"], "verified_alpha_s": v3[1],
                           "verified_alpha": v3[0], "n": sup3.n, "mu": pol3["mu"],
                           "support": smap_json(best3[1], dict(zip(keys, pol3["P"])))}
    log("E3 done: %d steps, best verified alpha_s %s on %d points" % (st3, v3[1], sup3.n))
    dump()

    # E4: one dimension, three sums per difference
    start1 = {}
    for d in range(-1, 6):
        start1[(d,)] = (1 if d % 2 else 2,)
    best4, st4, ac4 = anneal([(-4, 10)], [(-1, 4)], start1, args.minutes_1d, rng, log=log)
    keys, pts = smap_points(best4[1])
    sup4 = Support(pts)
    pol4 = optimize(sup4, [best4[2].get(k, 0.0) for k in keys], stages=((16, 1000), (10, 6000)))
    v4 = verify(sup4, pol4["P"])
    candidates.append((float(v4[1]), "E4 best 1-D support"))
    out["E4_anneal_1d"] = {"steps": st4, "accepted": ac4, "quick_best": best4[0],
                           "polished_alpha_s": pol4["alpha_s"], "verified_alpha_s": v4[1],
                           "verified_alpha": v4[0], "n": sup4.n, "mu": pol4["mu"],
                           "support": smap_json(best4[1], dict(zip(keys, pol4["P"])))}
    log("E4 done: %d steps, best verified alpha_s %s on %d points" % (st4, v4[1], sup4.n))

    # grade (rules fixed in notes/prereg-sdz.md)
    top = max(candidates)
    if not calibration_ok:
        grade = "INVALID"
    elif top[0] > RECORD_BAR:
        grade = "RECORD"
    elif top[0] > LIT_BEST + 1e-9:
        grade = "FRONTIER"
    else:
        grade = "NO_GAIN"
    out["best_overall"] = {"verified_alpha_s": top[0], "where": top[1]}
    out["tensor_verdicts"] = {"%d..%d" % (r["lo"], r["hi"]): r["verdict"] for r in out.get("E2_tensor", [])}
    out["grade"] = grade
    out["seconds"] = time.time() - t0
    dump()
    log("GRADE %s best %.12f (%s)" % (grade, top[0], top[1]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
