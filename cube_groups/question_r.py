# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma 31, Lemma 32 and Proposition 25 of notes/question-r.md: Case A of Question R.

Setting as in m6_sharp.py: X = F_2^t, V = F_2^m, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Lemma 31: in every system, if u, v in V have beta(u, v) = sigma(u), then with phi = beta(u, .) and
psi = beta(v, .)

    (I + A_v) phi(h) = A_u (phi(h) + psi(h))     for all h in V.

Lemma 32 (linear algebra): let A_u have rank t - 2 and kernel span(x0, z), R = Im A_u, and let A_v
satisfy A_v x0 = x0, A_v z = 0 and Im(I + A_v) inside R. Put A_w = A_u + A_v. If A_v and A_w have
rank <= t - 2, then t >= 5. For t = 5, A_v and A_w have rank exactly 3, their kernels K_v and K_w are
planes in R with K_v n K_w = span(z) and K_v + K_w = R, R is invariant under A_v and A_w, and the
fixed spaces of A_v and A_w meet in span(x0).

Parts. identity: Lemma 31 at every pair (u, v) with beta(u, v) = sigma(u) of random systems with
t = 3 and 4 and of the diagonal systems of Lemma 23(d). control: random pairs (alpha, sigma) that
are not systems break it. casea: Lemma 32 for t = 3, 4, 5 by exhaustive search. A change of basis
fixing x0 = e_0 and z = e_1 puts R (which contains z, as (I + A_v) z = z) in one of two forms:
span(e_1, ..., e_(t-2)) if x0 is not in R, span(e_0, ..., e_(t-3)) if it is. Then A_u is any matrix
whose columns 0 and 1 are zero and whose other columns are an ordered basis of R, and A_v is any
matrix with columns e_0, 0 and e_j + r_j (r_j in R) for j >= 2; these are exactly the pairs that
satisfy the hypotheses before the rank conditions.

Vectors and matrices are int bitmasks as in m6_sharp.py (entry (r, c) of a t x t matrix at bit
t r + c). Pure Python, no dependencies besides m6_sharp.py.

Usage: python question_r.py [--out-dir DIR] [--part identity|control|casea]
"""
import argparse
import itertools
import json
import os
import random

import m6_sharp as ms


def identity_matrix(t):
    return sum(1 << (t * i + i) for i in range(t))


def from_columns(cols, t):
    """The t x t matrix whose column c is cols[c]."""
    A = 0
    for c, col in enumerate(cols):
        for r in range(t):
            if (col >> r) & 1:
                A |= 1 << (t * r + c)
    return A


def span(gens):
    out = {0}
    for g in gens:
        out |= {x ^ g for x in out}
    return out


def kernel(A, t):
    return span(ms.nullspace(ms.rows_of(A, t), t))


def image(A, t):
    return {ms.mat_apply(A, x, t) for x in range(1 << t)}


# ---------- Lemma 31 ----------

def lemma31_check(at, sv, m, t):
    """(pairs (u, v) with beta(u, v) = sigma(u), those with sigma(u) != 0, pairs where Lemma 31
    fails at some h)."""
    n = 1 << m
    I = identity_matrix(t)
    pairs = nontrivial = fails = 0
    for u in range(n):
        x0 = sv[u]
        phi = [sv[u ^ h] ^ x0 ^ sv[h] for h in range(n)]
        for v in range(n):
            if phi[v] != x0:
                continue
            pairs += 1
            if x0:
                nontrivial += 1
            psi = [sv[v ^ h] ^ sv[v] ^ sv[h] for h in range(n)]
            M = I ^ at[v]
            if any(ms.mat_apply(M, phi[h], t) != ms.mat_apply(at[u], phi[h] ^ psi[h], t)
                   for h in range(n)):
                fails += 1
    return pairs, nontrivial, fails


def random_systems(rng, t, count, max_m=5):
    """count random systems (m, alpha table, value table) with dim V <= max_m, from random spaces
    of matrices and a random solution sigma of (*)."""
    out = []
    while len(out) < count:
        B = ms.independent([rng.getrandbits(t * t) for _ in range(rng.randint(1, 3))])
        if not B:
            continue
        m, at = ms.system(B, rng.randint(0, 2))
        if m > max_m:
            continue
        sol = ms.solve_sigma(at, m, t)
        if not sol:
            continue
        coeffs = ms.combine(sol, rng.getrandbits(len(sol)))
        out.append((m, at, ms.table(ms.sigma_from_coeffs(coeffs, ms.mon_tables(m), t), m)))
    return out


def identity_survey(rng, per_t=20):
    st = {}
    cases = [("diagonal_2", 2, ms.diagonal(2)), ("diagonal_3", 3, ms.diagonal(3))]
    for t in (3, 4):
        cases += [(f"random_t{t}", t, c) for c in random_systems(rng, t, per_t)]
    for name, t, (m, at, sv) in cases:
        s = st.setdefault(name, {"systems": 0, "not_system": 0, "pairs": 0, "nontrivial": 0,
                                 "fails": 0})
        s["systems"] += 1
        if not ms.is_system(at, sv, m, t):
            s["not_system"] += 1
        pairs, nontrivial, fails = lemma31_check(at, sv, m, t)
        s["pairs"] += pairs
        s["nontrivial"] += nontrivial
        s["fails"] += fails
    return st


def control(rng, count=50, t=3, m=3):
    """Random (alpha, sigma) on F_2^m that are not systems: Lemma 31 fails at some pair."""
    tabs = ms.mon_tables(m)
    st = {"pairs": 0, "systems": 0, "broken": 0}
    for _ in range(count):
        _, at = ms.system([rng.getrandbits(t * t) for _ in range(m)], 0)
        sv = ms.table(ms.sigma_from_coeffs(rng.getrandbits(t * len(tabs)), tabs, t), m)
        st["pairs"] += 1
        if ms.is_system(at, sv, m, t):
            st["systems"] += 1
        if lemma31_check(at, sv, m, t)[2]:
            st["broken"] += 1
    return st


# ---------- Lemma 32 ----------

def normal_forms(t):
    """R (dimension t - 2, containing z = e_1) up to a change of basis fixing e_0 and e_1."""
    forms = [("x0_not_in_R", [1 << i for i in range(1, t - 1)])]
    if t >= 4:
        forms.append(("x0_in_R", [1 << i for i in range(0, t - 2)]))
    return forms


def ordered_bases(Rb):
    """Every ordered basis of span(Rb)."""
    k = len(Rb)
    return [tup for tup in itertools.permutations(sorted(span(Rb) - {0}), k)
            if ms.rank_f2(list(tup)) == k]


def conclusions(Au, Av, R, t):
    """The conclusions of Lemma 32 for a pair satisfying its hypotheses, and the dimensions of the
    two fixed spaces."""
    I = identity_matrix(t)
    Aw = Au ^ Av
    Kv, Kw = kernel(Av, t), kernel(Aw, t)
    Fv, Fw = kernel(I ^ Av, t), kernel(I ^ Aw, t)
    out = {"t_at_least_5": t >= 5, "kv_in_R": Kv <= R, "kw_in_R": Kw <= R,
           "kv_kw_meet": (Kv & Kw) == {0, 2}, "fixed_meet": (Fv & Fw) == {0, 1}}
    if t == 5:
        out.update({"rank_v": ms.mat_rank(Av, t) == 3, "rank_w": ms.mat_rank(Aw, t) == 3,
                    "kv_plane": len(Kv) == 4, "kw_plane": len(Kw) == 4,
                    "kv_plus_kw": span(Kv | Kw) == R,
                    "R_invariant": all(ms.mat_apply(Av, r, t) in R and ms.mat_apply(Aw, r, t) in R
                                       for r in R)})
    dims = f"{len(Fv).bit_length() - 1},{len(Fw).bit_length() - 1}"
    return out, dims


def hypotheses(Au, Av, R, t):
    """Every hypothesis of Lemma 32 (x0 = e_0, z = e_1), one by one."""
    I = identity_matrix(t)
    Aw = Au ^ Av
    return {"rank_u": ms.mat_rank(Au, t) == t - 2, "ker_u": kernel(Au, t) == {0, 1, 2, 3},
            "image_u": image(Au, t) == R, "v_fixes_x0": ms.mat_apply(Av, 1, t) == 1,
            "v_kills_z": ms.mat_apply(Av, 2, t) == 0,
            "image_I_v": all(ms.mat_apply(I ^ Av, 1 << j, t) in R for j in range(t)),
            "rank_v": ms.mat_rank(Av, t) <= t - 2, "rank_w": ms.mat_rank(Aw, t) <= t - 2}


def lemma32(t):
    """Exhaustive check of Lemma 32 for one t (pairs counted before the rank conditions)."""
    I = identity_matrix(t)
    st = {"t": t, "pairs": 0, "survivors": 0, "by_form": {}, "hyp_fail": 0, "fail": {},
          "fixed_dims": {}}
    for name, Rb in normal_forms(t):
        R = span(Rb)
        vs = []
        for rs in itertools.product(sorted(R), repeat=t - 2):
            Av = from_columns([1, 0] + [(1 << (j + 2)) ^ r for j, r in enumerate(rs)], t)
            if not (ms.mat_apply(Av, 1, t) == 1 and ms.mat_apply(Av, 2, t) == 0
                    and all(ms.mat_apply(I ^ Av, 1 << j, t) in R for j in range(t))):
                st["hyp_fail"] += 1
            vs.append((Av, ms.mat_rank(Av, t)))
        surv = 0
        for basis in ordered_bases(Rb):
            Au = from_columns([0, 0] + list(basis), t)
            if not (ms.mat_rank(Au, t) == t - 2 and kernel(Au, t) == {0, 1, 2, 3}
                    and image(Au, t) == R):
                st["hyp_fail"] += 1
            for Av, rank_v in vs:
                st["pairs"] += 1
                if rank_v > t - 2 or ms.mat_rank(Au ^ Av, t) > t - 2:
                    continue
                # I + A_w = A_u + (I + A_v), so Im(I + A_w) lies in R as well
                if not all(ms.mat_apply(I ^ Au ^ Av, 1 << j, t) in R for j in range(t)):
                    st["hyp_fail"] += 1
                    continue
                surv += 1
                checks, dims = conclusions(Au, Av, R, t)
                for key, ok in checks.items():
                    if not ok:
                        st["fail"][key] = st["fail"].get(key, 0) + 1
                st["fixed_dims"][dims] = st["fixed_dims"].get(dims, 0) + 1
        st["by_form"][name] = surv
        st["survivors"] += surv
    return st


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["identity", "control", "casea"], default="casea")
    args = ap.parse_args()
    rng = random.Random(31)
    if args.part == "casea":
        out = {str(t): lemma32(t) for t in (3, 4, 5)}
        graded = {"pairs": [out[k]["pairs"] for k in ("3", "4", "5")] == [2, 192, 2 * 168 * 512],
                  "hypotheses": all(out[k]["hyp_fail"] == 0 for k in out),
                  "none_below_5": out["3"]["survivors"] == 0 and out["4"]["survivors"] == 0,
                  "t5_conclusions": out["5"]["fail"] == {},
                  "t5_survivors": out["5"]["survivors"] > 0}
    elif args.part == "identity":
        out = identity_survey(rng)
        graded = {"systems": all(s["not_system"] == 0 for s in out.values()),
                  "no_fail": all(s["fails"] == 0 for s in out.values()),
                  "diagonal_nontrivial": all(out[k]["nontrivial"] > 0
                                             for k in ("diagonal_2", "diagonal_3"))}
    else:
        out = control(rng)
        graded = {"no_systems": out["systems"] == 0,
                  "broken_most": out["broken"] >= out["pairs"] // 2}
    print(f"{args.part}: {json.dumps(out, sort_keys=True)}", flush=True)
    print(f"SUMMARY {args.part} all_match {all(graded.values())}", flush=True)
    write_out({"stats": out, "graded": graded}, args.out_dir, f"{args.part}.json")


if __name__ == "__main__":
    main()
