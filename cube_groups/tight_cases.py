# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma 33 of notes/tight-cases.md: the linear algebra behind Case A of Question R for every rank.

Lemma 33: let 1 <= k <= t - 1, let A_u in M_t(F_2) have rank t - k, with x0 in X_1 = ker A_u and
R = Im A_u, and let A_v satisfy A_v x0 = x0 and Im(I + A_v) inside R. Put A_w = A_u + A_v. If A_v
and A_w both have rank <= t - k, then t >= 2k + 1. If t = 2k + 1, the kernels K_v and K_w have
dimension k, meet in a space of dimension k - 1 inside X_1, and span R.

Part lemma33 checks this by exhaustive search for small (t, k). A change of basis fixing x0 = e_0
puts X_1 in the form span(e_0, ..., e_(k-1)), and then R (dimension t - k) in one of the forms of
normal_forms(): R n X_1 is span(e_0, ..., e_(d-1)) if x0 is in R and span(e_1, ..., e_d) if not,
and R is R n X_1 plus span(e_k, ..., e_(t-d-1)). Then A_u is any matrix whose first k columns are
zero and whose other columns are an ordered basis of R, and A_v is any matrix with column 0 equal
to e_0 and column j equal to e_j + r_j (r_j in R) for j >= 1; these are exactly the pairs that
satisfy the hypotheses before the rank conditions. A_v of rank > t - k are dropped before the pairs
are formed.

Vectors and matrices are int bitmasks as in m6_sharp.py (entry (r, c) of a t x t matrix at bit
t r + c). Pure Python, no dependencies besides m6_sharp.py and question_r.py.

Usage: python tight_cases.py [--out-dir DIR] [--part lemma33]
"""
import argparse
import itertools
import json

import m6_sharp as ms
import question_r as qr


def normal_forms(t, k):
    """R (dimension t - k) up to a change of basis fixing e_0 and span(e_0, ..., e_(k-1))."""
    forms = []
    for d in range(min(k, t - k) + 1):
        rest = [1 << i for i in range(k, t - d)]
        if d >= 1:
            forms.append((f"x0_in_R_d{d}", [1 << i for i in range(d)] + rest))
        if d <= k - 1:
            forms.append((f"x0_not_in_R_d{d}", [1 << i for i in range(1, d + 1)] + rest))
    return forms


def hypotheses(Au, Av, R, t, k):
    """Every hypothesis of Lemma 33 (x0 = e_0, X_1 = span(e_0, ..., e_(k-1))), one by one."""
    I = qr.identity_matrix(t)
    rho = t - k
    return {"rank_u": ms.mat_rank(Au, t) == rho,
            "ker_u": qr.kernel(Au, t) == qr.span([1 << i for i in range(k)]),
            "image_u": qr.image(Au, t) == R, "v_fixes_x0": ms.mat_apply(Av, 1, t) == 1,
            "image_I_v": all(ms.mat_apply(I ^ Av, 1 << j, t) in R for j in range(t)),
            "rank_v": ms.mat_rank(Av, t) <= rho, "rank_w": ms.mat_rank(Au ^ Av, t) <= rho}


def conclusions(Au, Av, R, t, k):
    """The conclusions of Lemma 33, and the steps of its proof, for a pair satisfying its
    hypotheses."""
    X1 = qr.span([1 << i for i in range(k)])
    Kv, Kw = qr.kernel(Av, t), qr.kernel(Au ^ Av, t)
    meet = Kv & Kw
    out = {"t_at_least_2k_plus_1": t >= 2 * k + 1, "kv_in_R": Kv <= R, "kw_in_R": Kw <= R,
           "meet_in_X1": meet <= X1, "x0_not_in_kv": 1 not in Kv}
    if t == 2 * k + 1:
        out.update({"kv_dim_k": len(Kv) == 1 << k, "kw_dim_k": len(Kw) == 1 << k,
                    "meet_dim": len(meet) == 1 << (k - 1), "kv_plus_kw": qr.span(Kv | Kw) == R})
    return out


def lemma33(t, k):
    """Exhaustive check of Lemma 33 for one (t, k)."""
    rho = t - k
    X1 = qr.span([1 << i for i in range(k)])
    st = {"t": t, "k": k, "forms": 0, "candidates_v": 0, "low_rank_v": 0, "pairs": 0,
          "survivors": 0, "by_form": {}, "hyp_fail": 0, "fail": {}, "examples": []}
    for name, Rb in normal_forms(t, k):
        st["forms"] += 1
        R = qr.span(Rb)
        low = []
        for rs in itertools.product(sorted(R), repeat=t - 1):
            Av = qr.from_columns([1] + [(1 << j) ^ r for j, r in zip(range(1, t), rs)], t)
            st["candidates_v"] += 1
            if ms.mat_rank(Av, t) <= rho:
                low.append(Av)
        st["low_rank_v"] += len(low)
        surv = 0
        for basis in qr.ordered_bases(Rb):
            Au = qr.from_columns([0] * k + list(basis), t)
            if not (ms.mat_rank(Au, t) == rho and qr.kernel(Au, t) == X1
                    and qr.image(Au, t) == R):
                st["hyp_fail"] += 1
            for Av in low:
                st["pairs"] += 1
                if ms.mat_rank(Au ^ Av, t) > rho:
                    continue
                surv += 1
                if not all(hypotheses(Au, Av, R, t, k).values()):
                    st["hyp_fail"] += 1
                for key, ok in conclusions(Au, Av, R, t, k).items():
                    if not ok:
                        st["fail"][key] = st["fail"].get(key, 0) + 1
                if len(st["examples"]) < 3:
                    st["examples"].append({"form": name, "Au": Au, "Av": Av})
        st["by_form"][name] = surv
        st["survivors"] += surv
    return st


PLAN = ((3, 2), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 3), (6, 4), (6, 5))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["lemma33"], default="lemma33")
    args = ap.parse_args()
    out = {f"{t},{k}": lemma33(t, k) for t, k in PLAN}
    graded = {"hypotheses": all(s["hyp_fail"] == 0 for s in out.values()),
              "conclusions": all(s["fail"] == {} for s in out.values()),
              "none_below_2k_plus_1": all(s["survivors"] == 0 for s in out.values()
                                          if s["t"] <= 2 * s["k"]),
              "survivors_at_5_2": out["5,2"]["survivors"] > 0}
    print(f"{args.part}: {json.dumps(out, sort_keys=True)}", flush=True)
    print(f"SUMMARY {args.part} all_match {all(graded.values())}", flush=True)
    qr.write_out({"stats": out, "graded": graded}, args.out_dir, f"{args.part}.json")


if __name__ == "__main__":
    main()
