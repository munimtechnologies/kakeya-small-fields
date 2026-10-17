# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Case B of Question R (notes/tight-cases.md) as an exact SAT search in a normal form, and the
classification of anisotropic systems with dim V = dim X = 2 (Lemma 34 of notes/case-b.md).

Setting and encoding as in sat_aniso.py. Case B at (t, k): an anisotropic system with dim X = t and
dim V = d = t + k - 1, and an element u with rank A_u <= t - k such that phi = beta(u, .) maps V
onto a hyperplane P of X that does not contain x0 = sigma(u). Lemma 35 of notes/case-b.md gives
bases of X and V with

    x0 = e_0,   P = span(e_1, ..., e_(t-1)),   A_u e_c = 0 for c < k,
    v_0 = u,    phi(v_i) = 0 for 1 <= i <= k - 1,   phi(v_(k-1+j)) = e_j for 1 <= j <= t - 1.

So such a system exists iff the CNF of sat_aniso.encode (without its echelon form) with these
values fixed by unit clauses is satisfiable. By Corollary 18 of notes/tight-cases.md, UNSAT for
(t, k) = (6, 3) gives A(6) <= 7, and UNSAT for (7, 4) gives A(7) <= 9, which settles Z_4^10 x Z_2^2.

Parts: selfcheck (pure Python: Lemma 34 by exhaustive search; on scrambled copies of a known
system, normalise() reaches the normal form and the CNF accepts exactly the anisotropic systems in
normal form), solve (one instance in a child process with a time budget; needs python-sat), grade
(the pre-registered predictions of m11/predictions.md).

Usage: python case_b.py --part selfcheck|solve|grade [--t T --k K] [--budget-minutes 5]
                        [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

import sat_aniso as sa


# ---------- Lemma 34: anisotropic systems with dim V = dim X = 2 ----------

def classify_2x2(at, sv):
    """'i' if beta = 0 and alpha = 0; 'ii' if some basis (v1, v2) of V has sigma(v1) = sigma(v2) = a,
    delta = beta(v1, v2) outside span(a), and A_v1, A_v2 both kill a and fix delta; else 'other'."""
    if sv[3] == sv[1] ^ sv[2] and at[1] == at[2] == 0:
        return "i"
    for v1, v2 in itertools.permutations((1, 2, 3), 2):
        a, delta = sv[v1], sv[v1 ^ v2] ^ sv[v1] ^ sv[v2]
        if sv[v2] != a or delta in (0, a):
            continue
        if all(sa.mat_apply(at[v], a, 2) == 0 and sa.mat_apply(at[v], delta, 2) == delta
               for v in (v1, v2)):
            return "ii"
    return "other"


def lemma34():
    st = {"candidates": 0, "systems": 0, "i": 0, "ii": 0, "other": 0}
    for A1, A2, s1, s2, b in itertools.product(range(16), range(16), range(1, 4), range(1, 4),
                                               range(4)):
        st["candidates"] += 1
        at, sv = sa.tables([A1, A2], [s1, s2], {(0, 1): b}, 2)
        if not (sa.anisotropic(sv) and sa.is_system(at, sv, 2, 2)):
            continue
        st["systems"] += 1
        st[classify_2x2(at, sv)] += 1
    return st


# ---------- the normal form (Lemma 35) ----------

def span(gens):
    out = {0}
    for g in gens:
        out |= {x ^ g for x in out}
    return out


def phi_table(sv, d, u):
    x0 = sv[u]
    return [sv[u ^ h] ^ x0 ^ sv[h] for h in range(1 << d)]


def qualifies(at, sv, d, t, k, u):
    """Does u satisfy the hypotheses of Lemma 35 (d = t + k - 1, sigma(u) != 0,
    rank A_u <= t - k, phi(V) a hyperplane without sigma(u))?"""
    if d != t + k - 1 or u == 0 or sv[u] == 0:
        return False
    if sa.rank_f2(sa.rows_of(at[u], t)) > t - k:
        return False
    P = span(phi_table(sv, d, u))
    return len(P) == 1 << (t - 1) and sv[u] not in P


def normalise(at, sv, d, t, k, u):
    """(As, ss, B) in the bases of the proof of Lemma 35, for an element u that qualifies."""
    x0 = sv[u]
    phi = phi_table(sv, d, u)
    P = span(phi)
    ker = {x for x in range(1 << t) if sa.mat_apply(at[u], x, t) == 0}
    ybasis = sa.independent(sorted(P & ker))[:k - 1]
    pbasis = sa.independent(ybasis + sorted(P))
    Q = sa.from_cols([x0] + pbasis, t)
    g = sa.mat_inv(Q, t)
    nbasis = sa.independent([u] + [h for h in range(1, 1 << d) if phi[h] == 0])
    fs = [next(h for h in range(1 << d) if phi[h] == p) for p in pbasis]
    vb = nbasis + fs
    As = [sa.mat_mul(sa.mat_mul(g, at[v], t), Q, t) for v in vb]
    ss = [sa.mat_apply(g, sv[v], t) for v in vb]
    B = {(i, j): sa.mat_apply(g, sv[vb[i] ^ vb[j]] ^ sv[vb[i]] ^ sv[vb[j]], t)
         for i, j in itertools.combinations(range(d), 2)}
    return As, ss, B


def wanted_phi(i, k):
    return 0 if i < k else 1 << (i - k + 1)


def in_normal_form(As, ss, B, t, k):
    d = t + k - 1
    if len(As) != d or ss[0] != 1:
        return False
    if any(sa.mat_apply(As[0], 1 << c, t) for c in range(k)):
        return False
    return all(B[(0, i)] == wanted_phi(i, k) for i in range(1, d))


def encode_case_b(t, k):
    """sat_aniso.encode (no echelon form) with the values of the normal form fixed."""
    d = t + k - 1
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]
    for r in range(t):
        cnf.clauses.append([S[0][r]] if r == 0 else [-S[0][r]])
        for c in range(k):
            cnf.clauses.append([-A[0][r][c]])
    for i in range(1, d):
        want = wanted_phi(i, k)
        for r in range(t):
            v = B[(0, i)][r]
            cnf.clauses.append([v] if (want >> r) & 1 else [-v])
    return cnf, names


def accepts(As, ss, B, t, k):
    cnf, names = encode_case_b(t, k)
    return sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, t, t + k - 1))


# ---------- known example and scrambling ----------

def example_t2():
    """The system of notes/case-b.md with t = 2 and k = 1 (V = span(u, f)): A_u = E_11, A_f = 0,
    sigma(u) = e_0, sigma(f) = e_1, beta(u, f) = e_1. It is anisotropic and already in normal form;
    u and u + f qualify for Lemma 35, f does not."""
    return [8, 0], [1, 2], {(0, 1): 2}


def random_invertible(rng, t):
    while True:
        g = rng.getrandbits(t * t)
        if sa.rank_f2(sa.rows_of(g, t)) == t:
            return g


def scramble(As, ss, B, t, d, rng):
    """The same system in random bases of X and V."""
    at, sv = sa.tables(As, ss, B, d)
    g = random_invertible(rng, t)
    gi = sa.mat_inv(g, t)
    while True:
        vb = [rng.randrange(1, 1 << d) for _ in range(d)]
        if sa.rank_f2(vb) == d:
            break
    vals = [sa.combine(vb, c) for c in range(1 << d)]
    at2 = [sa.mat_mul(sa.mat_mul(g, at[v], t), gi, t) for v in vals]
    sv2 = [sa.mat_apply(g, sv[v], t) for v in vals]
    return at2, sv2


def mutations(As, ss, B, t, rng, count):
    out = []
    for _ in range(count):
        As2, ss2, B2 = list(As), list(ss), dict(B)
        which = rng.randrange(3)
        if which == 0:
            i = rng.randrange(len(As2))
            As2[i] ^= 1 << rng.randrange(t * t)
        elif which == 1:
            i = rng.randrange(len(ss2))
            ss2[i] ^= 1 << rng.randrange(t)
        else:
            key = rng.choice(sorted(B2))
            B2[key] ^= 1 << rng.randrange(t)
        out.append((As2, ss2, B2))
    return out


def normalisation_check(rng, count):
    """Scramble the example, find every element that qualifies, normalise at it, and compare the
    CNF with a brute-force check on the result and on one-bit mutations of it."""
    t, k, d = 2, 1, 2
    st = {"scrambles": 0, "qualifying": [], "normal_form": 0, "accepted": 0, "mutations": 0,
          "mutations_accepted": 0, "disagree": 0}
    As0, ss0, B0 = example_t2()
    for _ in range(count):
        at, sv = scramble(As0, ss0, B0, t, d, rng)
        st["scrambles"] += 1
        us = [u for u in range(1, 1 << d) if qualifies(at, sv, d, t, k, u)]
        st["qualifying"].append(len(us))
        for u in us:
            As, ss, B = normalise(at, sv, d, t, k, u)
            st["normal_form"] += in_normal_form(As, ss, B, t, k)
            st["accepted"] += accepts(As, ss, B, t, k)
            for As2, ss2, B2 in mutations(As, ss, B, t, rng, 4):
                at2, sv2 = sa.tables(As2, ss2, B2, d)
                good = (sa.is_system(at2, sv2, d, t) and sa.anisotropic(sv2)
                        and in_normal_form(As2, ss2, B2, t, k))
                acc = accepts(As2, ss2, B2, t, k)
                st["mutations"] += 1
                st["mutations_accepted"] += acc
                st["disagree"] += acc != good
    st["qualifying"] = sorted(set(st["qualifying"]))
    return st


def selfcheck(rng):
    st = {"lemma34": lemma34(), "normalisation": normalisation_check(rng, 40),
          "example_in_normal_form": in_normal_form(*example_t2(), 2, 1),
          "cnf_sizes": {f"{t},{k}": encode_case_b(t, k)[0].nv for t, k in ((2, 1), (3, 2))}}
    n = st["normalisation"]
    st["graded"] = {
        "lemma34": st["lemma34"] == {"candidates": 9216, "systems": 24, "i": 6, "ii": 18,
                                     "other": 0},
        "example": st["example_in_normal_form"],
        "two_qualify": n["qualifying"] == [2],
        "normalised": n["normal_form"] == n["accepted"] == 2 * n["scrambles"],
        "cnf_agrees": n["disagree"] == 0,
        "nontrivial": 0 <= n["mutations_accepted"] < n["mutations"]}
    return st


# ---------- solving ----------

def instance_name(t, k):
    return f"cb_t{t}_k{k}"


def child(t, k, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_case_b(t, k)
    start = time.time()
    used = None
    for name in (sa.SOLVERS if solver == "auto" else (solver,)):
        try:
            s = Solver(name=name, bootstrap_with=cnf.clauses)
            used = name
            break
        except Exception:
            continue
    if used is None:
        raise RuntimeError("no SAT solver available")
    ok = s.solve()
    res = {"status": "SAT" if ok else "UNSAT", "solver": used, "vars": cnf.nv,
           "clauses": len(cnf.clauses), "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, t, t + k - 1)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve(t, k, solver, budget_seconds, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    d = t + k - 1
    name = instance_name(t, k)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--k",
           str(k), "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "k": k, "d": d, "name": name,
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and in_normal_form(As, ss, B, t, k))
        res["ranks"] = sorted(sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d))
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


# Pre-registered (m11/predictions.md). SAT counts only with a verified model; UNKNOWN and ERROR are
# reported and not graded.
EXPECTED = {"cb_t2_k1": "SAT", "cb_t3_k2": "UNSAT", "cb_t4_k2": "UNSAT"}
EXPLORATORY = ("cb_t6_k3", "cb_t7_k4", "cb_t5_k2")


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("cb_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    for name, want in EXPECTED.items():
        r = results.get(name)
        if r is None or r["status"] not in ("SAT", "UNSAT"):
            ungraded[name] = "missing" if r is None else r["status"]
            continue
        graded[name] = r["status"] == want and (want == "UNSAT" or r["verified"])
    # Proposition 26(a): in a verified model of an exploratory instance, every rank is <= t - k.
    for name in EXPLORATORY:
        r = results.get(name)
        if r is not None and r["status"] == "SAT":
            graded[name + "_verified"] = bool(r.get("verified"))
            graded[name + "_ranks"] = max(r.get("ranks") or [0]) <= r["t"] - r["k"]
    explore = {name: {key: results[name].get(key) for key in ("status", "seconds", "vars",
                                                               "clauses", "verified", "ranks")}
               for name in EXPLORATORY if name in results}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "exploratory": explore, "times": times}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=2)
    ap.add_argument("--k", type=int, default=1)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=5.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.t, args.k, args.solver, args.child_out)
    elif args.part == "solve":
        res = solve(args.t, args.k, args.solver, args.budget_minutes * 60, args.out_dir)
        print(f"SUMMARY {res['name']} {res['status']}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {sorted(out['ungraded'])}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck(random.Random(61))
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
