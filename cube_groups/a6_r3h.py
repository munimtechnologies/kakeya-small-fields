# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m29: the search of job m27 (a6_r3.py, notes/a14.md) again, with the hand facts of Lemma 69
(notes/a16.md) added to every instance as linear conditions.

Job m27 split the rank-3 configurations (A4) = ("A", 5), (B4) = ("B", 4) and (B5) = ("B", 5) of
Corollary 39 at t = 6 by the pair (X_1, R) = (ker A_u, Im A_u) and decided none of its 72 instances
at t = 6 within 2 or 3 minutes each. Its encoding fixes sigma(u) = e_0 and phi = beta(u, .) and
leaves everything else to the solver. In the same normal form (h_0 = u, h_i in ker phi for
i < d - p, and in shape A h_(d-p) = v with phi(v) = x0, so that U+ = span(h_0, ..., h_(d-p)) in
shape A and ker phi in shape B), Lemma 69 adds:

    (a) A_(h_i) x0 = phi(h_i) for h_i in U+                                 (Lemma 30(a))
    (b) A_(h_i) P in R for 0 < i < d - p                                     ((Q) with h' = u)
    (c) (I + A_v) P in R in shape A                                          (Lemma 62(a))
    (d) A_(h_i) X_1 in X_1 for h_i in U+                                     (Lemma 64(a))
    (e) A_m X_1 in span(x0) for m the sum of some non-empty set of the h_i in U+ other than u
                                                                              (Lemma 64)

(d) and (e) only when dim U+ = k = t - rho and k is 2 or 3; they are about an element of rank
exactly rho, with X_1 = ker A_u. (e) is encoded with one selector variable per choice of m. So
UNSAT for every orbit of a shape means that no system with t = 6 and dim V = 7 has an element of
rank 3 in that configuration. A SAT answer is checked by brute force and would give A(6) = 7,
whatever the facts.

Parts: selfcheck (pure Python: the selfcheck of a6_r3.py, hand counts of the facts, the CNF of the
facts against a direct check on random matrices, and the facts themselves on every anisotropic
system with t = dim V = 2 and on random systems), controls (those of m27, plus t = 2 at rank 0,
where (d) and (e) apply and the answer is SAT; needs python-sat), solve (one shape at t = 6; needs
python-sat), grade (the predictions of m29/predictions.md).

Usage: python a6_r3h.py --part selfcheck|controls|solve|grade [--shape A5|B4|B5]
                        [--budget-minutes 2] [--group-minutes 55] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

import a6_r3 as r3
import sat_aniso as sa

T = r3.T
RHO = r3.RHO
SHAPES = r3.SHAPES
# Controls: (t, d, rho, shape, p). The last one is Lemma 63 (ii) with u = a + b, where A_u = 0.
CONTROLS = r3.CONTROLS + ((2, 2, 0, "A", 1),)


# ---------- the facts of Lemma 69 ----------

def uplus(d, shape, p):
    """The indices i of the basis vectors h_i of the normal form that span U+."""
    kd = d - p
    return list(range(kd + 1)) if shape == "A" else list(range(kd))


def lemma64_applies(t, d, shape, p, rho):
    k = t - rho
    return k in (2, 3) and len(uplus(d, shape, p)) == k


def facts(t, d, shape, p, rho, x1, r):
    """(plain, alts). A condition (m, x, c, W) says A_m x + c x lies in span(W), where A_m is the
    sum of the A_i for i in m. Every plain condition holds, and so do all the conditions of at
    least one alternative (if there are any)."""
    kd = d - p
    pb = r3.p_basis(shape, p)
    up = uplus(d, shape, p)
    X1, R = r3.rref(list(x1)), r3.rref(list(r))
    plain = [((i,), 1, int(shape == "A" and i == kd), ()) for i in up[1:]]
    plain += [((i,), b, 0, R) for i in range(1, kd) for b in pb]
    if shape == "A":
        plain += [((kd,), b, 1, R) for b in pb]
    alts = []
    if lemma64_applies(t, d, shape, p, rho):
        rest = up[1:]
        plain += [((i,), x, 0, X1) for i in rest for x in X1]
        for c in range(1, 1 << len(rest)):
            m = tuple(rest[j] for j in range(len(rest)) if (c >> j) & 1)
            alts.append([(m, x, 0, (1,)) for x in X1])
    return plain, alts


def fact_counts(t, d, shape, p, rho, x1, r):
    """[plain conditions, their linear equations, alternatives]."""
    plain, alts = facts(t, d, shape, p, rho, x1, r)
    return [len(plain), sum(t - len(c[3]) for c in plain), len(alts)]


def holds(cond, As, t):
    m, x, c, W = cond
    a = 0
    for i in m:
        a ^= As[i]
    return r3.in_span(tuple(W), sa.mat_apply(a, x, t) ^ (x if c else 0))


def facts_hold(plain, alts, As, t):
    return (all(holds(c, As, t) for c in plain)
            and (not alts or any(all(holds(c, As, t) for c in alt) for alt in alts)))


def equations(cond, A, t):
    """[(literals, rhs)]: f(A_m x + c x) = 0 for f in a basis of the functionals that vanish on W."""
    m, x, c, W = cond
    out = []
    for f in sa.nullspace(list(W), t):
        lits = [A[i][row][col] for i in m for row in range(t) if (f >> row) & 1
                for col in range(t) if (x >> col) & 1]
        out.append((lits, sa.parity(f & x) if c else 0))
    return out


def add_facts(cnf, A, t, plain, alts):
    """Add the facts to cnf; return the selector variables of the alternatives."""
    for cond in plain:
        for lits, rhs in equations(cond, A, t):
            cnf.xor_eq(lits, rhs)
    sel = []
    for alt in alts:
        s = cnf.new()
        sel.append(s)
        for cond in alt:
            for lits, rhs in equations(cond, A, t):
                if not lits:
                    if rhs:
                        cnf.clauses.append([-s])
                    continue
                z = cnf.xor_def(lits)
                cnf.clauses.append([-s, z] if rhs else [-s, -z])
    if sel:
        cnf.clauses.append(list(sel))
    return sel


def encode_r3h(t, d, shape, p, rho, x1, r):
    cnf, names = r3.encode_r3(t, d, shape, p, x1, r)
    plain, alts = facts(t, d, shape, p, rho, x1, r)
    add_facts(cnf, names[0], t, plain, alts)
    return cnf, names


# ---------- the facts on real systems (coordinate-free) ----------

FACT_KEYS = ("a", "b", "c", "d", "e")


def new_counts():
    return {f"{k}_{w}": 0 for k in FACT_KEYS for w in ("tested", "failed")}


def lemma_check(at, sv, d, t, st):
    """For every u != 0 of an anisotropic system (alpha table at, value table sv), test each fact
    of Lemma 69 that applies, in coordinate-free form, and count the tests and the failures."""
    n = 1 << d

    def count(key, ok):
        st[key + "_tested"] += 1
        st[key + "_failed"] += not ok

    for u in range(1, n):
        x0 = sv[u]
        phi = [sv[u ^ h] ^ x0 ^ sv[h] for h in range(n)]
        P = r3.rref(phi)
        R = r3.rref([sa.mat_apply(at[u], 1 << c, t) for c in range(t)])
        X1 = r3.rref(sa.nullspace(sa.rows_of(at[u], t), t))
        up = [h for h in range(n) if phi[h] in (0, x0)]
        for h in up:
            count("a", sa.mat_apply(at[h], x0, t) == phi[h])
            if phi[h] == 0:
                count("b", all(r3.in_span(R, sa.mat_apply(at[h], y, t)) for y in P))
            else:
                count("c", all(r3.in_span(R, sa.mat_apply(at[h], y, t) ^ y) for y in P))
        k = len(X1)
        if k in (2, 3) and len(up) == 1 << k:
            count("d", all(r3.in_span(X1, sa.mat_apply(at[h], x, t)) for h in up for x in X1))
            count("e", any(all(r3.in_span((x0,), sa.mat_apply(at[m], x, t)) for x in X1)
                           for m in up if m not in (0, u)))


def all_t2_systems():
    """Every anisotropic system with t = dim V = 2, as (alpha table, value table)."""
    out = []
    for a0, a1 in itertools.product(range(16), repeat=2):
        for s0, s1 in itertools.product(range(1, 4), repeat=2):
            for b in range(4):
                at, sv = sa.tables([a0, a1], [s0, s1], {(0, 1): b}, 2)
                if sa.anisotropic(sv) and sa.is_system(at, sv, 2, 2):
                    out.append((at, sv))
    return out


def random_condition(rng, t, d):
    m = tuple(sorted(rng.sample(range(d), rng.randint(1, 2))))
    W = r3.rref([rng.randrange(1, 1 << t) for _ in range(rng.choice((0, t - 1, t - 1, t - 2)))])
    return (m, rng.randrange(1, 1 << t), rng.randint(0, 1), W)


def encoding_check(rng, trials, t=3, d=3):
    """The CNF of add_facts against facts_hold on random matrices (no system needed)."""
    st = {"trials": 0, "true": 0, "disagree": 0}
    for _ in range(trials):
        plain = [random_condition(rng, t, d) for _ in range(rng.randint(0, 2))]
        alts = [[random_condition(rng, t, d) for _ in range(rng.randint(1, 2))]
                for _ in range(rng.randint(0, 3))]
        As = [rng.getrandbits(t * t) for _ in range(d)]
        cnf, names = sa.encode(t, d, star=False, aniso=False, echelon=False)
        sel = add_facts(cnf, names[0], t, plain, alts)
        val = sa.assignment(cnf, names, As, [0] * d, {key: 0 for key in names[2]}, t, d)
        for s, alt in zip(sel, alts):
            val[s] = all(holds(c, As, t) for c in alt)
        want = facts_hold(plain, alts, As, t)
        st["trials"] += 1
        st["true"] += want
        st["disagree"] += sa.satisfies(cnf, val) != want
    return st


# ---------- selfcheck ----------

# Hand values (m29/predictions.md): (t, rho, shape, p) -> [plain conditions, equations, alts].
HAND_FACTS = {(6, 3, "A", 5): [18, 60, 3], (6, 3, "B", 4): [16, 54, 3], (6, 3, "B", 5): [6, 21, 0],
              (2, 1, "A", 1): [2, 3, 0], (2, 1, "B", 1): [0, 0, 0], (2, 0, "A", 1): [4, 4, 1],
              (4, 2, "A", 3): [8, 20, 0], (4, 2, "B", 3): [6, 14, 1], (4, 2, "B", 2): [6, 16, 0]}
# Every anisotropic system with t = dim V = 2 (Lemma 63 = Lemma 34): 24, and the tests per fact.
HAND_T2 = {"systems": 24, "a_tested": 216, "b_tested": 180, "c_tested": 36, "d_tested": 36,
           "e_tested": 36}


def selfcheck():
    st = {"r3": all(r3.selfcheck()["graded"].values()), "fact_counts": {}}
    cases = [(t, d, rho, s, p) for t, d, rho, s, p in CONTROLS] + [
        (T, T + 1, RHO, s, p) for s, p in SHAPES.values()]
    for t, d, rho, s, p in cases:
        x1, r, _ = r3.orbits(t, s, p, rho)[0]
        st["fact_counts"][f"t{t}_r{rho}_{s}{p}"] = fact_counts(t, d, s, p, rho, x1, r)
    st["encoding"] = encoding_check(random.Random(29), 400)
    t2 = new_counts()
    systems = all_t2_systems()
    for at, sv in systems:
        lemma_check(at, sv, 2, 2, t2)
    t2["systems"] = len(systems)
    st["t2"] = t2
    rnd = new_counts()
    rnd["systems"] = 0
    for t, d, As, ss, B in sa.random_examples(random.Random(2029), 300):
        at, sv = sa.tables(As, ss, B, d)
        if sa.is_system(at, sv, d, t) and sa.anisotropic(sv):
            rnd["systems"] += 1
            lemma_check(at, sv, d, t, rnd)
    st["random"] = rnd
    st["graded"] = {
        "r3_selfcheck": st["r3"],
        "fact_counts": all(st["fact_counts"][f"t{t}_r{rho}_{s}{p}"] == v
                           for (t, rho, s, p), v in HAND_FACTS.items()),
        "encoding_agrees": st["encoding"]["disagree"] == 0,
        "encoding_nontrivial": 0 < st["encoding"]["true"] < st["encoding"]["trials"],
        "t2_counts": all(t2[k] == v for k, v in HAND_T2.items()),
        "no_failures": all(c[f"{k}_failed"] == 0 for c in (t2, rnd) for k in FACT_KEYS)}
    return st


# ---------- solving ----------

def instance_name(t, rho, shape, p, idx):
    return f"r3h_t{t}_r{rho}_{shape}{p}_o{idx:03d}"


def specs(t, d, rho, shape, p):
    """The orbits of a6_r3.orbits, in the same order as job m27 (index idx = m27's o-number)."""
    return [{"t": t, "d": d, "rho": rho, "shape": shape, "p": p, "x1": list(x1), "r": list(r),
             "size": size, "name": instance_name(t, rho, shape, p, idx)}
            for idx, (x1, r, size) in enumerate(r3.orbits(t, shape, p, rho))]


def child(spec_path, solver, path):
    from pysat.solvers import Solver
    with open(spec_path) as f:
        sp = json.load(f)
    t, d = sp["t"], sp["d"]
    cnf, names = encode_r3h(t, d, sp["shape"], sp["p"], sp["rho"], sp["x1"], sp["r"])
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
        As, ss, B = sa.decode(s.get_model(), names, t, d)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_one(spec, solver, budget_seconds, out_dir):
    t, d, rho, shape, p = spec["t"], spec["d"], spec["rho"], spec["shape"], spec["p"]
    name = spec["name"]
    spec_path = os.path.join(out_dir, name + ".spec.json")
    with open(spec_path, "w") as f:
        json.dump(spec, f)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", spec_path,
           "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update(spec)
    res["invariants"] = r3.invariants(t, shape, p, spec["x1"], spec["r"])
    res["wall_seconds"] = round(time.time() - start, 2)
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and r3.in_normal_form(As, ss, B, t, d, shape, p, spec["x1"], spec["r"]))
        plain, alts = facts(t, d, shape, p, rho, spec["x1"], spec["r"])
        res["facts_hold"] = facts_hold(plain, alts, As, t)
        res["facts"] = r3.model_facts(As, ss, B, t, d)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def run_group(sps, solver, budget_seconds, group_seconds, out_dir):
    """The instances in order; once the group budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for sp in sps:
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = dict(sp, status="SKIPPED")
            with open(os.path.join(out_dir, sp["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(sp, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


# ---------- grading ----------

def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if (fn.startswith("r3h_") and fn.endswith(".json") and not fn.endswith(".child.json")
                and not fn.endswith(".spec.json")):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    for name, r in results.items():
        if r.get("t") == T:
            continue
        s = r.get("status", "missing")
        if s in ("SAT", "UNSAT"):
            graded[name] = s == r3.expected_control(r["t"], r["shape"], r["r"])
            if s == "SAT":
                graded[name + "_verified"] = bool(r.get("verified"))
                graded[name + "_facts_hold"] = bool(r.get("facts_hold"))
        else:
            ungraded[name] = s
    per_shape = {}
    for key, (s, p) in SHAPES.items():
        st = [r for n, r in sorted(results.items()) if r.get("t") == T and r["shape"] == s
              and r["p"] == p]
        status = [r.get("status") for r in st]
        per_shape[key] = {"instances": len(st),
                          "counts": {x: status.count(x) for x in sorted(set(status))},
                          "all_unsat": bool(st) and all(x == "UNSAT" for x in status),
                          "undecided": [r["name"] for r in st if r.get("status") != "UNSAT"]}
        for r in st:
            if r.get("status") == "SAT":
                graded[r["name"] + "_verified"] = bool(r.get("verified"))
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "per_shape": per_shape, "times": times,
            "any_sat_6": any(r.get("status") == "SAT" for r in results.values()
                             if r.get("t") == T)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--shape", choices=sorted(SHAPES), default="A5")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=2.0)
    ap.add_argument("--group-minutes", type=float, default=55.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="spec.json")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.spec, args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        sps = [sp for t, d, rho, s, p in CONTROLS for sp in specs(t, d, rho, s, p)]
        out = run_group(sps, args.solver, 120, 3600, args.out_dir)
        print(f"SUMMARY controls {json.dumps(out, sort_keys=True)}", flush=True)
    elif args.part == "solve":
        s, p = SHAPES[args.shape]
        sps = specs(T, T + 1, RHO, s, p)
        out = run_group(sps, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY solve {args.shape} instances {len(sps)} {json.dumps(out, sort_keys=True)}",
              flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_6 {out['any_sat_6']} "
              + " ".join(f"{k} {v['counts']}" for k, v in out["per_shape"].items()), flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
