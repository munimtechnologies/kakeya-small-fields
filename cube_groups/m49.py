# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m49: Corollary 60 (notes/a39.md) as clauses, measured on the open classes of the rank-3
configuration (B6) for t = 7 and dim V = 9 that jobs m45b and m45a left UNKNOWN.

Corollary 60: in every class of (B6) with d = dim(ker A_u n Im A_u) >= 1, A_n != 0 for every
n != 0 in N = ker phi. In m42.py's normal form, N = span(h_0 = u, h_1, ..., h_(kd - 1)) (kd = 3 in
(B6)) and A_u is fixed, and h -> A_h is linear, so for n = e u + sum_(i in S) h_i (S non-empty,
e in {0, 1}) the condition is one clause over the entries of e A_u + sum_(i in S) A_(h_i): for
|S| = 1 a clause over the 49 variables of A_(h_i) (each literal flipped where e = 1 and A_u has a 1),
for |S| >= 2 the same over 49 auxiliary variables equal to the XOR of the entries (sat_aniso's
CNF.xor_def, shared by e = 0 and e = 1). In (B6) that is 6 clauses and 49 auxiliary variables.

Each instance is otherwise m42.py's, unchanged (the CNF of jobs m45a and m45b, which are the
controls: same representatives, same solver order, about the same budget). Parts:

    check   m45.py's check (the classification of (B6) as m42a recorded it), the clause count on a
            real instance, the clauses against a direct evaluation of "A_n != 0" on random and
            constructed maps, and the planted system at t = 6 (kd = 3, every A_n != 0) as a
            positive control: the clauses must accept it, and the solver must find a verified SAT.
    solve   a batch: a = the 13 classes m45b left open with d >= 1, b = the 10 m45a left open with
            d >= 1.
    grade   graded checks, and the status of each class against its control.

Usage: python m49.py --part check|solve|grade [--batch a|b] [--cap-seconds 624] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

import m42
import m45
import sat_aniso as sa

# d of each pair orbit of (B6) (Lemma 83, notes/a27.md; the kernel X_1 is span(e_0, ..., e_3)).
D_OF_PAIR = {0: 3, 1: 3, 2: 3, 3: 2, 4: 2, 5: 2, 6: 2, 7: 1, 8: 1, 9: 1, 10: 1, 11: 0, 12: 0}
# The controls: (job, status, budget in seconds) of the same CNF without the clauses.
CONTROL = {
    "r3b_t7_B6_o000_c000": ("m45b", "UNKNOWN", 624), "r3b_t7_B6_o002_c000": ("m45b", "UNKNOWN", 624),
    "r3b_t7_B6_o004_c000": ("m45b", "UNKNOWN", 624), "r3b_t7_B6_o004_c001": ("m45b", "UNKNOWN", 624),
    "r3b_t7_B6_o005_c002": ("m45b", "UNKNOWN", 624), "r3b_t7_B6_o005_c003": ("m45b", "UNKNOWN", 624),
    "r3b_t7_B6_o006_c000": ("m45b", "UNKNOWN", 624), "r3b_t7_B6_o006_c001": ("m45b", "UNKNOWN", 624),
    "r3b_t7_B6_o007_c004": ("m45b", "UNKNOWN", 624), "r3b_t7_B6_o008_c000": ("m45b", "UNKNOWN", 660),
    "r3b_t7_B6_o008_c001": ("m45b", "UNKNOWN", 660), "r3b_t7_B6_o008_c002": ("m45b", "UNKNOWN", 660),
    "r3b_t7_B6_o008_c003": ("m45b", "UNKNOWN", 660),
    "r3b_t7_B6_o009_c004": ("m45a", "UNKNOWN", 624), "r3b_t7_B6_o009_c006": ("m45a", "UNKNOWN", 624),
    "r3b_t7_B6_o009_c007": ("m45a", "UNKNOWN", 624), "r3b_t7_B6_o009_c008": ("m45a", "UNKNOWN", 624),
    "r3b_t7_B6_o009_c009": ("m45a", "UNKNOWN", 624), "r3b_t7_B6_o010_c000": ("m45a", "UNKNOWN", 624),
    "r3b_t7_B6_o010_c001": ("m45a", "UNKNOWN", 624), "r3b_t7_B6_o010_c002": ("m45a", "UNKNOWN", 624),
    "r3b_t7_B6_o010_c003": ("m45a", "UNKNOWN", 624), "r3b_t7_B6_o010_c005": ("m45a", "UNKNOWN", 624),
}
BATCHES = {"a": sorted(n for n, c in CONTROL.items() if c[0] == "m45b"),
           "b": sorted(n for n, c in CONTROL.items() if c[0] == "m45a")}
# Hand counts: (clauses, auxiliary variables) for kd = 3 ((B6)) and kd = 4 ((B5)).
HAND_COR60 = {3: (6, 49), 4: (14, 196)}
# Hand counts for the decision rule (predictions.md): classes that must close in each batch.
RULE = {"a": 4, "b": 3}
PLANTED_BUDGET = 240.0


# ---------- the clauses of Corollary 60 ----------

def add_cor60(cnf, names, t, kd, au):
    """A_n != 0 for every n = e u + sum_(i in S) h_i with S a non-empty subset of {1, ..., kd - 1}.
    Returns (clauses added, auxiliary variables added)."""
    A = names[0]
    nv0 = cnf.nv
    count = 0
    for size in range(1, kd):
        for S in itertools.combinations(range(1, kd), size):
            if size == 1:
                ent = A[S[0]]
            else:
                ent = [[cnf.xor_def([A[i][r][c] for i in S]) for c in range(t)] for r in range(t)]
            for e in (0, 1):
                cnf.clauses.append([-ent[r][c] if e and (au >> (t * r + c)) & 1 else ent[r][c]
                                    for r in range(t) for c in range(t)])
                count += 1
    return count, cnf.nv - nv0


def maps_on_n(As, kd):
    """A_n for every n = e u + sum_(i in S) h_i as above (As[0] = A_u), in the order of add_cor60."""
    out = []
    for size in range(1, kd):
        for S in itertools.combinations(range(1, kd), size):
            m = 0
            for i in S:
                m ^= As[i]
            out += [m, m ^ As[0]]
    return out


def extend(cnf, val):
    """val (on the A variables) extended to the auxiliary variables, as sa.assignment does."""
    for v in sorted(cnf.defs):
        kind = cnf.defs[v]
        if kind[0] == "and":
            val[v] = val[kind[1]] and val[kind[2]]
        else:
            val[v] = sum(val[x] for x in kind[1]) % 2 == 1
    return val


def trial_maps(rng, t, kd, au):
    """Random A_(h_1), ..., A_(h_(kd-1)), often forced so that some A_n = 0."""
    As = [au] + [rng.getrandbits(t * t) for _ in range(1, kd)]
    i = rng.randrange(1, kd)
    others = [As[j] for j in range(1, kd) if j != i]
    pick = rng.randrange(5)
    if pick == 1:
        As[i] = 0
    elif pick == 2:
        As[i] = au
    elif pick == 3 and others:
        As[i] = others[0]
    elif pick == 4 and others:
        As[i] = others[-1] ^ au
        if len(others) > 1:
            As[i] ^= others[0]
    return As


def semantic_check(t, kd, au, trials, seed):
    """The clauses (on a CNF with only the A variables) hold exactly when every A_n != 0."""
    cnf = sa.CNF()
    A = [[[cnf.new() for c in range(t)] for r in range(t)] for i in range(kd)]
    add_cor60(cnf, (A, None, None), t, kd, au)
    rng = random.Random(seed)
    agree, seen = True, set()
    for _ in range(trials):
        As = trial_maps(rng, t, kd, au)
        val = {A[i][r][c]: bool((As[i] >> (t * r + c)) & 1)
               for i in range(kd) for r in range(t) for c in range(t)}
        want = all(maps_on_n(As, kd))
        agree = agree and sa.satisfies(cnf, extend(cnf, val)) == want
        seen.add(want)
    return {"agree": agree, "both_outcomes": seen == {True, False}, "trials": trials}


# ---------- instances ----------

def spec_of(name):
    return m45.spec_of(name)


def build(spec):
    cnf, names, hints = m42.build(spec)
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    n, aux = add_cor60(cnf, names, t, kd, au)
    return cnf, names, hints, n, aux


def d_of(au, t=7):
    return m42.dim_meet(m42.kernel(au, t), m42.column_space(au, t))


# ---------- solving (as m42.py, with build() above) ----------

def child(spec, solver, path):
    from pysat.solvers import Solver
    cnf, names, _, _, _ = build(spec)
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
        As, ss, B = sa.decode(s.get_model(), names, spec["t"], spec["d"])
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def write(res, out_dir):
    with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
        json.dump(res, f, indent=1)


def solve_one(spec, solver, budget_seconds, out_dir):
    path = os.path.join(out_dir, spec["name"] + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
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
    res.update({"wall_seconds": round(time.time() - start, 2),
                "budget_seconds": round(budget_seconds, 1)})
    if res["status"] == "SAT":
        t, d, au, s0, phis, kd, pvecs = m42.params(spec)
        As, ss = res["A"], res["s"]
        B = {(i, k): v for i, k, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        nf = (As[0] == au and ss[0] == s0
              and all(phis[i] is None or B[(0, i)] == phis[i] for i in range(1, d)))
        res["verified"] = sa.is_system(at, sv, d, t) and sa.anisotropic(sv) and nf
        res["cor60_holds"] = all(maps_on_n(As, kd))
        ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
        res["max_rank"] = max(ranks)
        res["rank_u"] = ranks[0]
    write(res, out_dir)
    print(f"solve {spec['name']}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


# ---------- parts ----------

def check(solver, out_dir):
    start = time.time()
    st = {"m45": m45.check()}
    graded = {"m45_" + k: bool(v) for k, v in st["m45"]["graded"].items()}
    probe = spec_of(BATCHES["a"][0])
    cnf, names, hints, n, aux = build(probe)
    st["probe"] = {"hints": hints, "cor60_clauses": n, "cor60_aux": aux, "vars": cnf.nv,
                   "clauses": len(cnf.clauses)}
    graded["probe_counts"] = (n, aux) == HAND_COR60[3] and hints == m42.HAND_HINTS["B6"]
    graded["probe_units"] = m42.units_consistent(cnf)
    graded["tables"] = (len(BATCHES["a"]) == 13 and len(BATCHES["b"]) == 10
                        and all(nm in m45.OPEN for nm in CONTROL))
    graded["d_at_least_1"] = all(d_of(m45.OPEN[nm]) == D_OF_PAIR[m45.pair_cls(nm)[0]] >= 1
                                 for nm in CONTROL)
    for kd in (3, 4):
        cnf2 = sa.CNF()
        A = [[[cnf2.new() for c in range(7)] for r in range(7)] for i in range(kd)]
        graded[f"hand_count_kd{kd}"] = add_cor60(cnf2, (A, None, None), 7, kd,
                                                 m45.OPEN[probe["name"]]) == HAND_COR60[kd]
        sem = semantic_check(7, kd, m45.OPEN[probe["name"]], 400, 49 + kd)
        st[f"semantic_kd{kd}"] = sem
        graded[f"semantic_kd{kd}"] = sem["agree"] and sem["both_outcomes"]
    # The positive control: the planted system at t = 6 (kd = 3) has every A_n != 0.
    As, ss, B = m42.planted()
    graded["planted_all_nonzero"] = all(maps_on_n(As, 3))
    pspec = m42.planted_spec()
    pc, pn, _, pcount, paux = build(pspec)
    graded["planted_counts"] = (pcount, paux) == (6, 36)
    graded["planted_accepted"] = sa.satisfies(pc, sa.assignment(pc, pn, As, ss, B, 6, 6))
    res = solve_one(pspec, solver, PLANTED_BUDGET, out_dir)
    if res["status"] in ("SAT", "UNSAT"):
        graded["planted_sat"] = res["status"] == "SAT" and bool(res.get("verified"))
    else:
        st["planted_ungraded"] = res["status"]
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


def run_solve(batch, solver, cap_seconds, out_dir):
    counts = {}
    for name in BATCHES[batch]:
        res = solve_one(spec_of(name), solver, cap_seconds, out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    print(f"SUMMARY solve batch {batch} instances {len(BATCHES[batch])} "
          f"{json.dumps(counts, sort_keys=True)}", flush=True)


def grade(batch, out_dir):
    """Graded: the check, and every SAT verified (a system, anisotropic, normal form, Corollary 60,
    rank A_u = 3, every rank <= 4). Reported: each class against its control, and the rule."""
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    counts, rows = {}, {}
    for name in BATCHES[batch]:
        path = os.path.join(out_dir, name + ".json")
        if not os.path.exists(path):
            ungraded[name] = "missing"
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        counts[s] = counts.get(s, 0) + 1
        job, cst, cb = CONTROL[name]
        rows[name] = {"status": s, "wall_seconds": r.get("wall_seconds"), "d": D_OF_PAIR[r["pair"]],
                      "control": f"{job} {cst} at {cb} s"}
        if s == "SAT":
            graded[name + "_verified"] = bool(r.get("verified")) and bool(r.get("cor60_holds"))
            graded[name + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    closed = counts.get("UNSAT", 0)
    return {"batch": batch, "graded": graded, "ungraded": ungraded, "counts": counts,
            "rows": rows, "closed_where_control_open": closed, "rule_needs": RULE[batch],
            "cor60_helps_by_rule": closed >= RULE[batch], "any_sat_7": counts.get("SAT", 0) > 0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "child", "grade"], default="check")
    ap.add_argument("--batch", choices=sorted(BATCHES), default="a")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--cap-seconds", type=float, default=624.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.batch, args.solver, args.cap_seconds, args.out_dir)
    elif args.part == "grade":
        out = grade(args.batch, args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"closed {out['closed_where_control_open']} of {len(BATCHES[args.batch])} "
              f"helps_by_rule {out['cor60_helps_by_rule']} any_sat_7 {out['any_sat_7']}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.solver, args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
