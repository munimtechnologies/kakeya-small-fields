# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m50: does CryptoMiniSat with native XOR constraints decide m42.py's instances faster than
CaDiCaL? A measured comparison, with predictions written before it ran (m50-predictions.md).

Every job so far (m8 to m49) solved the CNF of sat_aniso.encode with CaDiCaL 1.9.5 (pysat), where
each linear condition over F_2 is cut into parity clauses of at most 4 variables. The instances are
full of such conditions: (*) and (Q) are sums of products, anisotropy is a chain of sums, and the
hints of m42.py are linear. CryptoMiniSat 5 (pycryptosat) takes XOR constraints natively. This job
builds the same instances (m42.build, unchanged) with one change: CNF.xor_eq records each linear
condition as one XOR constraint instead of cutting it (XorCNF below; the products, the unit clauses
and the anisotropy clauses are the same clauses), and solves them with pycryptosat at its default
settings, one thread.

Arms:
  cadical   m42.py's solver (cadical195) on m42.py's CNF: a same-host speed control
  cms_cnf   CryptoMiniSat on m42.py's CNF (no native XOR): separates the solver from the encoding
  xor       CryptoMiniSat on the XorCNF instance

Instances (representatives as recorded by jobs m42a, m42c and m42d; CaDiCaL times from jobs m45a
and m46, wall seconds):
  calibration  9 classes that CaDiCaL showed UNSAT: 7 of (B5) in 43 to 356 s, 2 of (B6) in 265 and
               347 s
  targets      5 classes that no budget has decided: three with d = 3 (A_u^2 = 0), two with d = 1

Parts: check (pure Python), controls (tiny solves and the planted system, xor arm), solve, grade.

Usage: python m50.py --part check|controls|solve|grade [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import statistics
import subprocess
import sys
import time

import m42
import m46
import sat_aniso as sa

# (B6): X_1 = span(e_0, ..., e_3) for every pair orbit (m45.py); the images R and the
# representatives that job m42a recorded, for the classes used here.
B6_X1 = (8, 4, 2, 1)
B6_R = {2: (8, 4, 3), 8: (32, 16, 2), 12: (64, 32, 17)}
B6_AU = {"r3b_t7_B6_o002_c000": 34086976, "r3b_t7_B6_o008_c000": 558345756672,
         "r3b_t7_B6_o012_c003": 71498320576624, "r3b_t7_B6_o012_c006": 72048076390512}
# CaDiCaL's times on the calibration classes (UNSAT): m46 grade.json (B5), notes/a40.md (B6).
CAD_TIMES = {"r3b_t7_B5_o042_c000": 42.95, "r3b_t7_B5_o026_c002": 46.01,
             "r3b_t7_B5_o013_c002": 52.39, "r3b_t7_B5_o023_c002": 66.83,
             "r3b_t7_B5_o036_c000": 89.11, "r3b_t7_B5_o047_c003": 175.01,
             "r3b_t7_B5_o004_c000": 356.2, "r3b_t7_B6_o012_c006": 265.0,
             "r3b_t7_B6_o012_c003": 347.0}
CALIB = list(CAD_TIMES)
TARGETS = ["r3b_t7_B5_o000_c000", "r3b_t7_B5_o020_c000", "r3b_t7_B6_o002_c000",
           "r3b_t7_B6_o008_c000", "r3b_t7_B5_o027_c001"]
HOST_CONTROL = ["r3b_t7_B5_o042_c000", "r3b_t7_B5_o026_c002"]
# d = dim(X_1 n R), counted by hand from the pair tables (m50-predictions.md).
HAND_D = {"r3b_t7_B5_o042_c000": 2, "r3b_t7_B5_o026_c002": 1, "r3b_t7_B5_o013_c002": 2,
          "r3b_t7_B5_o023_c002": 2, "r3b_t7_B5_o036_c000": 2, "r3b_t7_B5_o047_c003": 0,
          "r3b_t7_B5_o004_c000": 2, "r3b_t7_B6_o012_c006": 0, "r3b_t7_B6_o012_c003": 0,
          "r3b_t7_B5_o000_c000": 3, "r3b_t7_B5_o020_c000": 3, "r3b_t7_B6_o002_c000": 3,
          "r3b_t7_B6_o008_c000": 1, "r3b_t7_B5_o027_c001": 1}
SMALL = ((2, 2, "SAT"), (2, 3, "UNSAT"), (3, 3, "SAT"), (3, 4, "UNSAT"))
TARGET_CAP = 720.0
HOST_CAP = 300.0


def calib_cap(name):
    """Three times CaDiCaL's time, at least 120 s, at most 600 s."""
    return min(600.0, max(120.0, 3 * CAD_TIMES[name]))


# ---------- the XOR encoding ----------

class XorCNF(sa.CNF):
    """sat_aniso.CNF, except that xor_eq keeps each linear condition as one XOR constraint
    (self.xors: (positive variables, rhs)) instead of cutting it into parity clauses."""

    def __init__(self):
        super().__init__()
        self.xors = []

    def xor_eq(self, lits, rhs):
        count = {}
        for lit in lits:
            if lit < 0:
                rhs ^= 1
                lit = -lit
            count[lit] = count.get(lit, 0) ^ 1
        vs = [v for v, c in count.items() if c]
        if not vs:
            if rhs:
                self.clauses.append([])
        elif len(vs) == 1:
            self.clauses.append([vs[0]] if rhs else [-vs[0]])
        else:
            self.xors.append((vs, int(rhs)))


def with_xor(fn, *args):
    """fn(*args) with sat_aniso.encode building an XorCNF."""
    saved = sa.CNF
    sa.CNF = XorCNF
    try:
        return fn(*args)
    finally:
        sa.CNF = saved


def accepts(cnf, val):
    """The assignment val satisfies every clause and, for an XorCNF, every XOR constraint."""
    return sa.satisfies(cnf, val) and all(
        sum(val[v] for v in vs) % 2 == rhs for vs, rhs in getattr(cnf, "xors", ()))


# ---------- instances ----------

def spec_of(name):
    shape, pi, ci = name[7:9], int(name[11:14]), int(name[16:19])     # r3b_t7_B5_oPPP_cCCC
    if shape == "B5":
        return {"name": name, "kind": "main", "t": m42.T, "d": m42.D, "p": 5, "pair": pi,
                "cls": ci, "x1": list(m46.x1_of(pi)), "r": list(m46.PAIR_R[pi]),
                "au": m46.OPEN[name]}
    return {"name": name, "kind": "main", "t": m42.T, "d": m42.D, "p": 6, "pair": pi, "cls": ci,
            "x1": list(B6_X1), "r": list(B6_R[pi]), "au": B6_AU[name]}


def small_spec(t, d):
    return {"name": f"small_t{t}_d{d}", "kind": "small", "t": t, "d": d}


def build(spec, arm):
    """(cnf, names) of an instance for an arm."""
    if spec["kind"] == "small":
        def make():
            return sa.encode(spec["t"], spec["d"], echelon=False)
    else:
        def make():
            cnf, names, _ = m42.build(spec)
            return cnf, names
    return with_xor(make) if arm == "xor" else make()


# ---------- check (pure Python) ----------

def check():
    start = time.time()
    st = {"seconds": None}
    reps = {}
    for p in (5, 6):
        sps, _ = m42.instances(m42.T, m42.D, p, m42.RHO)
        reps.update({s["name"]: s["au"] for s in sps})
    names = CALIB + TARGETS
    specs = [spec_of(n) for n in names]
    rng = random.Random(5050)
    agree = disagree = good = 0
    for t, d, As, ss, B in sa.random_examples(rng, 160):
        at, sv = sa.tables(As, ss, B, d)
        ok = sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
        plain = sa.encode(t, d, echelon=False)
        xcnf = with_xor(sa.encode, t, d, True, True, False)     # star, aniso, no echelon
        a = accepts(plain[0], sa.assignment(plain[0], plain[1], As, ss, B, t, d))
        b = accepts(xcnf[0], sa.assignment(xcnf[0], xcnf[1], As, ss, B, t, d))
        good += ok
        if a == b == ok:
            agree += 1
        else:
            disagree += 1
    As, ss, B = m42.planted()
    pc, pn = build(m42.planted_spec(), "xor")
    probe, probe_names = build(specs[0], "xor")
    plain_probe, _ = build(specs[0], "cnf")
    st.update({"random_cases": agree + disagree, "random_good": good, "random_disagree": disagree,
               "probe_xors": len(probe.xors), "probe_clauses": len(probe.clauses),
               "plain_clauses": len(plain_probe.clauses), "probe_vars": probe.nv,
               "plain_vars": plain_probe.nv})
    st["graded"] = {
        "reps": all(reps.get(s["name"]) == s["au"] for s in specs),
        "members": all(m42.kernel(s["au"], 7) == tuple(s["x1"])
                       and m42.column_space(s["au"], 7) == tuple(s["r"])
                       and sa.rank_f2(m42.cols_of(s["au"], 7)) == 3 for s in specs),
        "hand_d": all(m42.dim_meet(tuple(s["x1"]), tuple(s["r"])) == HAND_D[s["name"]]
                      for s in specs),
        "xor_agrees_with_cnf": disagree == 0 and 0 < good < agree,
        "planted_accepted": accepts(pc, sa.assignment(pc, pn, As, ss, B, 6, 6)),
        "probe_units_consistent": m42.units_consistent(probe),
        "same_products": probe.nv < plain_probe.nv and len(probe.xors) > 0}
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- solving ----------

def child(spec, arm, path):
    if arm == "cadical":
        m42.child(spec, "cadical195", path)
        return
    from pycryptosat import Solver
    cnf, names = build(spec, arm)
    start = time.time()
    if any(len(c) == 0 for c in cnf.clauses):
        res = {"status": "UNSAT", "solver": "trivial", "seconds": 0.0}
    else:
        s = Solver(threads=1)
        for c in cnf.clauses:
            s.add_clause(c)
        for vs, rhs in getattr(cnf, "xors", ()):
            s.add_xor_clause(vs, bool(rhs))
        ok, sol = s.solve()
        res = {"status": "SAT" if ok else ("UNSAT" if ok is False else "UNKNOWN"),
               "solver": "cryptominisat5", "vars": cnf.nv, "clauses": len(cnf.clauses),
               "xors": len(getattr(cnf, "xors", ())), "seconds": round(time.time() - start, 2)}
        if ok:
            model = [v if sol[v] else -v for v in range(1, len(sol))]
            As, ss, B = sa.decode(model, names, spec["t"], spec["d"])
            res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    with open(path, "w") as f:
        json.dump(res, f)


def verify(spec, res):
    t, d = spec["t"], spec["d"]
    As, ss = res["A"], res["s"]
    B = {(i, k): v for i, k, v in res["B"]}
    at, sv = sa.tables(As, ss, B, d)
    ok = sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
    if spec["kind"] != "small":
        _, _, au, s0, phis, _, _ = m42.params(spec)
        ok = ok and As[0] == au and ss[0] == s0 and all(
            phis[i] is None or B[(0, i)] == phis[i] for i in range(1, d))
        ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
        res["max_rank"] = max(ranks)
        res["rank_u"] = ranks[0]
    res["verified"] = ok


def solve_one(spec, arm, budget, out_dir):
    tag = f"{spec['name']}__{arm}"
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--arm", arm, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"name": spec["name"], "kind": spec["kind"], "arm": arm,
                "wall_seconds": round(time.time() - start, 2), "budget_seconds": round(budget, 1)})
    if res["status"] == "SAT":
        verify(spec, res)
    with open(os.path.join(out_dir, tag + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {tag}: {res['status']} {res['wall_seconds']} s", flush=True)
    return res


def plan():
    """(name, arm, cap) in running order."""
    out = [(n, "cadical", HOST_CAP) for n in HOST_CONTROL]
    out += [(n, "xor", calib_cap(n)) for n in CALIB]
    out += [(n, "cms_cnf", calib_cap(n)) for n in CALIB[:3]]
    out += [(n, "xor", TARGET_CAP) for n in TARGETS]
    return out


def run_solve(group_seconds, out_dir):
    start = time.time()
    counts = {}
    for name, arm, cap in plan():
        left = group_seconds - (time.time() - start)
        if left < 30:
            res = {"name": name, "arm": arm, "status": "SKIPPED"}
            with open(os.path.join(out_dir, f"{name}__{arm}.json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(spec_of(name), arm, min(cap, left - 15), out_dir)
        counts[f"{arm}_{res['status']}"] = counts.get(f"{arm}_{res['status']}", 0) + 1
    print(f"SUMMARY solve {json.dumps(counts, sort_keys=True)}", flush=True)


def run_controls(out_dir):
    for t, d, _ in SMALL:
        solve_one(small_spec(t, d), "xor", 120, out_dir)
    solve_one(m42.planted_spec(), "xor", 300, out_dir)


# ---------- grading (pre-registered in m50-predictions.md) ----------

def load(out_dir, name, arm):
    path = os.path.join(out_dir, f"{name}__{arm}.json")
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


def grade(out_dir):
    graded, ungraded, report = {}, {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    for t, d, want in SMALL:
        r = load(out_dir, f"small_t{t}_d{d}", "xor")
        st = r and r.get("status")
        if st in ("SAT", "UNSAT"):
            graded[f"small_t{t}_d{d}"] = st == want and (st == "UNSAT" or bool(r.get("verified")))
        else:
            ungraded[f"small_t{t}_d{d}"] = st
    r = load(out_dir, "r3b_planted", "xor")
    st = r and r.get("status")
    if st in ("SAT", "UNSAT"):
        graded["planted_sat"] = st == "SAT" and bool(r.get("verified"))
    else:
        ungraded["planted"] = st
    ratios, times = [], {}
    for name, arm, _ in plan():
        r = load(out_dir, name, arm)
        if r is None:
            continue
        st = r.get("status")
        times[f"{name}__{arm}"] = [st, r.get("wall_seconds")]
        if st == "SAT":
            graded[f"{name}__{arm}_verified"] = bool(r.get("verified"))
            graded[f"{name}__{arm}_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
            if name in CAD_TIMES:
                graded[f"{name}__{arm}_agrees_with_cadical"] = False
    for name in CALIB:
        r = load(out_dir, name, "xor")
        if r is None or r.get("status") in ("SKIPPED", "ERROR", None):
            continue
        ratios.append(CAD_TIMES[name] / r["wall_seconds"] if r["status"] == "UNSAT" else 0.0)
    host = []
    for name in HOST_CONTROL:
        r = load(out_dir, name, "cadical")
        if r and r.get("status") == "UNSAT":
            host.append(r["wall_seconds"] / CAD_TIMES[name])
    xor_unsat = sum(1 for n in CALIB if (load(out_dir, n, "xor") or {}).get("status") == "UNSAT")
    report.update({
        "calib_xor_unsat": xor_unsat,
        "calib_ratios": [round(x, 3) for x in ratios],
        "calib_median_ratio": round(statistics.median(ratios), 3) if ratios else None,
        "host_ratios": [round(x, 3) for x in host],
        "host_comparable": bool(host) and all(0.5 <= x <= 2.0 for x in host),
        "targets_closed": [n for n in TARGETS
                           if (load(out_dir, n, "xor") or {}).get("status") == "UNSAT"],
        "times": times})
    report["xor_wins"] = (xor_unsat >= 7 and report["calib_median_ratio"] is not None
                          and report["calib_median_ratio"] >= 3)
    return {"graded": graded, "ungraded": ungraded, "report": report}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "solve", "child", "grade"],
                    default="check")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="{}")
    ap.add_argument("--arm", default="xor")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.arm, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.out_dir)
    elif args.part == "solve":
        run_solve(args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"xor_wins {out['report']['xor_wins']} "
              f"median_ratio {out['report']['calib_median_ratio']} "
              f"targets_closed {len(out['report']['targets_closed'])}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check()
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
