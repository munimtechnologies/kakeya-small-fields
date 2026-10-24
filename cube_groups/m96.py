# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m96: why the positive control of job m95 failed, read off minimal sets of hypotheses
(notes/a88.md; cube_groups/m96-predictions.md).

What came back on 2026-10-23 (jobs m95a and m95b, notes/a88.md): all 23 orbits of type (N4) and all
159 (orbit, hyperplane) instances with d = 3 at (t, dim V) = (8, 11) were UNSAT, but so was the
positive control: the pilot's CNF without its 2^11 - 1 anisotropy clauses ("relax", 0.79 s), and the
same at (6, 3) (0.11 s). By m95's rule nothing is claimed. The clauses (S) and (a) agree with Lemma
38(a) on a reading by hand, and Lemma 38(a) uses (*) and (Q) but not anisotropy, so a refutation
without anisotropy need not be a bug; it could also come from a wrong clause.

This job asks which hypotheses the refutation uses. The CNF of m94.encode_n4 (d = 4) or of
m95.encode_rank4 (d = 3) is rebuilt clause for clause, and every clause after the system equations
(*) gets a label: the group of the hypothesis it encodes (below). Each group is switched on or off by
a selector literal (solver assumptions), so one solver per instance answers:

    bare     no group: (*) alone, which the zero system satisfies
    full     every group, with anisotropy
    relax    every group but anisotropy (m95's control)
    core     a minimal set of groups that with (*) has no model: the solver's core of the relax
             CNF, shrunk by deleting one group at a time while the rest stays UNSAT
    ladder   relax without one family at a time

A minimal core is a short list of hypotheses whose clauses, with (*), have no model: what a hand
proof of the contradiction has to use. Every model found is decoded and checked against every clause
of the groups that were on (and of (*)), and for t <= 6 against (*) by brute force (is_system).

Groups (labels "family:detail"):

    nf:su, nf:Au_e<c>, nf:phi_v<i>                 the normal form of Lemma 35 (case_b.py)
    shape:s_v<i>, shape:b_v<i>_v<j>, shape:Av<i>_e<c>    the values of shape (c) (Lemma 37)
    units:T<c>          (N4): rows k to t - 1 of A_u e_(k+c) are 0
    units:D<v>          d = 3: rows k to t - 1 of A_u v are 0, v a basis vector of D (Lemma 97)
    outside:O           d = 3: rows k to t - 1 of A_u e_(k+l0) are not all 0
    inv:<sel>           the columns A_u e_(k+c), c in sel, do not add up to 0 (T one-to-one)
    lin:v<i>c<j>        (S) for column j of A_(v_i) on [e_k], ..., [e_(t-1)] (Lemma 38(a))
    a:v<i>n<j>          (a) for beta(v_i, v_(k-1+j)) (Lemma 38(a))
    aniso               the 2^d - 1 anisotropy clauses (one group)

Instances: group a, (t, k) = (4, 2) with M in {N, I + N, E, F} (the classes of 2 x 2 matrices other
than 0 and I) and (6, 3) with (M_1, M_2) = (N, N^2) (m94's control), (E_00, E_11), (E_00, E_12);
group b, (8, 4) with m94's pilot W = span(E_00, E_12, E_11 + E_22), d = 4 and d = 3 with f = 1.

Parts: selfcheck (the CNFs against m94.encode_n4 clause for clause, m95b's sizes, the label
counts), run, grade.

Usage: python m96.py --part selfcheck|run|grade --group a|b [--cap-seconds S] [--main-cap S]
       [--minutes M] [--out-dir DIR]
"""
import argparse
import json
import os
import threading
import time

import case_b as cb
import case_b_shapes as csh
import m94
import sat_aniso as sa

GROUPS = ("a", "b")
T4 = {"N": [[0, 0], [1, 0]], "IN": [[1, 0], [1, 1]], "E": [[1, 0], [0, 0]],
      "F": [[0, 1], [1, 1]]}
E00 = [[1, 0, 0], [0, 0, 0], [0, 0, 0]]
E11 = [[0, 0, 0], [0, 1, 0], [0, 0, 0]]
E12 = [[0, 0, 0], [0, 0, 1], [0, 0, 0]]
INSTANCES = {
    "a": [("t4_" + key, 4, 2, [M], None) for key, M in T4.items()]
    + [("t6_shift", 6, 3, [m94.SHIFT, m94.SHIFT2], None), ("t6_e00e11", 6, 3, [E00, E11], None),
       ("t6_e00e12", 6, 3, [E00, E12], None)],
    "b": [("t8_n4", 8, 4, m94.pilot_ms(), None), ("t8_d3_f1", 8, 4, m94.pilot_ms(), 1)]}
# [vars, clauses] recorded by job m94 (d = 4; also m95's M94_SIZES) and by job m95b for d3_o05_f01
# (orbit 5 of m95's list is the pilot's).
SIZES = {"t6_shift": [23124, 136183], "t8_n4": [142832, 905882], "t8_d3_f1": [142880, 906151]}
FAMILY_ORDER = ("a", "lin", "inv", "units", "outside", "shape", "nf", "aniso")
LADDER = (("units", "outside"), ("inv",), ("lin",), ("a",), ("lin", "a"), ("shape",), ("nf",))
BRUTE_T = 6          # (*) checked by brute force on models with t <= BRUTE_T
KEEP_MODELS = 4      # models of core deletions kept per instance


def family(label):
    return label.split(":")[0]


def order_key(label):
    f = family(label)
    return (FAMILY_ORDER.index(f) if f in FAMILY_ORDER else len(FAMILY_ORDER), label)


def family_counts(labels):
    out = {}
    for g in set(x for x in labels if x):
        out[family(g)] = out.get(family(g), 0) + 1
    return out


# ---------- hyperplanes (as in m95.py; bit l of a vector is the coordinate of [e_(k+l)]) ----------

def parity(x):
    return bin(x).count("1") & 1


def apply(M, v):
    n = len(M)
    return sum((sum(M[r][c] for c in range(n) if v >> c & 1) & 1) << r for r in range(n))


def invariant(Ms, f):
    n = len(Ms[0])
    D = [v for v in range(1 << n) if not parity(f & v)]
    return len(D) == 1 << (n - 1) and all(not parity(f & apply(M, v)) for M in Ms for v in D)


def low_bit(f):
    return (f & -f).bit_length() - 1


def d_basis(f, n):
    l0 = low_bit(f)
    return [(1 << l) | ((f >> l & 1) << l0) for l in range(n) if l != l0]


# ---------- the labelled CNF ----------

def aniso_indices(cnf, t):
    """The anisotropy clauses of sat_aniso.encode: all-positive, of length t, every variable a
    parity definition (m95.relax's rule; nothing else in sat_aniso.encode has that form)."""
    return [i for i, c in enumerate(cnf.clauses)
            if len(c) == t and all(x > 0 and cnf.defs.get(x, ("",))[0] == "xor" for x in c)]


def build(t, k, Ms, f=None):
    """(cnf, names, labels, info): the clauses of m94.encode_n4(t, k, Ms) (f None) or of
    m95.encode_rank4(t, k, Ms, f) (d = 3), in the same order, with labels[i] the group of clause i
    (None for the system equations (*) and the parity definitions of sat_aniso.encode)."""
    n = t - k
    d = t + k - 1
    if n != k or len(Ms) != k - 1 or not m94.check_tuple(Ms):
        raise ValueError("needs t = 2 k and k - 1 commuting matrices spanning a space of "
                         "dimension k - 1 without I")
    if f is not None and not invariant(Ms, f):
        raise ValueError("ker f is not invariant under the matrices")
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]
    labels = [None] * len(cnf.clauses)
    for i in aniso_indices(cnf, t):
        labels[i] = "aniso"

    def put(label, fn):
        start = len(cnf.clauses)
        fn()
        labels.extend([label] * (len(cnf.clauses) - start))

    # case_b.encode_case_b: the normal form of Lemma 35
    for r in range(t):
        put("nf:su", lambda: cnf.clauses.append([S[0][r]] if r == 0 else [-S[0][r]]))
        for c in range(k):
            put(f"nf:Au_e{c}", lambda: cnf.clauses.append([-A[0][r][c]]))
    for i in range(1, d):
        want = cb.wanted_phi(i, k)
        for r in range(t):
            v = B[(0, i)][r]
            put(f"nf:phi_v{i}", lambda: cnf.clauses.append([v] if (want >> r) & 1 else [-v]))
    # case_b_shapes.encode_shape(t, k, "c"): the values of shape (c)
    Sx, Bx, Cx = csh.shape_values(t, k, "c")
    for i, s in Sx.items():
        for r in range(t):
            put(f"shape:s_v{i}",
                lambda: cnf.clauses.append([S[i][r]] if (s >> r) & 1 else [-S[i][r]]))
    for (i, j), b in Bx.items():
        for r in range(t):
            put(f"shape:b_v{i}_v{j}",
                lambda: cnf.clauses.append([B[(i, j)][r]] if (b >> r) & 1 else [-B[(i, j)][r]]))
    for (i, c), colv in Cx.items():
        for r in range(t):
            put(f"shape:Av{i}_e{c}",
                lambda: cnf.clauses.append([A[i][r][c]] if (colv >> r) & 1 else [-A[i][r][c]]))
    info = {"start": len(cnf.clauses), "first_var": cnf.nv + 1, "d": 4 if f is None else 3}
    # m94.encode_n4 / m95.encode_rank4: the type, T one-to-one, (S), (a)
    if f is None:
        for r in range(k, t):
            for c in range(k, t):
                put(f"units:T{c - k}", lambda: cnf.clauses.append([-A[0][r][c]]))
    else:
        for v in d_basis(f, n):
            for r in range(k, t):
                put(f"units:D{v}", lambda: cnf.xor_eq(
                    [A[0][r][k + l] for l in range(n) if v >> l & 1], 0))
        l0 = low_bit(f)
        put("outside:O", lambda: cnf.clauses.append([A[0][r][k + l0] for r in range(k, t)]))
    rows = range(k) if f is None else range(t)
    for sel in range(1, 1 << n):
        cs = [k + c for c in range(n) if (sel >> c) & 1]
        if len(cs) == 1:
            put(f"inv:{sel}", lambda: cnf.clauses.append([A[0][r][cs[0]] for r in rows]))
        else:
            put(f"inv:{sel}", lambda: cnf.clauses.append(
                [cnf.xor_def([A[0][r][c] for c in cs]) for r in rows]))
    for i in range(1, k):
        M = Ms[i - 1]
        for j in range(n):
            for r in range(t):
                put(f"lin:v{i}c{j}", lambda: cnf.xor_eq(
                    [A[i][r][k + j]] + [A[0][r][k + l] for l in range(n) if M[l][j]], 0))
    for i in range(1, k):
        M = Ms[i - 1]
        for j in range(1, t):
            for l in range(n):
                v = B[(i, k - 1 + j)][k + l]
                put(f"a:v{i}n{j}",
                    lambda: cnf.clauses.append([v] if j >= k and M[l][j - k] else [-v]))
    info.update({"vars": cnf.nv, "clauses": len(cnf.clauses)})
    return cnf, names, labels, info


# ---------- one solver with a selector per group ----------

class Guarded:
    """An incremental solver for a labelled CNF: clause c of group g is added as c + [-s_g], and
    each call switches every group on (s_g assumed true) or off (s_g assumed false)."""

    def __init__(self, clauses, labels, nv, name="glucose4"):
        from pysat.solvers import Solver
        self.groups = sorted({x for x in labels if x}, key=order_key)
        self.sel = {g: nv + 1 + i for i, g in enumerate(self.groups)}
        self.of = {v: g for g, v in self.sel.items()}
        self.s = Solver(name=name)
        for c, lab in zip(clauses, labels):
            self.s.add_clause(c if lab is None else c + [-self.sel[lab]])
        self.calls = 0

    def solve(self, on, cap):
        on = set(on)
        assum = [self.sel[g] if g in on else -self.sel[g] for g in self.groups]
        timer = threading.Timer(cap, self.s.interrupt)
        start = time.time()
        timer.start()
        try:
            res = self.s.solve_limited(assumptions=assum, expect_interrupt=True)
        finally:
            timer.cancel()
        self.s.clear_interrupt()
        self.calls += 1
        return {True: "SAT", False: "UNSAT", None: "UNKNOWN"}[res], round(time.time() - start, 2)

    def core(self):
        return {self.of[x] for x in (self.s.get_core() or []) if x in self.of}

    def model(self):
        return self.s.get_model()

    def delete(self):
        self.s.delete()


def check_model(model, cnf, names, labels, on, t, k):
    """A model decoded to (A_i, s_i, B_ik) and read back: every clause of (*) and of the groups
    that were on, on the assignment the data induce (sat_aniso.assignment); (*) by brute force for
    t <= BRUTE_T."""
    d = t + k - 1
    As, ss, B = sa.decode(model, names, t, d)
    val = sa.assignment(cnf, names, As, ss, B, t, d)
    ok = all(any(val[x] if x > 0 else not val[-x] for x in c)
             for c, lab in zip(cnf.clauses, labels) if lab is None or lab in on)
    at, sv = sa.tables(As, ss, B, d)
    return {"clauses_ok": ok, "system": sa.is_system(at, sv, d, t) if t <= BRUTE_T else None,
            "anisotropic": sa.anisotropic(sv), "rank_Au": sa.rank_f2(sa.rows_of(As[0], t)),
            "A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]}


def min_core(g, start, cap, deadline, on_sat=None, first_cap=None):
    """A minimal UNSAT subset of the groups start (with (*) always on): the solver's core, then
    deletion of one group at a time in order_key order, keeping the solver's core of each UNSAT
    answer. A group stays when its deletion is SAT or UNKNOWN; the core is minimal if every group
    that stayed was SAT and the pass finished before the deadline."""
    status, sec = g.solve(start, first_cap or cap)
    if status != "UNSAT":
        return {"status": status, "seconds": sec}
    core = g.core() & set(start)
    kept, removed, complete = {}, [], True
    for lab in sorted(core, key=order_key):
        if lab not in core:
            continue
        if time.time() > deadline:
            complete = False
            break
        trial = core - {lab}
        st, _ = g.solve(trial, cap)
        if st == "UNSAT":
            core = g.core() & trial
            removed.append(lab)
        else:
            kept[lab] = st
            if st == "SAT" and on_sat is not None:
                on_sat(lab, trial)
    final, _ = g.solve(core, cap)
    return {"status": "UNSAT", "core": sorted(core, key=order_key), "size": len(core),
            "families": family_counts(sorted(core)), "kept": kept, "removed": len(removed),
            "complete": complete, "final": final,
            "minimal": complete and all(v == "SAT" for v in kept.values())}


# ---------- the parts ----------

def instance_specs(group):
    return INSTANCES[group]


def selfcheck(group, out_dir):
    g = {}
    rows = {}
    for name, t, k, Ms, f in instance_specs(group):
        cnf, _, labels, info = build(t, k, Ms, f)
        n, d = t - k, t + k - 1
        fams = family_counts(labels)
        want = {"nf": 1 + k + (d - 1), "shape": (k - 1) + (k - 1) * (k - 2) // 2 + (k - 1) * k,
                "inv": (1 << n) - 1, "lin": (k - 1) * n, "a": (k - 1) * (t - 1), "aniso": 1}
        want.update({"units": n} if f is None else {"units": n - 1, "outside": 1})
        g[name + "_labels"] = (fams == want and len(labels) == len(cnf.clauses)
                               and labels.count("aniso") == (1 << d) - 1)
        if f is None:
            theirs, _, _ = m94.encode_n4(t, k, Ms)
            g[name + "_equal_m94"] = cnf.clauses == theirs.clauses and cnf.nv == theirs.nv
            del theirs
        if name in SIZES:
            g[name + "_sizes"] = [cnf.nv, len(cnf.clauses)] == SIZES[name]
        rows[name] = {"vars": cnf.nv, "clauses": len(cnf.clauses), "families": fams,
                      "start": info["start"], "first_var": info["first_var"]}
        del cnf, labels
    out = {"graded": g, "instances": rows}
    with open(os.path.join(out_dir, f"m96{group}_selfcheck.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"selfcheck: {json.dumps(rows, sort_keys=True)}", flush=True)
    print(f"SUMMARY selfcheck group {group} all_match {all(g.values())} graded {len(g)} "
          f"{json.dumps(g, sort_keys=True)}", flush=True)
    return out


def run_instance(spec, cap, main_cap, minutes):
    name, t, k, Ms, f = spec
    start = time.time()
    deadline = start + minutes * 60
    cnf, names, labels, info = build(t, k, Ms, f)
    g = Guarded(cnf.clauses, labels, cnf.nv)
    groups = list(g.groups)
    relax_groups = [x for x in groups if x != "aniso"]
    out = {"name": name, "t": t, "k": k, "f": f, "Ms": Ms, "vars": cnf.nv,
           "clauses": len(cnf.clauses), "groups": len(groups), "families": family_counts(labels),
           "build_seconds": round(time.time() - start, 1)}

    def attempt(on, c):
        st, sec = g.solve(on, c)
        row = {"status": st, "seconds": sec}
        if st == "SAT":
            row["check"] = check_model(g.model(), cnf, names, labels, set(on), t, k)
        return row

    out["bare"] = attempt([], main_cap)
    out["full"] = attempt(groups, main_cap)
    out["relax"] = attempt(relax_groups, main_cap)
    models = []

    def on_sat(lab, trial):
        if len(models) < KEEP_MODELS:
            models.append({"without": lab,
                           "check": check_model(g.model(), cnf, names, labels, set(trial), t, k)})

    out["ladder"] = {}
    for fams in LADDER:
        key = "-" + "-".join(fams)
        if time.time() > deadline:
            out["ladder"][key] = {"status": "SKIPPED"}
            continue
        out["ladder"][key] = attempt([x for x in relax_groups if family(x) not in fams], cap)
    if out["relax"]["status"] == "UNSAT":
        out["core"] = min_core(g, relax_groups, cap, deadline, on_sat, main_cap)
    else:
        out["core"] = {"status": out["relax"]["status"]}
    out["core_models"] = models
    out["solver_calls"] = g.calls
    out["seconds"] = round(time.time() - start, 1)
    g.delete()
    return out


def short(row):
    s = row.get("status")
    c = row.get("check")
    if c:
        s += "(" + ("ok" if c["clauses_ok"] and c["system"] is not False else "BAD") + \
             (",aniso" if c["anisotropic"] else "") + f",rk{c['rank_Au']})"
    return s


def line(r):
    core = r["core"]
    cs = (f"core {core.get('size')} minimal {core.get('minimal')} final {core.get('final')} "
          f"{json.dumps(core.get('families'), sort_keys=True)} {core.get('core')}"
          if "core" in core else f"core none ({core.get('status')})")
    lad = " ".join(f"{k} {short(v)}" for k, v in r["ladder"].items())
    return (f"inst {r['name']}: bare {short(r['bare'])} full {short(r['full'])} relax "
            f"{short(r['relax'])} {r['relax'].get('seconds')} s | {cs} | ladder {lad} | calls "
            f"{r['solver_calls']} seconds {r['seconds']}")


def run(group, cap, main_cap, minutes, out_dir):
    rows = []
    for spec in instance_specs(group):
        r = run_instance(spec, cap, main_cap, minutes)
        rows.append(r)
        print(line(r), flush=True)
        with open(os.path.join(out_dir, f"m96{group}_rows.json"), "w") as fh:
            json.dump(rows, fh, indent=1)
    print(f"SUMMARY run group {group} instances {len(rows)} relax "
          f"{json.dumps({r['name']: r['relax']['status'] for r in rows}, sort_keys=True)} "
          f"cores {json.dumps({r['name']: r['core'].get('size') for r in rows}, sort_keys=True)}",
          flush=True)


# ---------- grading (pre-registered in m96-predictions.md) ----------

def load(out_dir, name):
    p = os.path.join(out_dir, name)
    if not os.path.exists(p):
        return None
    with open(p) as fh:
        return json.load(fh)


def models_of(r):
    out = [(k, r[k]) for k in ("bare", "full", "relax") if r[k]["status"] == "SAT"]
    out += [("ladder" + k, v) for k, v in r["ladder"].items() if v.get("status") == "SAT"]
    out += [("core-" + m["without"], m) for m in r.get("core_models", [])]
    return out


def grade(group, out_dir):
    graded = {}
    st = load(out_dir, f"m96{group}_selfcheck.json") or {"graded": {"selfcheck": False}}
    for key, ok in st["graded"].items():
        graded["selfcheck_" + key] = bool(ok)
    rows = load(out_dir, f"m96{group}_rows.json") or []
    graded["all_instances"] = len(rows) == len(instance_specs(group))
    for r in rows:
        b = r["bare"]
        graded[r["name"] + "_bare_sat"] = (b["status"] == "SAT" and b["check"]["clauses_ok"]
                                            and b["check"]["system"] is not False)
        # UNKNOWN (cap reached) is reported, not graded
        if r["t"] <= 6 and r["full"]["status"] in ("SAT", "UNSAT"):
            graded[r["name"] + "_full_unsat"] = r["full"]["status"] == "UNSAT"
        if r["name"] in ("t6_shift", "t8_n4") and r["relax"]["status"] in ("SAT", "UNSAT"):
            graded[r["name"] + "_relax_unsat"] = r["relax"]["status"] == "UNSAT"
        graded[r["name"] + "_models_ok"] = all(m["check"]["clauses_ok"]
                                               and m["check"]["system"] is not False
                                               for _, m in models_of(r))
        if "core" in r["core"]:
            graded[r["name"] + "_core_final_unsat"] = r["core"]["final"] == "UNSAT"
    out = {"group": group, "graded": graded,
           "relax": {r["name"]: r["relax"]["status"] for r in rows},
           "full": {r["name"]: r["full"]["status"] for r in rows},
           "cores": {r["name"]: {k: r["core"].get(k) for k in ("size", "minimal", "complete",
                                                                "families", "core", "kept")}
                     for r in rows},
           "ladder": {r["name"]: {k: v.get("status") for k, v in r["ladder"].items()}
                      for r in rows}}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "run", "grade"], default="selfcheck")
    ap.add_argument("--group", choices=GROUPS, default="a")
    ap.add_argument("--cap-seconds", type=float, default=30.0)
    ap.add_argument("--main-cap", type=float, default=300.0)
    ap.add_argument("--minutes", type=float, default=12.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "selfcheck":
        selfcheck(args.group, args.out_dir)
    elif args.part == "run":
        run(args.group, args.cap_seconds, args.main_cap, args.minutes, args.out_dir)
    else:
        out = grade(args.group, args.out_dir)
        with open(os.path.join(args.out_dir, f"m96{args.group}_grade.json"), "w") as fh:
            json.dump(out, fh, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        print(f"SUMMARY grade group {args.group} all_match {not bad} graded {len(out['graded'])} "
              f"failed {bad} relax {json.dumps(out['relax'], sort_keys=True)} cores "
              f"{json.dumps({k: [v['size'], v['minimal']] for k, v in out['cores'].items()}, sort_keys=True)}",
              flush=True)


if __name__ == "__main__":
    main()
