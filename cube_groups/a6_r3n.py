# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m35: the second matrix. A probe of the split of the open (B5) classes at t = 6 by
sigma(h_1) and the matrix A_(h_1) (notes/a18.md, Lemma 71), on top of job m30's instances
(a6_r3m.py: normal form of Lemma 67, facts of Lemma 69, A_u fixed by Lemma 70).

In the normal form for u, h_1 lies in ker phi whenever d - p >= 2 (always in (B5): d - p = 2).
Lemma 71: with s = sigma(h_1) and N = A_(h_1),

    (i)   s lies in X_1 = ker A_u and not in span(x0); replacing h_1 by h_1 + h_0 keeps the normal
          form and replaces (s, N) by (s + x0, N + A_u), so s may be taken with e_0-coordinate 0;
    (ii)  N x0 = 0, N s = 0, N P lies in R = Im A_u;
    (iii) for g in H_A = {g in G : g X_1 = X_1, g R = R, g A_u g^(-1) = A_u} there is a system in
          the normal form with the same A_u and (s, N) replaced by (g s, g N g^(-1)), normalised
          as in (i).

So one instance per H_A-orbit on the normalised pairs (s, N) covers the class. In (B5) at t = 6
there are 3 choices of s and 8^4 = 4096 matrices N per s: 12288 pairs per class. H_A is computed
exactly: the conditions g = I + D, D x0 = 0, D P in P, D X_1 in X_1, D R in R, D A_u = A_u D are
linear in D, the solution space is enumerated and the invertible elements kept. At t = 4 this is
checked against the brute-force stabiliser in G (|G| <= 192), and the candidate matrices against
a brute force over all 2^16 matrices.

This job is a PROBE for a time model, not a decision: it runs three open classes of (B5)
(pair orbit 0 class 0, the only class there; pair orbit 9 class 5, whose class has size 1; pair
orbit 1 class 0) with the pairs fixed, after the controls: every t = 4 instance (UNSAT by
A(4) = 4) and four instances at t = 6 built from the direct sum of m32.py (two with a model and a
non-symmetric matrix among them, one UNSAT by hand because A_(h_1) sigma(h_1) != 0).

Parts: selfcheck, controls4, control6n, probe --target 0|1|2, grade; child (internal).

Usage: python a6_r3n.py --part selfcheck|controls4|control6n|probe|grade [--target K]
                        [--budget-minutes M] [--group-minutes M] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import a6_r3 as r3
import a6_r3h as h
import a6_r3m as m
import m32
import sat_aniso as sa

T = r3.T
RHO = r3.RHO
X0 = 1                  # x0 = sigma(u) = e_0 in the normal form of Lemma 67
MAX_LINEAR_DIM = 22     # the linear space of D is enumerated; refuse anything larger

# Probe targets: (shape key, pair orbit, class, the A_u job m30 used, minutes per instance,
# group minutes). The A_u values are those of m32.EXPECTED_AU.
PROBE = [("B5", 0, 0, 33824, 2.0, 45.0),
         ("B5", 9, 5, 34630270976, 2.0, 30.0),
         ("B5", 1, 0, 2098208, 1.0, 35.0)]

# Hand values (m35/predictions.md).
HAND_CANDIDATES_B5 = 12288                 # 3 choices of s times 8^4 matrices
HAND_S_B5 = [2, 4, 6]                      # X_1 = span(e_0, e_1, e_2): e_1, e_2, e_1 + e_2
HAND_ORBIT_SIZES = {0: 155, 9: 9920, 1: 6510}            # job m30's pair orbits of ("B", 5)
HAND_CLASS_SIZES = {(0, 0): 168, (9, 5): 1, (1, 0): 48}   # job m30's class sizes
HAND_H_ORDER = {(0, 0): 384, (9, 5): 1008, (1, 0): 32}   # |G| / orbit size / class size
# The controls at t = 6 from m32.direct_sum_control: (name, skew, s_1, A_1, expected).
# diag: h_1 = a_1, sigma(a_1) = E_1 = e_0 + e_4 + e_5 = 49, A_(a_1) = E_11 = 128.
# diag_shift: h_1 = a_1 + u, sigma = E_2 + E_3 = e_4 + e_5 = 48, A = E_11 + A_u = 2113536.
# skew: e_4 = E_2 + F_1, so E_1 = e_0 + e_1 + e_4 + e_5 = 51 and A_(a_1) has entries (1, 1) and
# (1, 4): 128 + 1024 = 1152, not symmetric. Its transpose (entries (1, 1), (4, 1): 33554560) maps
# s = 51 to e_1 + e_4 != 0, against A_h sigma(h) = 0: UNSAT.
HAND_CONTROL6N = [("ctl6n_diag", False, 49, 128, "SAT"),
                  ("ctl6n_diag_shift", False, 48, 2113536, "SAT"),
                  ("ctl6n_skew", True, 51, 1152, "SAT"),
                  ("ctl6n_skew_transposed", True, 51, 33554560, "UNSAT")]


# ---------- the exact stabiliser H_A ----------

def bit(t, row, col):
    return 1 << (t * row + col)


def stabiliser_constraints(t, A, x0, keep):
    """Masks c on the t*t bits of D (entry (row, col) at bit t row + col) such that
    parity(c & D) = 0 says: D x0 = 0; D W lies in span(W) for every W in keep; D A = A D."""
    cons = []
    for row in range(t):
        cons.append(sum(bit(t, row, c) for c in range(t) if (x0 >> c) & 1))
    for W in keep:
        W = list(W)
        for f in sa.nullspace(W, t):
            for w in W:
                cons.append(sum(bit(t, row, c) for row in range(t) if (f >> row) & 1
                                for c in range(t) if (w >> c) & 1))
    for row in range(t):
        for col in range(t):
            mask = 0
            for k in range(t):
                if (A >> (t * k + col)) & 1:
                    mask ^= bit(t, row, k)
                if (A >> (t * row + k)) & 1:
                    mask ^= bit(t, k, col)
            cons.append(mask)
    return cons


def stabiliser(t, shape, p, x1, r, A):
    """H_A = {g in G : g X_1 = X_1, g R = R, g A g^(-1) = A}, exactly, sorted. Every g is I + D
    with D in the solution space of the linear conditions; invertibility is checked."""
    cons = stabiliser_constraints(t, A, X0, [r3.p_basis(shape, p), list(x1), list(r)])
    basis = sa.nullspace(cons, t * t)
    if len(basis) > MAX_LINEAR_DIM:
        raise ValueError(f"linear space too large: 2^{len(basis)}")
    ident = m.identity(t)
    out = []
    for c in range(1 << len(basis)):
        g = ident ^ sa.combine(basis, c)
        if sa.rank_f2(sa.rows_of(g, t)) == t:
            out.append(g)
    return sorted(out)


# ---------- the candidate pairs (s, N) ----------

def s_choices(t, x1):
    """s in X_1 outside span(x0), one per coset of span(x0): the one with e_0-coordinate 0."""
    X1 = list(r3.rref(list(x1)))
    return sorted(v for c in range(1, 1 << len(X1)) for v in [sa.combine(X1, c)] if not v & X0)


def extend(cur, vecs):
    out = []
    for v in vecs:
        if sa.rank_f2(cur + out + [v]) > len(cur) + len(out):
            out.append(v)
    return out


def candidate_matrices(t, shape, p, x1, r, s):
    """Every N with N x0 = 0, N s = 0 and N P in span(r), sorted. N is given by the images of a
    basis: x0, s (both 0), then a completion of P + span(x0, s) (images in span(r)), then a
    completion of X (images anywhere)."""
    R = list(r3.rref(list(r)))
    first = [X0, s]
    mid = extend(first, r3.p_basis(shape, p))
    rest = extend(first + mid, [1 << c for c in range(t)])
    inv = sa.mat_inv(sa.from_cols(first + mid + rest, t), t)
    rvals = [sa.combine(R, c) for c in range(1 << len(R))]
    out = []
    for mids in itertools.product(rvals, repeat=len(mid)):
        for rests in itertools.product(range(1 << t), repeat=len(rest)):
            vals = [0, 0] + list(mids) + list(rests)
            out.append(sa.mat_mul(sa.from_cols(vals, t), inv, t))
    return sorted(out)


def satisfies_conditions(t, shape, p, r, s, N):
    R = r3.rref(list(r))
    return (sa.mat_apply(N, X0, t) == 0 and sa.mat_apply(N, s, t) == 0
            and all(r3.in_span(R, sa.mat_apply(N, b, t)) for b in r3.p_basis(shape, p)))


def candidates(t, shape, p, x1, r):
    return [(s, N) for s in s_choices(t, x1) for N in candidate_matrices(t, shape, p, x1, r, s)]


def normalise(s, N, au):
    """The representative of {(s, N), (s + x0, N + A_u)} with e_0-coordinate 0 in s."""
    return (s ^ X0, N ^ au) if s & X0 else (s, N)


def act(g, ginv, s, N, au, t):
    return normalise(sa.mat_apply(g, s, t), sa.mat_mul(sa.mat_mul(g, N, t), ginv, t), au)


def pair_orbits(t, shape, p, x1, r, au):
    """(H_A, candidates, [(representative pair, orbit size)], every orbit inside the candidates)."""
    H = stabiliser(t, shape, p, x1, r, au)
    Hinv = [sa.mat_inv(g, t) for g in H]
    cands = candidates(t, shape, p, x1, r)
    candset = set(cands)
    seen = set()
    out = []
    inside = True
    for c in cands:
        if c in seen:
            continue
        orb = {act(g, gi, c[0], c[1], au, t) for g, gi in zip(H, Hinv)}
        inside = inside and orb <= candset
        seen |= orb
        out.append((min(orb), len(orb)))
    return H, cands, out, inside


# ---------- the encoding ----------

def encode_r3n(t, d, shape, p, rho, x1, r, au, s1, a1):
    """a6_r3m.encode_r3m (normal form, facts, A_u = au) plus the unit clauses sigma(h_1) = s1 and
    A_(h_1) = a1 (entry (row, col) at bit t row + col, as everywhere)."""
    cnf, names = m.encode_r3m(t, d, shape, p, rho, x1, r, au)
    A, S = names[0], names[1]
    for row in range(t):
        v = S[1][row]
        cnf.clauses.append([v] if (s1 >> row) & 1 else [-v])
    for row in range(t):
        for col in range(t):
            v = A[1][row][col]
            cnf.clauses.append([v] if (a1 >> (t * row + col)) & 1 else [-v])
    return cnf, names


# ---------- instances ----------

def instance_name(t, rho, shape, p, idx, cls, j):
    return f"r3n_t{t}_r{rho}_{shape}{p}_o{idx:03d}_m{cls:03d}_n{j:03d}"


def class_prefix(t, rho, shape, p, idx, cls):
    return f"r3n_t{t}_r{rho}_{shape}{p}_o{idx:03d}_m{cls:03d}"


def class_info(t, d, rho, shape, p, idx, cls, x1, r, au, size, class_size):
    """The pair orbits of one class with their checks and one spec per orbit."""
    X1, R = r3.rref(list(x1)), r3.rref(list(r))
    H, cands, orbs, inside = pair_orbits(t, shape, p, x1, r, au)
    go = r3.group_order(t, shape, p)
    specs = [{"t": t, "d": d, "rho": rho, "shape": shape, "p": p, "x1": list(X1), "r": list(R),
              "size": size, "orbit": idx, "cls": cls, "class_size": class_size, "au": au,
              "s1": s, "a1": N, "pair_size": n,
              "name": instance_name(t, rho, shape, p, idx, cls, j)}
             for j, ((s, N), n) in enumerate(orbs)]
    return {"t": t, "shape": shape, "p": p, "orbit": idx, "cls": cls, "x1": list(X1),
            "r": list(R), "au": au, "size": size, "class_size": class_size, "kd": d - p,
            "H_order": len(H), "H_in_G": all(r3.in_group(g, t, shape, p) for g in H),
            "H_fixes": all(r3.image(g, X1, t) == X1 and r3.image(g, R, t) == R
                           and m.conj(g, au, t) == au for g in H),
            "H_divides_G": go % len(H) == 0,
            "H_times_class_le_H_pair": len(H) * class_size <= go // size,
            "H_times_class_eq_H_pair": len(H) * class_size == go // size,
            "s_choices": s_choices(t, x1), "candidates": len(cands),
            "candidates_distinct": len(set(cands)) == len(cands),
            "candidates_ok": all(satisfies_conditions(t, shape, p, r, s, N) for s, N in cands),
            "orbits": len(orbs), "orbit_sizes": sorted(n for _, n in orbs),
            "sizes_add_up": sum(n for _, n in orbs) == len(cands),
            "sizes_divide_H": all(len(H) % n == 0 for _, n in orbs), "inside": inside,
            "specs": specs}


def t4_classes():
    """Every class of every pair orbit at t = 4 (the controls of a6_r3.py), with job m30's seeds:
    [(t, d, rho, shape, p, idx, cls, x1, r, size, rep, class size)]."""
    out = []
    for t, d, rho, s, p in r3.CONTROLS:
        if t != 4:
            continue
        for idx, (x1, r, size) in enumerate(r3.orbits(t, s, p, rho)):
            cl = m.classes(t, s, p, x1, r, seed=f"m30-{t}-{s}{p}-{idx}")
            for cls, (rep, mem) in enumerate(cl):
                out.append((t, d, rho, s, p, idx, cls, x1, r, size, rep, len(mem)))
    return out


def t4_specs(per_class=3):
    """At most per_class instances of every class at t = 4 (all UNSAT by A(4) = 4): a smoke test
    of the encoding, not a result."""
    out = []
    for t, d, rho, s, p, idx, cls, x1, r, size, rep, csize in t4_classes():
        out += class_info(t, d, rho, s, p, idx, cls, x1, r, rep, size, csize)["specs"][:per_class]
    return out


def control6n_specs():
    out = []
    for name, skew, s1, a1, expect in HAND_CONTROL6N:
        As, ss, B, x1, r, au = m32.direct_sum_control(skew)
        out.append({"t": T, "d": T, "rho": RHO, "shape": "B", "p": 3, "x1": list(x1),
                    "r": list(r), "size": 0, "orbit": -1, "cls": -1, "class_size": 0, "au": au,
                    "s1": s1, "a1": a1, "pair_size": 0, "name": name, "expect": expect})
    return out


def class_path(out_dir, key, idx, cls):
    return os.path.join(out_dir, f"r3n_class_{key}_o{idx:03d}_m{cls:03d}.json")


def probe_class(k, out_dir):
    """The class info of probe target k, computed once and saved."""
    key, idx, cls, au_exp, _, _ = PROBE[k]
    path = class_path(out_dir, key, idx, cls)
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    s, p = r3.SHAPES[key]
    data = m.load_classes(out_dir, T, RHO, s, p)
    o = data[idx]
    rep, csize = o["reps"][cls]
    info = class_info(T, T + 1, RHO, s, p, idx, cls, tuple(o["x1"]), tuple(o["r"]), rep,
                      o["size"], csize)
    info["au_expected"] = au_exp
    info["au_as_m30"] = rep == au_exp
    with open(path, "w") as f:
        json.dump(info, f)
    return info


# ---------- solving ----------

def child(spec_path, solver, path):
    from pysat.solvers import Solver
    with open(spec_path) as f:
        sp = json.load(f)
    t, d = sp["t"], sp["d"]
    cnf, names = encode_r3n(t, d, sp["shape"], sp["p"], sp["rho"], sp["x1"], sp["r"], sp["au"],
                            sp["s1"], sp["a1"])
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
    res["wall_seconds"] = round(time.time() - start, 2)
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and r3.in_normal_form(As, ss, B, t, d, shape, p, spec["x1"], spec["r"]))
        plain, alts = h.facts(t, d, shape, p, rho, spec["x1"], spec["r"])
        res["facts_hold"] = h.facts_hold(plain, alts, As, t)
        res["au_matches"] = As[0] == spec["au"]
        res["s1_matches"] = ss[1] == spec["s1"]
        res["a1_matches"] = As[1] == spec["a1"]
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


def run_probe(k, out_dir, solver="auto"):
    key, idx, cls, au_exp, minutes, group_minutes = PROBE[k]
    info = probe_class(k, out_dir)
    prefix = class_prefix(T, RHO, *r3.SHAPES[key], idx, cls)
    if not info["au_as_m30"]:
        res = {"name": prefix, "status": "MISMATCH", "au": info["au"], "t": T}
        with open(os.path.join(out_dir, prefix + ".json"), "w") as f:
            json.dump(res, f, indent=1)
        print(f"SUMMARY probe {k} {prefix} MISMATCH", flush=True)
        return {"MISMATCH": 1}
    counts = run_group(info["specs"], solver, minutes * 60, group_minutes * 60, out_dir)
    print(f"SUMMARY probe {k} {prefix} H {info['H_order']} instances {len(info['specs'])} "
          f"{json.dumps(counts, sort_keys=True)}", flush=True)
    return counts


# ---------- selfcheck ----------

def control6n_hand():
    st = {}
    for name, skew, s1, a1, expect in HAND_CONTROL6N:
        As, ss, B, x1, r, au = m32.direct_sum_control(skew)
        row = {"au_hand": au == m32.HAND_CONTROL[skew]["au"],
               "a1_ok": satisfies_conditions(T, "B", 3, r, s1, a1) == (expect == "SAT"),
               "s1_in_X1": r3.in_span(r3.rref(list(x1)), s1), "s1_not_x0": s1 not in (0, X0)}
        if name == "ctl6n_diag_shift":
            row["is_shift"] = (s1, a1) == normalise(ss[1], As[1], au)
        elif name == "ctl6n_skew_transposed":
            row["is_transpose"] = a1 == m32.transpose(1152, T) and a1 != 1152
            row["breaks_s"] = sa.mat_apply(a1, s1, T) != 0
        else:
            row["model_values"] = (ss[1], As[1]) == (s1, a1)
            row["a1_symmetric"] = a1 == m32.transpose(a1, T)
        st[name] = row
    return st


def selfcheck(out_dir):
    st = {"t4": [], "t6": [], "control6n": control6n_hand()}
    groups = {}
    n4 = 0
    for t, d, rho, s, p, idx, cls, x1, r, size, rep, csize in t4_classes():
        if (t, s, p) not in groups:
            groups[(t, s, p)] = m.group_elements(t, s, p)
        G = groups[(t, s, p)]
        X1, R = r3.rref(list(x1)), r3.rref(list(r))
        HA = stabiliser(t, s, p, x1, r, rep)
        brute = sorted(g for g in G if r3.image(g, X1, t) == X1 and r3.image(g, R, t) == R
                       and m.conj(g, rep, t) == rep)
        info = class_info(t, d, rho, s, p, idx, cls, x1, r, rep, size, csize)
        exact = True
        for sv in info["s_choices"]:
            built = candidate_matrices(t, s, p, x1, r, sv)
            bf = sorted(N for N in range(1 << (t * t)) if satisfies_conditions(t, s, p, r, sv, N))
            exact = exact and built == bf
        n4 += info["orbits"]
        row = {k: v for k, v in info.items() if k != "specs"}
        row.update({"H_exact": HA == brute, "H_brute": len(brute), "candidates_exact": exact})
        st["t4"].append(row)
    st["t4_instances"] = n4
    for k in range(len(PROBE)):
        info = probe_class(k, out_dir)
        st["t6"].append({k: v for k, v in info.items() if k != "specs"})
    t4, t6, c6 = st["t4"], st["t6"], st["control6n"]
    st["graded"] = {
        "t4_kd": all(row["kd"] >= 2 for row in t4),
        "t4_H_exact": all(row["H_exact"] for row in t4) and len(t4) >= 50,
        "t4_candidates_exact": all(row["candidates_exact"] and row["candidates_distinct"]
                                   and row["candidates_ok"] for row in t4),
        "t4_orbits": all(row["sizes_add_up"] and row["sizes_divide_H"] and row["inside"]
                         for row in t4),
        "t6_au_as_m30": all(row["au_as_m30"] for row in t6),
        "t6_H_in_G": all(row["H_in_G"] and row["H_fixes"] for row in t6),
        "t6_lagrange": all(row["H_divides_G"] and row["H_times_class_le_H_pair"] for row in t6),
        "t6_counts": all(row["candidates"] == HAND_CANDIDATES_B5 and row["s_choices"] == HAND_S_B5
                         and row["candidates_distinct"] and row["candidates_ok"] for row in t6),
        "t6_orbits": all(row["sizes_add_up"] and row["sizes_divide_H"] and row["inside"]
                         for row in t6),
        "control6n_hand": all(v for row in c6.values() for k, v in row.items()
                              if k != "a1_symmetric")
                          and not c6["ctl6n_skew"]["a1_symmetric"]}
    st["exploratory"] = {
        "t6_H_eq_hand": {f"o{idx:03d}_m{cls:03d}": [row["H_order"], HAND_H_ORDER[(idx, cls)],
                                                    row["H_times_class_eq_H_pair"]]
                         for row, (_, idx, cls, _, _, _) in zip(t6, PROBE)},
        "t6_orbit_counts": [row["orbits"] for row in t6]}
    return st


# ---------- grading ----------

def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if (fn.startswith(("r3n_t", "ctl6n_")) and fn.endswith(".json")
                and not fn.endswith((".child.json", ".spec.json"))):
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
        s = r.get("status", "missing")
        if name.startswith("ctl6n_"):
            graded[name] = s == r["expect"]
            if s == "SAT":
                for k in ("verified", "facts_hold", "au_matches", "s1_matches", "a1_matches"):
                    graded[f"{name}_{k}"] = bool(r.get(k))
        elif r.get("t") == 4:
            if s in ("SAT", "UNSAT", "ERROR"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
        else:
            if s == "MISMATCH":
                graded[name + "_au_as_m30"] = False
            elif s == "ERROR":
                graded[name] = False
            if s == "SAT":
                for k in ("verified", "facts_hold", "au_matches", "s1_matches", "a1_matches"):
                    graded[f"{name}_{k}"] = bool(r.get(k))
    t4 = [r.get("status") for n, r in results.items() if r.get("t") == 4]
    probe = {}
    for k, (key, idx, cls, _, minutes, _) in enumerate(PROBE):
        prefix = class_prefix(T, RHO, *r3.SHAPES[key], idx, cls)
        rs = [r for n, r in sorted(results.items()) if n.startswith(prefix)]
        status = [r.get("status") for r in rs]
        times = sorted(r["wall_seconds"] for r in rs if r.get("status") in ("SAT", "UNSAT"))
        info = {}
        try:
            with open(class_path(out_dir, key, idx, cls)) as f:
                info = json.load(f)
        except (OSError, ValueError):
            pass
        probe[prefix] = {"H_order": info.get("H_order"), "orbits": info.get("orbits"),
                         "run": len(rs), "counts": {x: status.count(x) for x in sorted(set(status), key=str)},
                         "decided": len(times),
                         "decided_fraction_of_run": round(len(times) / len(rs), 3) if rs else None,
                         "median_seconds": times[len(times) // 2] if times else None,
                         "max_seconds": times[-1] if times else None,
                         "budget_minutes": minutes}
    return {"graded": graded, "ungraded": ungraded,
            "t4": {"instances": len(t4), "counts": {x: t4.count(x) for x in sorted(set(t4), key=str)}},
            "probe": probe,
            "times": {n: r.get("wall_seconds") for n, r in results.items()},
            "any_sat_6": any(r.get("status") == "SAT" for n, r in results.items()
                             if n.startswith("r3n_t6"))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls4", "control6n", "probe", "child",
                                       "grade"], default="selfcheck")
    ap.add_argument("--target", type=int, default=0)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=1.0)
    ap.add_argument("--group-minutes", type=float, default=12.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="spec.json")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.spec, args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls4":
        sps = t4_specs()
        out = run_group(sps, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY controls4 instances {len(sps)} {json.dumps(out, sort_keys=True)}",
              flush=True)
    elif args.part == "control6n":
        sps = control6n_specs()
        out = run_group(sps, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY control6n instances {len(sps)} {json.dumps(out, sort_keys=True)}",
              flush=True)
    elif args.part == "probe":
        run_probe(args.target, args.out_dir, args.solver)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_6 {out['any_sat_6']} t4 {json.dumps(out['t4']['counts'], sort_keys=True)} "
              + " ".join(f"{k} H {v['H_order']} orbits {v['orbits']} {json.dumps(v['counts'], sort_keys=True)} "
                         f"median {v['median_seconds']}" for k, v in out["probe"].items()),
              flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck(args.out_dir)
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())} "
              f"t4_instances {st['t4_instances']} "
              f"t6 {json.dumps(st['exploratory'], sort_keys=True)}", flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
