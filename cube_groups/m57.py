# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m57: two passes over classes of (B6) and (B5) at t = 7 and dim V = 9 that earlier jobs left
UNKNOWN, under rules that jobs m50 and m53 wrote down before they ran (notes/a46.md).

Group a (job m57a): the 17 classes of (B5) in batch c of job m48 (m48.py's representatives, which
the check parts of jobs m48a and m48b confirmed against m42.py's classification of (B5)), CaDiCaL,
at most 15 minutes per class, 150 minutes in all. This is the run that m48c was staged to be, with
the instance built by the code of m42.py copied below unchanged instead of by m42.py itself.

Group b (job m57b):
  (1) r3p_t7_B6_o001_a07, the one instance of job m53 (the kind-P class of (B6) with d = 3, split by
      the second matrix A_(h_1); notes/a42.md, Proposition 30) that stayed UNKNOWN at 210 s:
      CaDiCaL for 15 minutes (m53's rule for 30 to 39 of 40 UNSAT), then, if still UNKNOWN,
      CryptoMiniSat with native XOR constraints for 15 minutes. If it is UNSAT, all 40 instances
      of the kind-P class are, and the class is empty.
  (2) the 21 open classes of (B5) with d = dim(ker A_u n Im A_u) <= 2 that CaDiCaL left UNKNOWN at
      10 or 15 minutes (jobs m46, m48a, m48b): CryptoMiniSat with native XOR, at most 5 minutes
      each. Job m50 found that arm uneven: it closed r3b_t7_B5_o027_c001 in 5 s after CaDiCaL
      failed at 600 s and o047_c003 in 3 s against CaDiCaL's 175 s, but left 5 of 9 classes that
      CaDiCaL decides undecided.

The XOR arm is m50.py's: sat_aniso.encode builds an XorCNF, whose xor_eq keeps each linear
condition as one XOR constraint instead of cutting it into parity clauses; everything else is the
same clauses. Matrices are t^2-bit masks with entry (r, c) at bit t r + c, as in sat_aniso.py.

Parts:
    check   graded: every representative has the kernel X_1 and image R of its pair, rank 3 and the
            hand value of d; the d counts of both lists; a07's A_(h_1) is admissible with rank 0
            on X_1; hint and unit counts as in m42.py and m53.py; on random small systems the XOR
            instance accepts exactly the anisotropic systems, as the CNF does; the planted system
            at t = 6 with A_(v_1) fixed is accepted (and rejected with one entry flipped), and is
            solved SAT and verified in both arms.
    solve   the group's plan in order, each instance capped as above.
    grade   graded checks and every SAT verified; statuses by arm and by d.

Usage: python m57.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
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

T = 7
D = 9
MIN_BUDGET = 20.0
PLANTED_BUDGET = {"cadical": 240.0, "xor": 300.0}
HAND_HINTS = {"B6": 79, "B5": 111, "planted": 45}

# (B5), m46.py's tables: X_1 = span(e_0, ..., e_3) for pair orbits 0 to 19 (X_1 inside H0) and
# span(e_0, e_1, e_2, e_6) for 20 to 48; the image R of each pair orbit as m42c numbered them.
FIRST_BETA_PAIR = 20
X1_OF_ORBIT = {0: (8, 4, 2, 1), 1: (64, 4, 2, 1)}
PAIR_R = {
    0: (4, 2, 1), 1: (8, 4, 2), 2: (8, 4, 3), 3: (16, 2, 1), 4: (16, 4, 2), 5: (16, 4, 3),
    6: (17, 4, 2), 7: (32, 16, 1), 8: (32, 16, 2), 9: (32, 16, 3), 10: (32, 17, 2),
    11: (64, 2, 1), 12: (64, 4, 2), 13: (64, 4, 3), 14: (64, 16, 1), 15: (64, 16, 2),
    16: (64, 16, 3), 17: (64, 17, 2), 18: (64, 32, 16), 19: (64, 32, 17),
    20: (4, 2, 1), 21: (8, 2, 1), 22: (8, 4, 2), 23: (8, 4, 3), 24: (9, 4, 2), 25: (16, 8, 1),
    26: (16, 8, 2), 27: (16, 8, 3), 28: (16, 9, 2), 29: (32, 16, 8), 30: (32, 16, 9),
    31: (64, 2, 1), 32: (64, 4, 2), 33: (64, 4, 3), 34: (64, 8, 1), 35: (64, 8, 2),
    36: (64, 8, 3), 37: (64, 9, 2), 38: (64, 16, 8), 39: (64, 16, 9), 40: (72, 2, 1),
    41: (72, 4, 2), 42: (72, 4, 3), 43: (72, 16, 1), 44: (72, 16, 2), 45: (72, 16, 3),
    46: (72, 17, 2), 47: (72, 32, 16), 48: (72, 32, 17)}

# Batch c of job m48 (m48.py's OPEN, names sorted, every third from the third): representatives
# A_u as job m42d recorded them.
BATCH_C = {
    "r3b_t7_B5_o001_c000": 34086912,
    "r3b_t7_B5_o004_c002": 17180135424,
    "r3b_t7_B5_o005_c004": 8590204992,
    "r3b_t7_B5_o007_c006": 571230650400,
    "r3b_t7_B5_o009_c009": 1103806605392,
    "r3b_t7_B5_o012_c002": 351843721154560,
    "r3b_t7_B5_o013_c004": 351843721154592,
    "r3b_t7_B5_o015_c004": 70394513985536,
    "r3b_t7_B5_o016_c024": 422233939904528,
    "r3b_t7_B5_o019_c016": 142949396512816,
    "r3b_t7_B5_o024_c001": 33689616,
    "r3b_t7_B5_o028_c008": 6559892536,
    "r3b_t7_B5_o035_c000": 35184405647360,
    "r3b_t7_B5_o037_c000": 35184405647376,
    "r3b_t7_B5_o041_c001": 70368777867264,
    "r3b_t7_B5_o047_c002": 35747029581824,
    "r3b_t7_B5_o048_c003": 36288195461136,
}
# The open classes of (B5) with d <= 2 that CaDiCaL left UNKNOWN: 13 from job m46 (m46.py's OPEN;
# o027_c001 left out, closed by job m50), 2 from m48a and 6 from m48b (m48.py's OPEN).
LEFTOVERS = {
    "r3b_t7_B5_o003_c005": 4294975536,
    "r3b_t7_B5_o004_c001": 8590204928,
    "r3b_t7_B5_o005_c005": 8590207056,
    "r3b_t7_B5_o006_c000": 4295499792,
    "r3b_t7_B5_o007_c005": 566935683104,
    "r3b_t7_B5_o008_c001": 562640723968,
    "r3b_t7_B5_o009_c004": 562640726096,
    "r3b_t7_B5_o010_c002": 566935687232,
    "r3b_t7_B5_o010_c003": 571230654544,
    "r3b_t7_B5_o010_c007": 1653562417168,
    "r3b_t7_B5_o015_c001": 70381629087744,
    "r3b_t7_B5_o015_c011": 422216760037376,
    "r3b_t7_B5_o016_c001": 70377334124640,
    "r3b_t7_B5_o017_c000": 70377334120480,
    "r3b_t7_B5_o017_c001": 70381629087792,
    "r3b_t7_B5_o017_c006": 140741783330832,
    "r3b_t7_B5_o019_c006": 72048076390512,
    "r3b_t7_B5_o030_c000": 279239983136,
    "r3b_t7_B5_o030_c011": 1105970855944,
    "r3b_t7_B5_o039_c003": 35188784496696,
    "r3b_t7_B5_o039_c022": 140743947583496,
}
# d by hand from the pair tables (notes/a41.md, a46.md); graded in --part check.
HAND_D_COUNTS = {"a": {"3": 1, "2": 8, "1": 5, "0": 3}, "b": {"2": 4, "1": 14, "0": 3}}

# (B6), the kind-P class (pair orbit 1), as in m53.py: X_1, R, A_u = e_4 -> e_1, e_5 -> e_2,
# e_6 -> e_3, and the representative A_(h_1) of m53's instance a07 (m53 out/r3p_t7_B6_o001_a07.json:
# e_4 -> e_1, rank 0 on X_1, m52 index 512, class size 56).
B6_X1 = (8, 4, 2, 1)
B6_R = (8, 4, 2)
B6_AU = (1 << 11) | (1 << 19) | (1 << 27)
A07 = {"name": "r3p_t7_B6_o001_a07", "kind": "main", "t": T, "d": D, "p": 6, "pair": 1,
       "x1": list(B6_X1), "r": list(B6_R), "au": B6_AU, "a1": 1 << 11, "rank_x1": 0,
       "m52_index": 512, "m52_size": 56}


# ---------- from m42.py, unchanged ----------

def rref(vecs):
    """The reduced row echelon basis of span(vecs), pivots = leading bits, in decreasing order."""
    rows = []
    for v in vecs:
        for r in rows:
            if (v >> (r.bit_length() - 1)) & 1:
                v ^= r
        if v:
            q = v.bit_length() - 1
            rows = [r ^ v if (r >> q) & 1 else r for r in rows]
            rows.append(v)
            rows.sort(reverse=True)
    return tuple(rows)


def in_span(rows, v):
    return len(rref(list(rows) + [v])) == len(rows)


def dim_meet(a, b):
    return len(a) + len(b) - len(rref(list(a) + list(b)))


def cols_of(g, t):
    return [sa.mat_apply(g, 1 << c, t) for c in range(t)]


def kernel(A, t):
    return rref(sa.nullspace(sa.rows_of(A, t), t))


def column_space(A, t):
    return rref(cols_of(A, t))


def ann(rows, t):
    """Basis of {f : f . s = 0 for every s in rows}."""
    return sa.nullspace(list(rows), t)


def p_basis(p):
    return rref([1 << j for j in range(1, p + 1)])


def phis_for(d, p):
    kd = d - p
    return (None,) + (0,) * (kd - 1) + tuple(1 << j for j in range(1, p + 1))


def encode_fixed(t, d, au, s0, phis):
    """sat_aniso.encode (no echelon form) with A_0 = au, s_0 = s0 and B_0i = phis[i] fixed by unit
    clauses (as encode_fixed in m41.py, without fixed s_i)."""
    cnf, names = sa.encode(t, d, echelon=False)
    A, S, B = names[0], names[1], names[2]

    def unit(var, bit):
        cnf.clauses.append([var] if bit else [-var])

    for r in range(t):
        unit(S[0][r], (s0 >> r) & 1)
        for c in range(t):
            unit(A[0][r][c], (au >> (t * r + c)) & 1)
    for i in range(1, d):
        if phis[i] is None:
            continue
        for r in range(t):
            unit(B[(0, i)][r], (phis[i] >> r) & 1)
    return cnf, names


def add_hints(cnf, names, t, kd, au, s0, pvecs):
    """For n = v_i, 0 < i < kd (in ker phi): A_n x0 = 0 and sigma(n) in X_1 by (3) of a10.md; A_n
    maps P + span(x0) into R and beta(n, n') lies in X_1 by (2). Returns the number of linear
    conditions added."""
    A, S, B = names[0], names[1], names[2]
    ann_x1 = ann(kernel(au, t), t)
    ann_r = ann(column_space(au, t), t)
    ext = rref(list(pvecs) + [s0])
    n = 0
    for i in range(1, kd):
        for row in range(t):
            cnf.xor_eq([A[i][row][c] for c in range(t) if (s0 >> c) & 1], 0)
            n += 1
        for y in ext:
            for f in ann_r:
                cnf.xor_eq([A[i][row][c] for row in range(t) if (f >> row) & 1
                            for c in range(t) if (y >> c) & 1], 0)
                n += 1
        for f in ann_x1:
            cnf.xor_eq([S[i][row] for row in range(t) if (f >> row) & 1], 0)
            n += 1
    for i, j in itertools.combinations(range(1, kd), 2):
        for f in ann_x1:
            cnf.xor_eq([B[(i, j)][row] for row in range(t) if (f >> row) & 1], 0)
            n += 1
    return n


def sigma_old(v):
    """X: E_i = bit 2i, F_i = bit 2i + 1; V: a_i = bit 2i, b_i = bit 2i + 1;
    sigma(a_i) = sigma(b_i) = E_i, sigma(a_i + b_i) = F_i, no cross terms."""
    out = 0
    for i in range(3):
        a, b = (v >> (2 * i)) & 1, (v >> (2 * i + 1)) & 1
        if a ^ b:
            out ^= 1 << (2 * i)
        elif a:
            out ^= 1 << (2 * i + 1)
    return out


def alpha_old(v):
    """A_(a_i) = A_(b_i) = the projection onto span(F_i) along the rest, A_(a_i + b_i) = 0."""
    out = 0
    for i in range(3):
        if ((v >> (2 * i)) ^ (v >> (2 * i + 1))) & 1:
            out ^= sa.entries(6, [(2 * i + 1, 2 * i + 1)])
    return out


def planted():
    """(As, ss, B) at t = 6, d = 6 in the basis h_0 = a_1 + a_2 + a_3 = u, h_1 = a_1, h_2 = a_2
    (phi = 0), h_3, h_4, h_5 = b_1, b_2, b_3, after the change of X-basis of m32.py (skew)."""
    t = 6
    nb = sa.from_cols([21, 2, 8, 32, 6, 16], t)
    c = sa.mat_inv(nb, t)
    hs = [21, 1, 4, 2, 8, 32]
    As = [sa.mat_mul(sa.mat_mul(c, alpha_old(v), t), nb, t) for v in hs]
    ss = [sa.mat_apply(c, sigma_old(v), t) for v in hs]
    B = {(i, k): sa.mat_apply(c, sigma_old(hs[i] ^ hs[k]) ^ sigma_old(hs[i]) ^ sigma_old(hs[k]), t)
         for i in range(t) for k in range(i + 1, t)}
    return As, ss, B


def planted_spec():
    return {"name": "r3b_planted", "kind": "planted", "t": 6, "d": 6, "p": 3,
            "au": planted()[0][0]}


def params(spec):
    """(t, d, au, s0, phis, kd, pvecs) of an instance."""
    if spec["kind"] == "planted":
        As, ss, B = planted()
        phis = (None,) + tuple(B[(0, i)] for i in range(1, 6))
        return 6, 6, As[0], ss[0], phis, 3, [phis[i] for i in (3, 4, 5)]
    t, d, p = spec["t"], spec["d"], spec["p"]
    return t, d, spec["au"], 1, phis_for(d, p), d - p, list(p_basis(p))


def units_consistent(cnf):
    lits = {c[0] for c in cnf.clauses if len(c) == 1}
    return all(-x not in lits for x in lits)


# ---------- the XOR encoding (m50.py) ----------

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

def pair_cls(name):
    """(pair, class) of a name r3b_t7_B5_oPPP_cCCC."""
    return int(name[11:14]), int(name[16:19])


def x1_of(pair):
    return X1_OF_ORBIT[0 if pair < FIRST_BETA_PAIR else 1]


def b5_spec(name, au):
    pi, ci = pair_cls(name)
    return {"name": name, "kind": "main", "t": T, "d": D, "p": 5, "pair": pi, "cls": ci,
            "x1": list(x1_of(pi)), "r": list(PAIR_R[pi]), "au": au}


def meet_d(spec):
    return dim_meet(tuple(spec["x1"]), tuple(spec["r"]))


def fix_a1(cnf, names, t, a1):
    """t^2 unit clauses A_(v_1) = a1 (as m53.py). Returns the number added."""
    A = names[0]
    for r in range(t):
        for c in range(t):
            cnf.clauses.append([A[1][r][c]] if (a1 >> (t * r + c)) & 1 else [-A[1][r][c]])
    return t * t


def build_plain(spec):
    t, d, au, s0, phis, kd, pvecs = params(spec)
    cnf, names = encode_fixed(t, d, au, s0, phis)
    hints = add_hints(cnf, names, t, kd, au, s0, pvecs)
    units = fix_a1(cnf, names, t, spec["a1"]) if "a1" in spec else 0
    return cnf, names, hints, units


def build(spec, arm):
    """(cnf, names, hints, units) of an instance for an arm ("cadical" or "xor")."""
    return with_xor(build_plain, spec) if arm == "xor" else build_plain(spec)


def planted_with_a1(a1=None):
    spec = planted_spec()
    spec["a1"] = planted()[0][1] if a1 is None else a1
    return spec


def column(m, c, t=T):
    return sum(((m >> (t * r + c)) & 1) << r for r in range(t))


def rank_on_x1(m):
    return len(rref([column(m, c) for c in range(4)]))


def admissible_b6(m):
    """m is in Adm of Proposition 30 (a) for the kind-P class (m53.admissible)."""
    cols = [column(m, c) for c in range(T)]
    return (cols[0] == 0 and all(in_span(B6_R, v) for v in cols) and rank_on_x1(m) <= 2
            and m != 0 and m != B6_AU)


def plan(group):
    """[(spec, arm, cap seconds, condition)] in running order; condition "a07_open" runs the entry
    only if a07 is still undecided."""
    if group == "a":
        return [(b5_spec(n, au), "cadical", 900.0, None) for n, au in sorted(BATCH_C.items())]
    out = [(dict(A07), "cadical", 900.0, None), (dict(A07), "xor", 900.0, "a07_open")]
    out += [(b5_spec(n, au), "xor", 300.0, None) for n, au in sorted(LEFTOVERS.items())]
    return out


# ---------- solving ----------

def child(spec, arm, path):
    cnf, names, _, _ = build(spec, arm)
    start = time.time()
    if any(len(c) == 0 for c in cnf.clauses):
        res = {"status": "UNSAT", "solver": "trivial", "seconds": 0.0}
    elif arm == "xor":
        from pycryptosat import Solver
        s = Solver(threads=1)
        for c in cnf.clauses:
            s.add_clause(c)
        for vs, rhs in cnf.xors:
            s.add_xor_clause(vs, bool(rhs))
        ok, sol = s.solve()
        res = {"status": "SAT" if ok else ("UNSAT" if ok is False else "UNKNOWN"),
               "solver": "cryptominisat5", "vars": cnf.nv, "clauses": len(cnf.clauses),
               "xors": len(cnf.xors), "seconds": round(time.time() - start, 2)}
        if ok:
            model = [v if sol[v] else -v for v in range(1, len(sol))]
            As, ss, B = sa.decode(model, names, spec["t"], spec["d"])
            res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    else:
        from pysat.solvers import Solver
        s, used = None, None
        for name in sa.SOLVERS:
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


def verify(spec, res):
    """A SAT answer is a system, anisotropic, in the normal form with A_u (and A_(v_1)) as fixed;
    records rank A_u and the largest rank."""
    t, d, au, s0, phis, kd, pvecs = params(spec)
    As, ss = res["A"], res["s"]
    B = {(i, k): v for i, k, v in res["B"]}
    at, sv = sa.tables(As, ss, B, d)
    nf = (As[0] == au and ss[0] == s0 and ("a1" not in spec or As[1] == spec["a1"])
          and all(phis[i] is None or B[(0, i)] == phis[i] for i in range(1, d)))
    res["verified"] = sa.is_system(at, sv, d, t) and sa.anisotropic(sv) and nf
    ranks = [sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d)]
    res["max_rank"] = max(ranks)
    res["rank_u"] = ranks[0]


def tag_of(spec, arm):
    return f"{spec['name']}__{arm}"


def solve_one(spec, arm, budget, out_dir):
    tag = tag_of(spec, arm)
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
    res.update({k: v for k, v in spec.items() if k != "kind"})
    res.update({"kind": spec["kind"], "arm": arm, "wall_seconds": round(time.time() - start, 2),
                "budget_seconds": round(budget, 1)})
    if res["status"] == "SAT":
        verify(spec, res)
    with open(os.path.join(out_dir, tag + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {tag}: {res['status']} {res['wall_seconds']} s", flush=True)
    return res


def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    entries = plan(group)
    counts, a07_open = {}, True
    for k, (spec, arm, cap, cond) in enumerate(entries):
        if cond == "a07_open" and not a07_open:
            continue
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            budget = min(cap, max(min(MIN_BUDGET, left), left / (len(entries) - k)))
            if spec["name"] == A07["name"]:
                budget = min(cap, left)
            res = solve_one(spec, arm, budget, out_dir)
        if spec["name"] == A07["name"] and res["status"] in ("SAT", "UNSAT"):
            a07_open = False
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- check ----------

def check(out_dir, random_cases=100):
    start = time.time()
    graded, st = {}, {}
    specs = {"a": [b5_spec(n, au) for n, au in sorted(BATCH_C.items())],
             "b": [b5_spec(n, au) for n, au in sorted(LEFTOVERS.items())]}
    allb5 = specs["a"] + specs["b"]
    graded["reps"] = all(kernel(s["au"], T) == tuple(s["x1"])
                         and column_space(s["au"], T) == tuple(s["r"])
                         and sa.rank_f2(cols_of(s["au"], T)) == 3 for s in allb5)
    by_d = {}
    for g, sps in specs.items():
        by_d[g] = {}
        for s in sps:
            by_d[g][str(meet_d(s))] = by_d[g].get(str(meet_d(s)), 0) + 1
    st["by_d"] = by_d
    graded["hand_d"] = by_d == HAND_D_COUNTS
    graded["lists"] = (len(BATCH_C) == 17 and len(LEFTOVERS) == 21
                       and not set(BATCH_C) & set(LEFTOVERS))
    graded["a07"] = (kernel(B6_AU, T) == B6_X1 and column_space(B6_AU, T) == B6_R
                     and dim_meet(B6_X1, B6_R) == 3 and admissible_b6(A07["a1"])
                     and rank_on_x1(A07["a1"]) == A07["rank_x1"])
    # Hints and units, both arms.
    probes = {}
    for arm in ("cadical", "xor"):
        c5, _, h5, u5 = build(specs["a"][0], arm)
        c6, _, h6, u6 = build(dict(A07), arm)
        probes[arm] = {"B5_hints": h5, "B6_hints": h6, "B6_units": u6, "B5_vars": c5.nv,
                       "B6_vars": c6.nv, "B6_xors": len(getattr(c6, "xors", ()))}
        graded[f"hints_{arm}"] = (h5 == HAND_HINTS["B5"] and h6 == HAND_HINTS["B6"]
                                  and u5 == 0 and u6 == T * T
                                  and units_consistent(c5) and units_consistent(c6))
    st["probes"] = probes
    graded["xor_is_smaller"] = (probes["xor"]["B6_vars"] < probes["cadical"]["B6_vars"]
                                and probes["xor"]["B6_xors"] > 0)
    # The XOR instance against the CNF on random small systems (as m50.py's check).
    rng = random.Random(5757)
    agree = disagree = good = 0
    for t, d, As, ss, B in sa.random_examples(rng, random_cases):
        at, sv = sa.tables(As, ss, B, d)
        ok = sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
        plain = sa.encode(t, d, echelon=False)
        xcnf = with_xor(sa.encode, t, d, True, True, False)
        a = accepts(plain[0], sa.assignment(plain[0], plain[1], As, ss, B, t, d))
        b = accepts(xcnf[0], sa.assignment(xcnf[0], xcnf[1], As, ss, B, t, d))
        good += ok
        if a == b == ok:
            agree += 1
        else:
            disagree += 1
    st["random"] = {"cases": agree + disagree, "good": good, "disagree": disagree}
    graded["xor_agrees_with_cnf"] = disagree == 0 and 0 < good < agree
    # The positive control: the planted system at t = 6 with A_(v_1) fixed to its own map.
    As, ss, B = planted()
    for arm in ("cadical", "xor"):
        pc, pn, ph, _ = build(planted_with_a1(), arm)
        qc, qn, _, _ = build(planted_with_a1(As[1] ^ 1), arm)
        graded[f"planted_accepted_{arm}"] = (ph == HAND_HINTS["planted"]
                                             and accepts(pc, sa.assignment(pc, pn, As, ss, B, 6, 6)))
        graded[f"planted_flip_rejected_{arm}"] = not accepts(
            qc, sa.assignment(qc, qn, As, ss, B, 6, 6))
    for arm in ("cadical", "xor"):
        res = solve_one(planted_with_a1(), arm, PLANTED_BUDGET[arm], out_dir)
        if res["status"] in ("SAT", "UNSAT"):
            graded[f"planted_sat_{arm}"] = res["status"] == "SAT" and bool(res.get("verified"))
        else:
            st[f"planted_ungraded_{arm}"] = res["status"]
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- grading (pre-registered in m57-predictions.md) ----------

def grade(group, out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    rows, by_arm, by_d = {}, {}, {}
    for spec, arm, _, _ in plan(group):
        path = os.path.join(out_dir, tag_of(spec, arm) + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        tag = tag_of(spec, arm)
        rows[tag] = [s, r.get("wall_seconds")]
        by_arm.setdefault(arm, {})
        by_arm[arm][s] = by_arm[arm].get(s, 0) + 1
        if spec["p"] == 5:
            dk = str(meet_d(spec))
            by_d.setdefault(dk, {})
            by_d[dk][s] = by_d[dk].get(s, 0) + 1
        if s == "SAT":
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    out = {"graded": graded, "ungraded": ungraded, "rows": rows, "by_arm": by_arm, "by_d": by_d,
           "b5_unsat": sorted(t.split("__")[0] for t, (s, _) in rows.items()
                              if s == "UNSAT" and t.startswith("r3b_")),
           "any_sat_7": any(s == "SAT" for s, _ in rows.values())}
    if group == "b":
        a07 = [rows.get(tag_of(A07, arm), [None])[0] for arm in ("cadical", "xor")]
        out["a07"] = a07
        out["kind_p_empty"] = "UNSAT" in a07
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "child", "grade"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="{}")
    ap.add_argument("--arm", default="cadical")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.arm, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} by_arm {json.dumps(out['by_arm'], sort_keys=True)} "
              f"kind_p_empty {out.get('kind_p_empty')}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
