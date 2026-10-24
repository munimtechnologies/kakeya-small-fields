# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m97: Lemma 98 (the square identity of type (N4), notes/a89.md) on solver models, a small
reduced system built from it, and the CNFs of rank 4 at t = 8 without anisotropy
(cube_groups/m97-predictions.md).

What came back on 2026-10-24 (job m96, notes/a89.md): without its anisotropy clauses ("relax") the
CNF of type (N4) has models at (4, 2) for M = N and E and at (6, 3) for (E_00, E_11) and (E_00, E_12),
and none for M = I + N, F, for (N, N^2) and for m94's pilot at (8, 4). By hand (a89.md), in type
(N4) and without anisotropy, every y in Y satisfies

    M_y^2 = M_(n(z_y)),  z_y = G_y y,   (G_y + G_y^2) y = 0,   T q(y) = y + z_y,
    T M_n q(y) = (G_y + G_y^2) sigma(n) for n in N,                                (Lemma 98)

where M_y = M_(n_y), G_y = A_(h_y) on X_1, n(x) is the element of N with sigma value x, and T = A_u
on X / X_1. At k = 2 these force M^2 = 0 or M^2 = M, which is exactly the split m96 found.

Parts:

    selfcheck  the 23 orbits of type (N4) in m95's published m95_orbits.json against N4_ORBITS
    models     relax models at (4, 2) and (6, 3) (several per instance, each blocked after it is
               read): (*) as (L) and (Q) and by brute force, the normal form, every family of m95,
               not anisotropic, and every identity of Lemma 98 read off the model
    reduced    the reduced system of Lemma 98 for the 7 small instances and the 23 orbits at
               (8, 4), at three levels: relax; aniso1 (q(y) != 0, Lemma 38(e)); aniso2 (also
               dim span q(Y) >= k - 1, Lemma 38(e))
    t8         the relax CNF of each of the 23 orbits (m95.encode_rank4 + m95.relax), solved with a
               cap; models checked as in "models" ((*) as (L) and (Q) only)
    grade      the graded checks of m97-predictions.md

The reduced system: unknowns G_a = G_(e_a) (1 <= a < k), k x k on X_1 with G_a x0 = e_a, and
S = T^(-1). Lemma 98 fixes z_y (n -> M_n is one-to-one on N), so G_a e_a = z_(e_a), and
G_a e_b + G_b e_a = z_(e_a + e_b) + z_(e_a) + z_(e_b) for a != b: (k - 1)(k - 2)/2 free vectors of
X_1. For each choice: z_y = G_y y for every y, (G_y + G_y^2) y = 0, and the equations
M_i S w_y = S H_y e_i (w_y = y + z_y, H_y = G_y + G_y^2) are linear in S; the system is SAT if some
solution S is invertible. Every condition is a consequence of (*) and the hypotheses of the CNF
(a89.md), so an instance whose reduced system is UNSAT has no model, and every model of a relax CNF
gives a solution of its reduced system.

Vectors: X_1 = span(e_0, ..., e_(k-1)) with bit c = coordinate of e_c (x0 = e_0); X / X_1 with bit
l = coordinate of [e_(k+l)]; M[l][j] is entry (l, j), column j the image of [e_(k+j)] (m94.m_of).

Usage: python m97.py --part selfcheck|models|reduced|t8|grade [--orbits FILE] [--cap-seconds S]
       [--minutes M] [--out-dir DIR]
"""
import argparse
import json
import os
import threading
import time

import case_b_shapes as csh
import m94
import m95
import sat_aniso as sa

# m95a's 23 orbits of type (N4) at (8, 4): (index, basis masks of W, orbit size), from
# compete-results/m95a-n4-orbits-v1/out/m95a_rows.json (2026-10-23).
N4_ORBITS = [(0, (1, 32, 1024), 3360), (1, (1, 32, 2048), 5040), (4, (1, 64, 128), 840),
             (5, (1, 64, 1056), 10080), (6, (1, 64, 16384), 840), (7, (1, 64, 16512), 2520),
             (11, (1, 608, 1056), 3360), (14, (1, 1056, 32800), 3360), (18, (2, 4, 8), 15),
             (19, (2, 4, 1057), 840), (20, (2, 4, 8192), 315), (21, (2, 4, 8200), 315),
             (25, (2, 33, 2048), 5040), (28, (2, 512, 1057), 840), (29, (2, 512, 8192), 15),
             (30, (2, 512, 8200), 315), (34, (2, 516, 1057), 2520), (35, (2, 516, 8200), 315),
             (39, (2, 520, 2048), 210), (40, (2, 520, 8196), 105), (41, (2, 520, 10244), 630),
             (48, (2, 1057, 32801), 5040), (57, (2, 19456, 33792), 1680)]
PILOT = 5
SMALL = {"t4_N": (4, 2, [[[0, 0], [1, 0]]]), "t4_IN": (4, 2, [[[1, 0], [1, 1]]]),
         "t4_E": (4, 2, [[[1, 0], [0, 0]]]), "t4_F": (4, 2, [[[0, 1], [1, 1]]]),
         "t6_shift": (6, 3, [m94.SHIFT, m94.SHIFT2]),
         "t6_e00e11": (6, 3, [[[1, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 1, 0], [0, 0, 0]]]),
         "t6_e00e12": (6, 3, [[[1, 0, 0], [0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 1], [0, 0, 0]]])}
# job m96a (2026-10-23): the relax answers, and the hand derivations of a89.md for the reduced system
M96_RELAX = {"t4_N": "SAT", "t4_IN": "UNSAT", "t4_E": "SAT", "t4_F": "UNSAT", "t6_shift": "UNSAT",
             "t6_e00e11": "SAT", "t6_e00e12": "SAT"}
LEVELS = ("relax", "aniso1", "aniso2")
MODELS_PER = 6        # models read per SAT instance at t <= 6
MODELS_T8 = 3
INVERT_CAP = 4096     # elements of a solution space tried for an invertible S


def orbit_name(index, size):
    return f"n4_o{index:02d}_s{size}"


def instances():
    """(name, t, k, Ms) for the small instances and the 23 orbits."""
    out = [(name, t, k, Ms) for name, (t, k, Ms) in SMALL.items()]
    out += [(orbit_name(i, s), 8, 4, [m94.m_of(x, 4) for x in w]) for i, w, s in N4_ORBITS]
    return out


# ---------- the matrices M(x) and maps of X_1 ----------

def mat_x(Ms, x):
    """M_(n(x)) = x_0 I + sum of x_i M_i for x in X_1."""
    n = len(Ms[0])
    out = [[(x & 1) * int(r == c) for c in range(n)] for r in range(n)]
    for i, M in enumerate(Ms, 1):
        if x >> i & 1:
            out = m94.add(out, M)
    return out


def span_index(Ms):
    """flat(M(x)) -> x; ValueError if x -> M(x) is not one-to-one."""
    k = len(Ms) + 1
    index = {m94.flat(mat_x(Ms, x)): x for x in range(1 << k)}
    if len(index) != 1 << k:
        raise ValueError("n -> M_n is not one-to-one")
    return index


def g_apply(cols, x):
    """The map with columns cols (bit masks) applied to x."""
    out = 0
    c = 0
    while x:
        if x & 1:
            out ^= cols[c]
        x >>= 1
        c += 1
    return out


def ys_of(k):
    """The non-zero y in Y = span(e_1, ..., e_(k-1))."""
    return list(range(2, 1 << k, 2))


def squares(Ms):
    """z_y with M_y^2 = M(z_y) for every y, or (None, y) for the first y whose square is outside
    span(I, M_1, ..., M_(k-1))."""
    k = len(Ms) + 1
    index = span_index(Ms)
    z = {}
    for y in ys_of(k):
        My = mat_x(Ms, y)
        sq = m94.flat(m94.mul(My, My))
        if sq not in index:
            return None, y
        z[y] = index[sq]
    return z, None


# ---------- the reduced system ----------

def s_equations(Ms, w, H):
    """The equations M_i S w_y = S H_y e_i over the k^2 entries of S (variable r k + c = S[r][c]),
    for every y: w[y] a vector of X_1, H[y] the columns of H_y."""
    k = len(Ms) + 1
    eqs = []
    for y in w:
        for i in range(1, k):
            Mi = Ms[i - 1]
            h = H[y][i]
            for r in range(k):
                mask = 0
                for l in range(k):
                    if Mi[r][l]:
                        for c in range(k):
                            if w[y] >> c & 1:
                                mask ^= 1 << (l * k + c)
                for c in range(k):
                    if h >> c & 1:
                        mask ^= 1 << (r * k + c)
                if mask:
                    eqs.append(mask)
    return eqs


def s_rows(S, k):
    return [(S >> (r * k)) & ((1 << k) - 1) for r in range(k)]


def invertible_in(basis, k, cap=INVERT_CAP):
    """(S, complete): an invertible S in the span of basis (as a k^2-bit mask), or None. If some
    row or column of S is 0 on the whole span, there is none; otherwise at most cap elements are
    tried, and complete is False if the cap was reached first."""
    rows = [0] * k
    for b in basis:
        rows = [x | y for x, y in zip(rows, s_rows(b, k))]
    cols = 0
    for x in rows:
        cols |= x
    if not all(rows) or cols != (1 << k) - 1:
        return None, True
    n = 1 << len(basis)
    for c in range(1, min(n, cap + 1)):
        S = sa.combine(basis, c)
        if sa.rank_f2(s_rows(S, k)) == k:
            return S, True
    return None, n <= cap + 1


def reduced(Ms, level="relax"):
    """The reduced system of Lemma 98 for the tuple Ms (k - 1 commuting k x k matrices)."""
    k = len(Ms) + 1
    if len(Ms[0]) != k:
        raise ValueError("type (N4) needs t = 2 k")
    ys = ys_of(k)
    z, bad = squares(Ms)
    if z is None:
        return {"status": "UNSAT", "stage": "square", "y": bad}
    if level != "relax":
        same = [y for y in ys if z[y] == y]
        if same:
            return {"status": "UNSAT", "stage": "q_zero", "y": same[0], "z": z}
    pairs = [(a, b) for a in range(1, k) for b in range(a + 1, k)]
    s = {(a, b): z[(1 << a) | (1 << b)] ^ z[1 << a] ^ z[1 << b] for a, b in pairs}
    counts = {"choices": 1 << (k * len(pairs)), "linear": 0, "rank": 0, "solved": 0, "capped": 0}
    for bits in range(counts["choices"]):
        G = {a: [0] * k for a in range(1, k)}
        for a in range(1, k):
            G[a][0] = 1 << a
            G[a][a] = z[1 << a]
        for p, (a, b) in enumerate(pairs):
            v = (bits >> (k * p)) & ((1 << k) - 1)
            G[a][b] = v
            G[b][a] = v ^ s[(a, b)]
        ok = True
        w, H = {}, {}
        for y in ys:
            Gy = [0] * k
            for a in range(1, k):
                if y >> a & 1:
                    Gy = [x ^ g for x, g in zip(Gy, G[a])]
            zy = g_apply(Gy, y)
            if zy != z[y] or zy ^ g_apply(Gy, zy):
                ok = False
                break
            w[y] = y ^ zy
            H[y] = [g ^ g_apply(Gy, g) for g in Gy]
        if not ok:
            continue
        counts["linear"] += 1
        if level == "aniso2" and sa.rank_f2(list(w.values())) < k - 1:
            continue
        counts["rank"] += 1
        sol = sa.nullspace(s_equations(Ms, w, H), k * k)
        S, complete = invertible_in(sol, k)
        if S is None:
            counts["capped"] += not complete
            continue
        counts["solved"] += 1
        return {"status": "SAT", "stage": "solved", "counts": counts, "z": z,
                "G": {a: G[a] for a in G}, "S_rows": s_rows(S, k), "w": w}
    stage = "no_invertible_S" if counts["rank"] else ("rank" if counts["linear"] else "linear")
    return {"status": "UNKNOWN" if counts["capped"] else "UNSAT", "stage": stage,
            "counts": counts, "z": z}


# ---------- Lemma 98 read off a model ----------

def identities(As, ss, B, t, k, Ms):
    """Every hypothesis and identity of a89.md on the decoded system (As, ss, B) in the normal
    form: u = v_0, n(x) = sum of v_i over the bits i of x, h_(e_j) = v_(k-1+j)."""
    d = t + k - 1
    low = (1 << k) - 1
    at, sv = sa.tables(As, ss, B, d)
    out = {"coeff_ok": sa.coeff_ok(As, ss, B, t, d), "anisotropic": sa.anisotropic(sv),
           "shape": csh.in_shape(As, ss, B, t, k, "c")}
    out.update(m95.fixed_parts(As, B, t, k, Ms))
    if t <= 6:
        out["system"] = sa.is_system(at, sv, d, t)
    tcol = [sa.mat_apply(As[0], 1 << (k + l), t) for l in range(k)]
    out["T_into_X1"] = all(c <= low for c in tcol)
    out["sigma_N"] = all(sv[x] == x for x in range(1 << k))
    index = span_index(Ms)
    keep = l98 = r2 = five = l46 = True
    for y in ys_of(k):
        hm = (y >> 1) << k
        A = at[hm]
        gc = [sa.mat_apply(A, 1 << c, t) for c in range(k)]
        keep = keep and all(c <= low for c in gc)
        G = [c & low for c in gc]
        z = g_apply(G, y)
        My = mat_x(Ms, y)
        l98 = l98 and index.get(m94.flat(m94.mul(My, My))) == z
        r2 = r2 and not z ^ g_apply(G, z)
        q = sv[hm] >> k
        five = five and g_apply(tcol, q) == y ^ z
        H = [g ^ g_apply(G, g) for g in G]
        for i in range(1, k):
            five = five and g_apply(tcol, m95.apply(Ms[i - 1], q)) == H[i]
        for l in range(k):
            want = sum(My[r][l] << r for r in range(k))
            l46 = l46 and (sa.mat_apply(A, 1 << (k + l), t) >> k) == want
    out.update({"G_keeps_X1": keep, "lemma98": l98, "r2": r2, "five": five, "lemma46a": l46})
    return out


def model_ok(chk):
    """A relax model must satisfy everything but anisotropy (the full CNF is UNSAT)."""
    keys = ("coeff_ok", "shape", "units", "inv", "lin", "a", "T_into_X1", "sigma_N", "G_keeps_X1",
            "lemma98", "r2", "five", "lemma46a")
    return (all(chk[x] for x in keys) and chk.get("system") is not False
            and not chk["anisotropic"])


def short_model(chk):
    return ",".join(sorted(x for x, v in chk.items() if v is False and x != "anisotropic")) or "ok"


# ---------- solving a relax CNF ----------

def relax_cnf(t, k, Ms):
    cnf, names, info = m95.encode_rank4(t, k, Ms)
    dropped = m95.relax(cnf, t)
    return cnf, names, dropped


def primaries(names, t, d):
    A, S, Bv = names[0], names[1], names[2]
    out = [A[i][r][c] for i in range(d) for r in range(t) for c in range(t)]
    out += [S[i][r] for i in range(d) for r in range(t)]
    out += [v for key in sorted(Bv) for v in Bv[key]]
    return out


def solve_models(t, k, Ms, count, cap, deadline):
    """(status, seconds, dropped, models): the relax CNF solved, then each model blocked on the
    variables of (A_i, s_i, B_ij) and solved again, up to count models."""
    from pysat.solvers import Solver
    d = t + k - 1
    cnf, names, dropped = relax_cnf(t, k, Ms)
    s = Solver(name="glucose4", bootstrap_with=cnf.clauses)
    prim = primaries(names, t, d)
    models, status, first = [], None, None
    while len(models) < count and time.time() < deadline:
        timer = threading.Timer(cap, s.interrupt)
        start = time.time()
        timer.start()
        try:
            res = s.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        s.clear_interrupt()
        sec = round(time.time() - start, 2)
        st = {True: "SAT", False: "UNSAT", None: "UNKNOWN"}[res]
        if status is None:
            status, first = st, sec
        if st != "SAT":
            break
        model = s.get_model()
        pos = {x for x in model if x > 0}
        models.append(sa.decode(model, names, t, d))
        s.add_clause([-v if v in pos else v for v in prim])
    s.delete()
    return status, first, dropped, models


# ---------- the parts ----------

def selfcheck(orbits_file, out_dir):
    with open(orbits_file) as f:
        st = json.load(f)
    theirs = [(o["index"], tuple(o["basis"]), o["size"]) for o in st["orbits"] if o["n4"]]
    g = {"orbits_equal": theirs == N4_ORBITS, "orbits_23": len(N4_ORBITS) == 23,
         "pilot": N4_ORBITS[3] == (PILOT, tuple(m94.PILOT_W), 10080),
         "tuples_ok": all(m94.check_tuple(Ms) for _, _, _, Ms in instances())}
    with open(os.path.join(out_dir, "m97_selfcheck.json"), "w") as f:
        json.dump({"graded": g}, f, indent=1)
    print(f"SUMMARY selfcheck all_match {all(g.values())} {json.dumps(g, sort_keys=True)}",
          flush=True)


def run_models(cap, minutes, out_dir, names_wanted, count, label):
    start = time.time()
    rows = []
    for name, t, k, Ms in instances():
        if name not in names_wanted:
            continue
        if time.time() - start > minutes * 60:
            rows.append({"name": name, "status": "SKIPPED"})
            continue
        status, sec, dropped, models = solve_models(t, k, Ms, count, cap,
                                                    start + minutes * 60)
        checks = [identities(As, ss, B, t, k, Ms) for As, ss, B in models]
        row = {"name": name, "t": t, "k": k, "status": status, "seconds": sec,
               "aniso_dropped": dropped, "aniso_expected": (1 << (t + k - 1)) - 1,
               "models": len(models), "models_ok": [model_ok(c) for c in checks],
               "checks": checks}
        if models:
            As, ss, B = models[0]
            row["first_model"] = {"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in
                                                         sorted(B.items())]}
        rows.append(row)
        print(f"{label} {name}: relax {status} {sec} s dropped {dropped} models {len(models)} "
              f"ok {sum(row['models_ok'])} "
              f"{' '.join(short_model(c) for c in checks)}", flush=True)
        with open(os.path.join(out_dir, f"m97_{label}.json"), "w") as f:
            json.dump(rows, f, indent=1)
    with open(os.path.join(out_dir, f"m97_{label}.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print(f"SUMMARY {label} " + json.dumps({r["name"]: [r["status"], r.get("models"),
                                                       sum(r.get("models_ok", []))]
                                            for r in rows}, sort_keys=True), flush=True)


def run_reduced(out_dir):
    rows = []
    for name, t, k, Ms in instances():
        start = time.time()
        row = {"name": name, "t": t, "k": k}
        for level in LEVELS:
            res = reduced(Ms, level)
            row[level] = res
        row["seconds"] = round(time.time() - start, 2)
        rows.append(row)
        print(f"reduced {name}: " + " ".join(
            f"{lv} {row[lv]['status']}({row[lv]['stage']})" for lv in LEVELS)
            + f" seconds {row['seconds']}", flush=True)
    with open(os.path.join(out_dir, "m97_reduced.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print("SUMMARY reduced " + json.dumps({r["name"]: [r[lv]["status"] for lv in LEVELS]
                                           for r in rows}, sort_keys=True), flush=True)


def load(out_dir, name):
    p = os.path.join(out_dir, name)
    if not os.path.exists(p):
        return None
    with open(p) as f:
        return json.load(f)


def grade(out_dir):
    g = {}
    st = load(out_dir, "m97_selfcheck.json") or {"graded": {"selfcheck": False}}
    for key, ok in st["graded"].items():
        g["selfcheck_" + key] = bool(ok)
    red = {r["name"]: r for r in load(out_dir, "m97_reduced.json") or []}
    g["reduced_all"] = len(red) == len(instances())
    for name, want in M96_RELAX.items():
        if name in red:
            g["reduced_" + name] = red[name]["relax"]["status"] == want
    small = {r["name"]: r for r in load(out_dir, "m97_models.json") or []}
    t8 = {r["name"]: r for r in load(out_dir, "m97_t8.json") or []}
    g["models_all"] = len(small) == len(SMALL)
    for name, r in list(small.items()) + list(t8.items()):
        if r["status"] in ("SKIPPED", "UNKNOWN", None):
            continue
        g["dropped_" + name] = r["aniso_dropped"] == r["aniso_expected"]
        if name in M96_RELAX:
            g["relax_as_m96_" + name] = r["status"] == M96_RELAX[name]
        if r["status"] == "SAT":
            g["models_ok_" + name] = r["models"] > 0 and all(r["models_ok"])
            if name in red:
                g["consistent_" + name] = red[name]["relax"]["status"] == "SAT"
    pilot = orbit_name(PILOT, 10080)
    if pilot in t8 and t8[pilot]["status"] in ("SAT", "UNSAT"):
        g["pilot_relax_unsat"] = t8[pilot]["status"] == "UNSAT"
    orbits = [orbit_name(i, s) for i, _, s in N4_ORBITS]
    out = {"graded": g,
           "reduced": {n: [red[n][lv]["status"] + "(" + red[n][lv]["stage"] + ")"
                           for lv in LEVELS] for n in red},
           "t8_relax": {n: [r["status"], r.get("seconds"), r.get("models")] for n, r in t8.items()},
           "small_relax": {n: [r["status"], r.get("models")] for n, r in small.items()},
           "orbits_aniso2_unsat": sum(red[n]["aniso2"]["status"] == "UNSAT" for n in orbits
                                      if n in red),
           "orbits_aniso1_unsat": sum(red[n]["aniso1"]["status"] == "UNSAT" for n in orbits
                                      if n in red),
           "orbits_relax_unsat": sum(red[n]["relax"]["status"] == "UNSAT" for n in orbits
                                     if n in red),
           "t8_relax_sat": sorted(n for n, r in t8.items() if r["status"] == "SAT")}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "models", "reduced", "t8", "grade"],
                    default="selfcheck")
    ap.add_argument("--orbits", default="m95_orbits.json")
    ap.add_argument("--cap-seconds", type=float, default=60.0)
    ap.add_argument("--minutes", type=float, default=60.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "selfcheck":
        selfcheck(args.orbits, args.out_dir)
    elif args.part == "models":
        run_models(args.cap_seconds, args.minutes, args.out_dir, set(SMALL), MODELS_PER, "models")
    elif args.part == "t8":
        run_models(args.cap_seconds, args.minutes, args.out_dir,
                   {orbit_name(i, s) for i, _, s in N4_ORBITS}, MODELS_T8, "t8")
    elif args.part == "reduced":
        run_reduced(args.out_dir)
    else:
        out = grade(args.out_dir)
        with open(os.path.join(args.out_dir, "m97_grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        print(f"SUMMARY grade all_match {not bad} graded {len(out['graded'])} failed {bad} "
              f"orbits relax/aniso1/aniso2 UNSAT {out['orbits_relax_unsat']}/"
              f"{out['orbits_aniso1_unsat']}/{out['orbits_aniso2_unsat']} of 23 t8 relax SAT "
              f"{out['t8_relax_sat']} reduced {json.dumps(out['reduced'], sort_keys=True)}",
              flush=True)


if __name__ == "__main__":
    main()
