# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m98: the reduced system of Lemma 98 checked against solver models, decided without a cap,
the positive control for d = 3, and DRAT certificates for m95b's 159 instances
(cube_groups/m98-predictions.md, notes/a90.md).

What came back on 2026-10-24 (job m97, notes/a90.md): 67 of 69 graded checks held. Every identity
of Lemma 98 held on every model, at t = 4, 6 and 8. The relax CNF (no anisotropy clauses) has
checked models at t = 8 for orbits 0, 1, 6, 14 and 29 of type (N4), so the encoder has a positive
control at t = 8. With anisotropy, the reduced system is UNSAT for 20 of the 23 orbits: 14 have a
non-zero idempotent in W (Lemma 99(c)), 6 have no invertible S even without anisotropy. Orbits 18,
29 and 40 survive it. The two failed checks: orbits 0 and 14 have relax models, but m97's reduced
system answered UNKNOWN for them, because m97.invertible_in only tries the combinations of the
first 12 vectors of a solution space (its cap of 4096), and their spaces are larger.

Parts:

    selfcheck   m97's orbit list against m95_orbits.json, the 159 d = 3 instances, and relax by
                prefix (only the clauses sat_aniso.encode wrote are scanned) against m95.relax
    consistent  relax models of the 4 SAT instances at t <= 6 and of the 5 SAT orbits at t = 8: the
                pair (G, S = T^(-1)) read off each model must lie in the search space of
                m97.reduced and solve every condition of it, recomputed here by matrix products
    reduced2    m97.reduced for all 30 instances and 3 levels with a complete search for an
                invertible S (random tries, then every element of the solution space)
    d3          the relax CNF (by prefix) of each of the 159 instances with d = 3, models checked
                ((L), (Q), shape (c), every family of m95 with D = ker f, not anisotropic)
    controls    cert1's tool controls (m95.run_controls)
    certb       m95b's 159 instances solved again, each UNSAT answer certified (CaDiCaL writes a
                DRAT proof, drat-trim checks it), as m95a did for its 23
    grade_a     the graded checks of parts selfcheck to d3
    grade_b     the graded checks of parts controls and certb

Usage: python m98.py --part selfcheck|consistent|reduced2|d3|controls|certb|grade_a|grade_b
       [--orbits FILE] [--tools DIR] [--cap-seconds S] [--minutes M] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import tempfile
import threading
import time

import m94
import m95
import m97
import sat_aniso as sa

T, K = 8, 4
CONSISTENT = ["t4_N", "t4_E", "t6_e00e11", "t6_e00e12", "n4_o00_s3360", "n4_o01_s5040",
              "n4_o06_s840", "n4_o14_s3360", "n4_o29_s15"]
MODELS = {6: 6, 8: 3}      # models read per instance at t <= 6 and at t = 8
# job m97 (compete-results/m97-square-identity-v1, 2026-10-24): the reduced system's answers at
# relax, aniso1, aniso2 ("U" UNSAT, "S" SAT, "?" UNKNOWN)
M97_REDUCED = {
    "t4_N": "SSS", "t4_IN": "UUU", "t4_E": "SUU", "t4_F": "UUU", "t6_shift": "UUU",
    "t6_e00e11": "SUU", "t6_e00e12": "SUU", "n4_o00_s3360": "?UU", "n4_o01_s5040": "SUU",
    "n4_o04_s840": "UUU", "n4_o05_s10080": "SUU", "n4_o06_s840": "SUU", "n4_o07_s2520": "UUU",
    "n4_o11_s3360": "UUU", "n4_o14_s3360": "?UU", "n4_o18_s15": "SSS", "n4_o19_s840": "UUU",
    "n4_o20_s315": "UUU", "n4_o21_s315": "UUU", "n4_o25_s5040": "UUU", "n4_o28_s840": "UUU",
    "n4_o29_s15": "SSS", "n4_o30_s315": "UUU", "n4_o34_s2520": "UUU", "n4_o35_s315": "UUU",
    "n4_o39_s210": "UUU", "n4_o40_s105": "SSS", "n4_o41_s630": "UUU", "n4_o48_s5040": "UUU",
    "n4_o57_s1680": "UUU"}
CODE = {"UNSAT": "U", "SAT": "S", "UNKNOWN": "?"}
DEADLINE = [float("inf")]  # for invertible_full, set per call of m97.reduced
RELAX_SECONDS = 600        # budget of one call of m97.reduced in reduced2
CAPPED = m97.invertible_in  # kept: reduced2 replaces m97.invertible_in by invertible_full


# ---------- linear algebra over F_2 (rows and columns as bit masks) ----------

def apply_rows(rows, v):
    """The matrix with the given rows applied to v."""
    return sum((bin(r & v).count("1") & 1) << i for i, r in enumerate(rows))


def rows_of_cols(cols, k):
    """Rows of the k x k matrix whose columns are cols."""
    return [sum((cols[c] >> r & 1) << c for c in range(k)) for r in range(k)]


def inverse_rows(rows, k):
    """Rows of the inverse of a k x k matrix given by rows, or None if it is singular."""
    aug = [rows[r] | (1 << (k + r)) for r in range(k)]
    for c in range(k):
        piv = next((r for r in range(c, k) if aug[r] >> c & 1), None)
        if piv is None:
            return None
        aug[c], aug[piv] = aug[piv], aug[c]
        for r in range(k):
            if r != c and aug[r] >> c & 1:
                aug[r] ^= aug[c]
    return [aug[r] >> k for r in range(k)]


def invertible_full(basis, k, cap=None):
    """Drop-in for m97.invertible_in without its cap: (S, complete) with S an invertible element of
    the span of basis (a k^2-bit mask) or None. Random tries first, then every element in Gray-code
    order; complete is False only if DEADLINE passed."""
    _, complete = CAPPED(basis, k, 0)
    if not complete:          # the zero-row/column test passed: search the span
        n = len(basis)
        rng = random.Random(n)
        for _ in range(min(256, (1 << n) - 1)):
            S = sa.combine(basis, rng.randrange(1, 1 << n))
            if sa.rank_f2(m97.s_rows(S, k)) == k:
                return S, True
        S = 0
        for i in range(1, 1 << n):
            S ^= basis[(i & -i).bit_length() - 1]
            if sa.rank_f2(m97.s_rows(S, k)) == k:
                return S, True
            if i & 4095 == 0 and time.time() > DEADLINE[0]:
                return None, False
    return None, True


# ---------- the reduced system recomputed on a pair (G, S) ----------

def check_solution(Ms, G, S_rows):
    """Every condition of m97.reduced on the pair (G, S), recomputed by matrix products: G[a] the
    columns of G_(e_a) on X_1 (1 <= a < k), S_rows the rows of S = T^(-1). Also the anisotropy
    levels aniso1 (z_y != y) and aniso2 (dim span{w_y} >= k - 1)."""
    k = len(Ms) + 1
    z, bad = m97.squares(Ms)
    if z is None:
        return {"square": False}
    low = (1 << k) - 1
    out = {"square": True,
           "g_bits": all(0 <= x <= low for a in G for x in G[a]),
           "g_x0": all(G[a][0] == 1 << a for a in range(1, k)),
           "g_diag": all(G[a][a] == z[1 << a] for a in range(1, k)),
           "g_pairs": all(G[a][b] ^ G[b][a] == z[(1 << a) | (1 << b)] ^ z[1 << a] ^ z[1 << b]
                          for a in range(1, k) for b in range(a + 1, k)),
           "invertible": sa.rank_f2(list(S_rows)) == k}
    zm = r2 = eq = True
    ws = []
    for y in m97.ys_of(k):
        Gy = [0] * k
        for a in range(1, k):
            if y >> a & 1:
                Gy = [x ^ g for x, g in zip(Gy, G[a])]
        zy = m97.g_apply(Gy, y)
        zm = zm and zy == z[y]
        r2 = r2 and m97.g_apply(Gy, zy) == zy
        w = y ^ zy
        ws.append(w)
        H = [g ^ m97.g_apply(Gy, g) for g in Gy]
        Sw = apply_rows(S_rows, w)
        for i in range(1, k):
            eq = eq and m95.apply(Ms[i - 1], Sw) == apply_rows(S_rows, H[i])
    out.update({"z_match": zm, "r2": r2, "equations": eq})
    out["relax_ok"] = all(out.values())
    out["aniso1"] = all(z[y] != y for y in m97.ys_of(k))
    out["aniso2"] = out["aniso1"] and sa.rank_f2(ws) >= k - 1
    return out


def solution_of(As, ss, B, t, k):
    """(G, S_rows, q, flags) read off a decoded model in the normal form: G[a] = A_(v_(k-1+a)) on
    X_1, T = A_u on [e_k], ..., [e_(t-1)], S = T^(-1), q[y] = [sigma(h_y)]."""
    d = t + k - 1
    low = (1 << k) - 1
    gc = {a: [sa.mat_apply(As[k - 1 + a], 1 << c, t) for c in range(k)] for a in range(1, k)}
    G = {a: [x & low for x in gc[a]] for a in gc}
    tcol = [sa.mat_apply(As[0], 1 << (k + l), t) for l in range(k)]
    S_rows = inverse_rows(rows_of_cols([x & low for x in tcol], k), k)
    _, sv = sa.tables(As, ss, B, d)
    q = {y: sv[(y >> 1) << k] >> k for y in m97.ys_of(k)}
    flags = {"G_keeps_X1": all(x <= low for a in gc for x in gc[a]),
             "T_into_X1": all(x <= low for x in tcol), "T_invertible": S_rows is not None}
    return G, S_rows, q, flags


def model_solution(As, ss, B, t, k, Ms):
    """The checks of part consistent on one model."""
    G, S_rows, q, flags = solution_of(As, ss, B, t, k)
    out = dict(flags)
    out["identities_ok"] = m97.model_ok(m97.identities(As, ss, B, t, k, Ms))
    if S_rows is None:
        out["solution_ok"] = False
        return out
    chk = check_solution(Ms, G, S_rows)
    z, _ = m97.squares(Ms)
    out["q_is_Sw"] = all(q[y] == apply_rows(S_rows, y ^ z[y]) for y in q)
    out["check"] = chk
    out["solution_ok"] = (chk.get("relax_ok", False) and out["q_is_Sw"] and flags["G_keeps_X1"]
                          and flags["T_into_X1"])
    return out


# ---------- relax by prefix ----------

def relax_prefix(cnf, t, start):
    """m95.relax on the first start clauses only (those encode_shape wrote, where sat_aniso.encode
    puts the anisotropy clauses); the clauses after them are kept as they are."""
    head, tail = cnf.clauses[:start], cnf.clauses[start:]
    cnf.clauses = head
    dropped = m95.relax(cnf, t)
    cnf.clauses = cnf.clauses + tail
    return dropped


def d3_specs(orbits_file):
    with open(orbits_file) as f:
        st = json.load(f)
    return m95.group_specs("b", st["orbits"])


# ---------- the parts ----------

def selfcheck(orbits_file, out_dir):
    with open(orbits_file) as f:
        st = json.load(f)
    theirs = [(o["index"], tuple(o["basis"]), o["size"]) for o in st["orbits"] if o["n4"]]
    specs = d3_specs(orbits_file)
    g = {"orbits_equal": theirs == m97.N4_ORBITS, "d3_instances": len(specs) == 159,
         "d3_pilot_f1": any(s["w"] == list(m94.PILOT_W) and s["f"] == 1 for s in specs)}
    pilot = m94.pilot_ms()
    a, _, info = m95.encode_rank4(T, K, pilot)
    b, _, _ = m95.encode_rank4(T, K, pilot)
    da = m95.relax(a, T)
    db = relax_prefix(b, T, info["start"])
    g["prefix_d4_equal"] = a.clauses == b.clauses and da == db == (1 << (T + K - 1)) - 1
    del a, b
    c, _, info = m95.encode_rank4(T, K, pilot, 1)
    n_all = len(c.clauses)
    dc = relax_prefix(c, T, info["start"])
    g["prefix_d3_drop"] = dc == (1 << (T + K - 1)) - 1 and len(c.clauses) == n_all - dc
    del c
    e, _, _ = m95.encode_rank4(T, K, pilot, 1)
    over = m95.relax(e, T) - dc
    del e
    with open(os.path.join(out_dir, "m98_selfcheck.json"), "w") as f:
        json.dump({"graded": g, "m95_relax_overdrop_d3": over}, f, indent=1)
    print(f"SUMMARY selfcheck all_match {all(g.values())} {json.dumps(g, sort_keys=True)} "
          f"m95_relax_overdrop_d3 {over}", flush=True)


def run_consistent(cap, minutes, out_dir):
    start = time.time()
    inst = {name: (t, k, Ms) for name, t, k, Ms in m97.instances()}
    rows = []
    for name in CONSISTENT:
        t, k, Ms = inst[name]
        if time.time() - start > minutes * 60:
            rows.append({"name": name, "status": "SKIPPED"})
            continue
        status, sec, dropped, models = m97.solve_models(t, k, Ms, MODELS[max(t, 6)], cap,
                                                        start + minutes * 60)
        sols = [model_solution(As, ss, B, t, k, Ms) for As, ss, B in models]
        row = {"name": name, "t": t, "status": status, "seconds": sec, "dropped": dropped,
               "models": len(models), "solutions": sols}
        rows.append(row)
        print(f"consistent {name}: relax {status} {sec} s models {len(models)} identities_ok "
              f"{sum(s['identities_ok'] for s in sols)} solution_ok "
              f"{sum(s['solution_ok'] for s in sols)} aniso1/aniso2 "
              f"{sum(s.get('check', {}).get('aniso1', False) for s in sols)}/"
              f"{sum(s.get('check', {}).get('aniso2', False) for s in sols)}", flush=True)
    with open(os.path.join(out_dir, "m98_consistent.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print("SUMMARY consistent " + json.dumps(
        {r["name"]: [r["status"], r.get("models"), sum(s["solution_ok"] for s in
                                                       r.get("solutions", []))] for r in rows},
        sort_keys=True), flush=True)


def run_reduced2(out_dir):
    m97.invertible_in = invertible_full     # m97.reduced looks the name up when it runs
    rows = []
    for name, t, k, Ms in m97.instances():
        row = {"name": name}
        start = time.time()
        for level in m97.LEVELS:
            DEADLINE[0] = time.time() + RELAX_SECONDS
            res = m97.reduced(Ms, level)
            if res["status"] == "SAT":
                G = {int(a): v for a, v in res["G"].items()}
                res["witness"] = check_solution(Ms, G, res["S_rows"])
            row[level] = res
        row["seconds"] = round(time.time() - start, 2)
        rows.append(row)
        print(f"reduced2 {name}: " + " ".join(
            f"{lv} {row[lv]['status']}({row[lv]['stage']})" for lv in m97.LEVELS)
            + f" seconds {row['seconds']}", flush=True)
    with open(os.path.join(out_dir, "m98_reduced2.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print("SUMMARY reduced2 " + json.dumps(
        {r["name"]: "".join(CODE[r[lv]["status"]] for lv in m97.LEVELS) for r in rows},
        sort_keys=True), flush=True)


def d3_check(As, ss, B, Ms, f):
    """A relax model with d = 3: (L) and (Q), shape (c), every family of m95 with D = ker f, not
    anisotropic; the identities of Lemma 98 are recorded but not required (L != 0)."""
    t, k = T, K
    d = t + k - 1
    _, sv = sa.tables(As, ss, B, d)
    out = {"coeff_ok": sa.coeff_ok(As, ss, B, t, d), "anisotropic": sa.anisotropic(sv),
           "shape": m97.csh.in_shape(As, ss, B, t, k, "c")}
    out.update(m95.fixed_parts(As, B, t, k, Ms, f))
    out["ok"] = (all(out[x] for x in ("coeff_ok", "shape", "units", "inv", "lin", "a"))
                 and not out["anisotropic"])
    ident = m97.identities(As, ss, B, t, k, Ms)
    out["l98"] = {x: ident[x] for x in ("sigma_N", "T_into_X1", "G_keeps_X1", "lemma98", "r2",
                                        "five", "lemma46a")}
    return out


def run_d3(orbits_file, cap, minutes, out_dir):
    from pysat.solvers import Solver
    start = time.time()
    rows = []
    for sp in d3_specs(orbits_file):
        if time.time() - start > minutes * 60:
            rows.append({"name": sp["name"], "status": "SKIPPED"})
            continue
        Ms = m95.ms_of(sp)
        cnf, names, info = m95.encode_rank4(T, K, Ms, sp["f"])
        dropped = relax_prefix(cnf, T, info["start"])
        s = Solver(name="glucose4", bootstrap_with=cnf.clauses)
        timer = threading.Timer(cap, s.interrupt)
        t0 = time.time()
        timer.start()
        try:
            res = s.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        sec = round(time.time() - t0, 2)
        status = {True: "SAT", False: "UNSAT", None: "UNKNOWN"}[res]
        row = {"name": sp["name"], "orbit": sp["orbit"], "f": sp["f"], "status": status,
               "seconds": sec, "dropped": dropped}
        if status == "SAT":
            As, ss, B = sa.decode(s.get_model(), names, T, T + K - 1)
            row["check"] = d3_check(As, ss, B, Ms, sp["f"])
        s.delete()
        del cnf
        rows.append(row)
        print(f"d3 {sp['name']}: relax {status} {sec} s dropped {dropped}"
              + (f" ok {row['check']['ok']} l98 {json.dumps(row['check']['l98'], sort_keys=True)}"
                 if "check" in row else ""), flush=True)
    with open(os.path.join(out_dir, "m98_d3.json"), "w") as f:
        json.dump(rows, f, indent=1)
    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    print(f"SUMMARY d3 instances {len(rows)} {json.dumps(counts, sort_keys=True)} sat "
          f"{[r['name'] for r in rows if r['status'] == 'SAT'][:40]}", flush=True)


def run_certb(orbits_file, tools, cap, minutes, out_dir):
    start = time.time()
    rows, counts = [], {}
    for sp in d3_specs(orbits_file):
        if time.time() - start > minutes * 60:
            res = dict(sp, status="SKIPPED", wall_seconds=0)
        else:
            with tempfile.TemporaryDirectory() as tmp:
                res = m95.solve_one(sp, cap, out_dir, tmp)
                if res["status"] == "UNSAT":
                    m95.certify(tools, res, tmp)
        for x in ("A", "s", "B"):
            res.pop(x, None)
        rows.append(res)
        key = res["status"] + ("_" + res["cert"] if "cert" in res else "")
        counts[key] = counts.get(key, 0) + 1
        print(m95.line(res), flush=True)
    with open(os.path.join(out_dir, "m98b_rows.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print(f"SUMMARY certb instances {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


# ---------- grading (pre-registered in m98-predictions.md) ----------

def grade_a(out_dir):
    g = {}
    st = m97.load(out_dir, "m98_selfcheck.json") or {"graded": {"selfcheck": False}}
    for key, ok in st["graded"].items():
        g["selfcheck_" + key] = bool(ok)
    cons = {r["name"]: r for r in m97.load(out_dir, "m98_consistent.json") or []}
    for name in CONSISTENT:
        r = cons.get(name, {})
        sols = r.get("solutions", [])
        g["sat_" + name] = r.get("status") == "SAT" and len(sols) > 0
        g["identities_" + name] = bool(sols) and all(s["identities_ok"] for s in sols)
        g["solution_" + name] = bool(sols) and all(s["solution_ok"] for s in sols)
    red = {r["name"]: r for r in m97.load(out_dir, "m98_reduced2.json") or []}
    for name, want in M97_REDUCED.items():
        r = red.get(name)
        for lv, w in zip(m97.LEVELS, want):
            got = CODE[r[lv]["status"]] if r else "-"
            key = f"reduced2_{name}_{lv}"
            # decided everywhere; equal to m97 where m97 decided; SAT where a relax model exists
            g[key] = got in "SU" and (got == w if w != "?" else got == "S")
            if r and r[lv]["status"] == "SAT":
                g[f"witness_{name}_{lv}"] = r[lv]["witness"].get("relax_ok", False)
    d3 = m97.load(out_dir, "m98_d3.json") or []
    g["d3_all"] = len(d3) == 159
    for r in d3:
        if r["status"] in ("SAT", "UNSAT"):
            g["d3_dropped_" + r["name"]] = r["dropped"] == (1 << (T + K - 1)) - 1
        if r["status"] == "SAT":
            g["d3_model_" + r["name"]] = r["check"]["ok"]
    sat = [r for r in d3 if r["status"] == "SAT"]
    out = {"graded": g,
           "d3_counts": {s: sum(r["status"] == s for r in d3) for s in ("SAT", "UNSAT", "UNKNOWN",
                                                                        "SKIPPED")},
           "d3_sat": [r["name"] for r in sat],
           "d3_sat_orbits": sorted({r["orbit"] for r in sat}),
           "d3_l98_all": {x: all(r["check"]["l98"][x] for r in sat) for x in
                          ("sigma_N", "T_into_X1", "G_keeps_X1", "lemma98", "r2", "five",
                           "lemma46a")} if sat else {},
           "d3_max_seconds": max((r["seconds"] for r in d3 if "seconds" in r), default=None),
           "reduced2": {n: "".join(CODE[r[lv]["status"]] for lv in m97.LEVELS)
                        for n, r in red.items()},
           "reduced2_max_seconds": max((r["seconds"] for r in red.values()), default=None)}
    return out


def grade_b(out_dir):
    g = {}
    ctl = m97.load(out_dir, "m95a_controls.json") or {"graded": {"controls": False}}
    g.update(ctl["graded"])
    rows = m97.load(out_dir, "m98b_rows.json") or []
    g["certb_all"] = len(rows) == 159
    for r in rows:
        g["verified_" + r["name"]] = r.get("cert") == "VERIFIED"
    done = [r for r in rows if r.get("cert") == "VERIFIED"]
    out = {"graded": g, "verified": len(done),
           "not_verified": [r["name"] for r in rows if r.get("cert") != "VERIFIED"],
           "cadical_sum": round(sum(r["cadical"]["seconds"] for r in done), 2),
           "drat_sum": round(sum(r["drat"]["seconds"] for r in done), 2),
           "largest_proof": max((r["proof_bytes"] for r in done), default=None),
           "rows": {r["name"]: [r["status"], r.get("seconds"), r.get("cert"),
                                r.get("cnf_sha256")] for r in rows}}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "consistent", "reduced2", "d3", "controls",
                                       "certb", "grade_a", "grade_b"], default="selfcheck")
    ap.add_argument("--orbits", default="m95_orbits.json")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--cap-seconds", type=float, default=60.0)
    ap.add_argument("--minutes", type=float, default=60.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "selfcheck":
        selfcheck(args.orbits, args.out_dir)
    elif args.part == "consistent":
        run_consistent(args.cap_seconds, args.minutes, args.out_dir)
    elif args.part == "reduced2":
        run_reduced2(args.out_dir)
    elif args.part == "d3":
        run_d3(args.orbits, args.cap_seconds, args.minutes, args.out_dir)
    elif args.part == "controls":
        m95.run_controls(args.tools, args.out_dir)
    elif args.part == "certb":
        run_certb(args.orbits, args.tools, args.cap_seconds, args.minutes, args.out_dir)
    else:
        a = args.part == "grade_a"
        out = grade_a(args.out_dir) if a else grade_b(args.out_dir)
        with open(os.path.join(args.out_dir, "m98a_grade.json" if a else "m98b_grade.json"),
                  "w") as f:
            json.dump(out, f, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        if a:
            extra = (f"d3 {json.dumps(out['d3_counts'], sort_keys=True)} d3_sat_orbits "
                     f"{out['d3_sat_orbits']} d3_l98_all {json.dumps(out['d3_l98_all'])} "
                     f"d3_max_s {out['d3_max_seconds']} reduced2_max_s "
                     f"{out['reduced2_max_seconds']} reduced2 "
                     f"{json.dumps(out['reduced2'], sort_keys=True)}")
        else:
            extra = (f"verified {out['verified']} not_verified {out['not_verified'][:8]} "
                     f"cadical_sum {out['cadical_sum']} drat_sum {out['drat_sum']} "
                     f"largest_proof {out['largest_proof']}")
        print(f"SUMMARY {args.part} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {extra}", flush=True)


if __name__ == "__main__":
    main()
