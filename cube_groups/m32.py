# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Jobs m32, m33 and m34: what job m30 (a6_r3m.py, notes/a17.md) left open at t = 6, with longer
budgets, and a positive control at t = 6 that no earlier job had.

Job m30 fixed the matrix A_u up to the stabiliser of (ker A_u, Im A_u) (Lemma 70) and found all
141 classes of ("A", 5) UNSAT, 399 of the 401 classes of ("B", 4) UNSAT (2 UNKNOWN at one
minute), and 17 of the 66 classes of ("B", 5) UNSAT (25 UNKNOWN at one minute, 24 SKIPPED when
the group budget ended). This module re-runs exactly those 51 instances with a6_r3m.py unchanged
(the classes are rebuilt with the same seeds, and every instance's A_u is checked against the
value job m30 used before it runs), in three groups:

    m32: the 2 ("B", 4) instances with 20 minutes each, then the 24 SKIPPED ("B", 5) instances
         with 3 minutes each
    m33: the UNKNOWN ("B", 5) instances of pair orbits 0 to 4 (11) with 12 minutes each
    m34: the UNKNOWN ("B", 5) instances of pair orbits 6 to 8 (14) with 10 minutes each

The controls of jobs m27 to m30 that have a model are all at t = 2, where every matrix A_u with
kernel span(e_0) and image span(e_1) is symmetric. The positive control here is at t = 6: the
direct sum of three copies of the system of Lemma 63 (ii) (sigma(a) = sigma(b) = e,
sigma(a + b) = f, A_a = A_b = the projection onto span(f) along span(e), A_(a+b) = 0) is an
anisotropic system with t = dim V = 6 in which u = a_1 + a_2 + a_3 has rank 3 in shape ("B", 3).
Written in the normal form of Lemma 67, it is a model of the instance (t, d) = (6, 6), ("B", 3),
X_1 = ker A_u, R = Im A_u, A_u fixed, facts of Lemma 69 included, so that instance must be SAT;
"skew" takes e_4 = E_2 + F_1 instead of E_2, which makes A_u non-symmetric, and its transpose
must be UNSAT (its kernel is not X_1).

Parts: control6 (needs python-sat), leftovers --group m32|m33|m34 (needs python-sat), grade.
"""
import argparse
import json
import os
import time

import a6_r3 as r3
import a6_r3h as h
import a6_r3m as m
import sat_aniso as sa

T = 6
RHO = 3

# What job m30 left open (compete-results/m30-a6r3m-v1/out): instance name -> the A_u it used.
B4_LEFT = {"r3m_t6_r3_B4_o001_m000": 4294967824, "r3m_t6_r3_B4_o026_m008": 3260700}
B5_SKIPPED = {
    "r3m_t6_r3_B5_o005_m005": 142606352, "r3m_t6_r3_B5_o005_m006": 144703504,
    "r3m_t6_r3_B5_o005_m007": 144703512, "r3m_t6_r3_B5_o005_m008": 270532640,
    "r3m_t6_r3_B5_o005_m009": 270532648, "r3m_t6_r3_B5_o007_m005": 142607376,
    "r3m_t6_r3_B5_o007_m006": 144704528, "r3m_t6_r3_B5_o007_m007": 144705048,
    "r3m_t6_r3_B5_o007_m008": 270534688, "r3m_t6_r3_B5_o007_m009": 270535208,
    "r3m_t6_r3_B5_o008_m005": 276824608, "r3m_t6_r3_B5_o008_m006": 281018928,
    "r3m_t6_r3_B5_o008_m007": 404752392, "r3m_t6_r3_B5_o008_m008": 417333816,
    "r3m_t6_r3_B5_o009_m004": 9007267840, "r3m_t6_r3_B5_o009_m005": 34630270976,
    "r3m_t6_r3_B5_o010_m004": 9000976416, "r3m_t6_r3_B5_o010_m005": 9005170736,
    "r3m_t6_r3_B5_o010_m006": 9007267896, "r3m_t6_r3_B5_o010_m007": 17718837256,
    "r3m_t6_r3_B5_o010_m008": 17853054984, "r3m_t6_r3_B5_o010_m009": 17987272712,
    "r3m_t6_r3_B5_o010_m010": 34630270984, "r3m_t6_r3_B5_o010_m011": 34764488712}
B5_UNKNOWN = {
    "r3m_t6_r3_B5_o000_m000": 33824, "r3m_t6_r3_B5_o001_m000": 2098208,
    "r3m_t6_r3_B5_o001_m001": 2098216, "r3m_t6_r3_B5_o001_m003": 4194856,
    "r3m_t6_r3_B5_o002_m000": 2164736, "r3m_t6_r3_B5_o002_m001": 4229120,
    "r3m_t6_r3_B5_o003_m000": 2164768, "r3m_t6_r3_B5_o003_m001": 2165288,
    "r3m_t6_r3_B5_o003_m003": 4229672, "r3m_t6_r3_B5_o004_m000": 2164744,
    "r3m_t6_r3_B5_o004_m001": 4229136, "r3m_t6_r3_B5_o006_m000": 138414080,
    "r3m_t6_r3_B5_o006_m001": 140511232, "r3m_t6_r3_B5_o006_m002": 142607360,
    "r3m_t6_r3_B5_o006_m003": 144704512, "r3m_t6_r3_B5_o006_m004": 270534656,
    "r3m_t6_r3_B5_o007_m000": 138414112, "r3m_t6_r3_B5_o007_m001": 138414632,
    "r3m_t6_r3_B5_o007_m002": 138415672, "r3m_t6_r3_B5_o007_m003": 140511264,
    "r3m_t6_r3_B5_o007_m004": 140511784, "r3m_t6_r3_B5_o008_m000": 138414096,
    "r3m_t6_r3_B5_o008_m001": 140511256, "r3m_t6_r3_B5_o008_m003": 144704552,
    "r3m_t6_r3_B5_o008_m004": 270534664}
EXPECTED_AU = dict(B4_LEFT, **B5_SKIPPED, **B5_UNKNOWN)


def orbit_of(name):
    return int(name.split("_o")[1][:3])


# (instance name, minutes) in the order they run.
GROUPS = {
    "m32": [(n, 20) for n in sorted(B4_LEFT)] + [(n, 3) for n in sorted(B5_SKIPPED)],
    "m33": [(n, 12) for n in sorted(B5_UNKNOWN) if orbit_of(n) <= 4],
    "m34": [(n, 10) for n in sorted(B5_UNKNOWN) if orbit_of(n) >= 6]}


# ---------- the positive control at t = 6 ----------

# Hand values: A_u = diag(0, 1, 1, 1, 0, 0) is bits 7, 14, 21 (entry (row, col) at bit 6 row + col);
# the skew one adds (1, 4), bit 10. X_1 in rref: span(e_0, e_4, e_5) and span(e_0, e_1 + e_4, e_5).
HAND_CONTROL = {False: {"au": 2113664, "x1": (32, 16, 1), "r": (8, 4, 2)},
                True: {"au": 2114688, "x1": (32, 18, 1), "r": (8, 4, 2)}}


def sigma_old(v):
    """Three copies of Lemma 63 (ii) side by side. X: E_i = bit 2i, F_i = bit 2i + 1; V: a_i = bit 2i,
    b_i = bit 2i + 1; sigma(a_i) = sigma(b_i) = E_i, sigma(a_i + b_i) = F_i, no cross terms."""
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
            out ^= sa.entries(T, [(2 * i + 1, 2 * i + 1)])
    return out


def direct_sum_control(skew=False):
    """The direct sum in the normal form of Lemma 67 for u = a_1 + a_2 + a_3, shape ("B", 3):
    e_0 = E_1 + E_2 + E_3, e_1, e_2, e_3 = F_1, F_2, F_3, e_4 = E_2 (or E_2 + F_1), e_5 = E_3;
    h_0 = u, h_1 = a_1, h_2 = a_2 (phi = 0), h_3, h_4, h_5 = b_1, b_2, b_3 (phi = e_1, e_2, e_3).
    Returns (As, ss, B, x1, r, au)."""
    nb = sa.from_cols([21, 2, 8, 32, 6 if skew else 4, 16], T)     # new coordinates -> old
    c = sa.mat_inv(nb, T)
    hs = [21, 1, 4, 2, 8, 32]
    As = [sa.mat_mul(sa.mat_mul(c, alpha_old(v), T), nb, T) for v in hs]
    ss = [sa.mat_apply(c, sigma_old(v), T) for v in hs]
    B = {(i, k): sa.mat_apply(c, sigma_old(hs[i] ^ hs[k]) ^ sigma_old(hs[i]) ^ sigma_old(hs[k]), T)
         for i in range(T) for k in range(i + 1, T)}
    x1 = m.ker_of(As[0], T)
    r = m.im_of(As[0], T)
    return As, ss, B, x1, r, As[0]


def transpose(A, t):
    return sum(((A >> (t * row + col)) & 1) << (t * col + row) for row in range(t) for col in range(t))


def control_checks(skew):
    """Brute-force checks of the construction, before any solver runs."""
    As, ss, B, x1, r, au = direct_sum_control(skew)
    at, sv = sa.tables(As, ss, B, T)
    plain, alts = h.facts(T, T, "B", 3, RHO, x1, r)
    hand = HAND_CONTROL[skew]
    return {"system": sa.is_system(at, sv, T, T), "anisotropic": sa.anisotropic(sv),
            "normal_form": r3.in_normal_form(As, ss, B, T, T, "B", 3, x1, r),
            "facts_hold": h.facts_hold(plain, alts, As, T),
            "rank_3": sa.rank_f2(sa.rows_of(au, T)) == 3,
            "shape_B3": not r3.in_span(r3.rref([2, 4, 8]), ss[0]) and ss[0] == 1,
            "hand_au": au == hand["au"], "hand_x1": tuple(x1) == hand["x1"],
            "hand_r": tuple(r) == hand["r"],
            "symmetric": au == transpose(au, T)}


def control_specs():
    out = []
    for skew in (False, True):
        As, ss, B, x1, r, au = direct_sum_control(skew)
        base = {"t": T, "d": T, "rho": RHO, "shape": "B", "p": 3, "x1": list(x1), "r": list(r),
                "size": 0, "orbit": -1, "cls": -1, "class_size": 0}
        tag = "skew" if skew else "diag"
        out.append(dict(base, au=au, name=f"ctl6_{tag}", expect="SAT"))
        if skew:
            out.append(dict(base, au=transpose(au, T), name="ctl6_skew_transposed", expect="UNSAT"))
    return out


# ---------- runs ----------

def run_controls(budget_seconds, group_seconds, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    checks = {"diag": control_checks(False), "skew": control_checks(True)}
    with open(os.path.join(out_dir, "control6_checks.json"), "w") as f:
        json.dump(checks, f, indent=1)
    print(f"control6 checks: {json.dumps(checks, sort_keys=True)}", flush=True)
    start = time.time()
    for sp in control_specs():
        left = group_seconds - (time.time() - start)
        if left < 1:
            break
        m.solve_one(sp, "auto", min(budget_seconds, left), out_dir)


def run_leftovers(group, group_seconds, out_dir):
    """The group's instances, each with its own budget; an instance whose rebuilt A_u differs from
    job m30's is not run (status MISMATCH)."""
    os.makedirs(out_dir, exist_ok=True)
    by_name = {}
    for s, p in (("B", 4), ("B", 5)):
        if any(n.startswith(f"r3m_t6_r3_{s}{p}_") for n, _ in GROUPS[group]):
            for sp in m.specs(T, T + 1, RHO, s, p, out_dir):
                by_name[sp["name"]] = sp
    start = time.time()
    counts = {}
    for name, minutes in GROUPS[group]:
        sp = by_name.get(name)
        left = group_seconds - (time.time() - start)
        if sp is None or sp["au"] != EXPECTED_AU[name]:
            res = {"name": name, "status": "MISMATCH", "au": sp["au"] if sp else None}
            with open(os.path.join(out_dir, name + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        elif left < 1:
            res = dict(sp, status="SKIPPED")
            with open(os.path.join(out_dir, name + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = m.solve_one(sp, "auto", min(minutes * 60, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    print(f"SUMMARY leftovers {group} instances {len(GROUPS[group])} "
          f"{json.dumps(counts, sort_keys=True)}", flush=True)
    return counts


def grade(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if (fn.startswith(("r3m_", "ctl6_")) and fn.endswith(".json")
                and not fn.endswith((".child.json", ".spec.json"))):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    graded = {}
    try:
        with open(os.path.join(out_dir, "control6_checks.json")) as f:
            graded["control6_checks"] = all(v for c in json.load(f).values()
                                            for k, v in c.items() if k != "symmetric")
    except (OSError, ValueError):
        pass
    for name, r in results.items():
        if name.startswith("ctl6_"):
            graded[name] = r.get("status") == r["expect"]
            if r["status"] == "SAT":
                for k in ("verified", "facts_hold", "au_matches"):
                    graded[f"{name}_{k}"] = bool(r.get(k))
        elif name.startswith("r3m_"):
            graded[name + "_au_as_m30"] = r.get("status") != "MISMATCH"
            if r.get("status") == "SAT":
                for k in ("verified", "facts_hold", "au_matches"):
                    graded[f"{name}_{k}"] = bool(r.get(k))
    status = {n: r.get("status") for n, r in results.items()}
    counts = {}
    for n, s in status.items():
        key = n[:12] if n.startswith("r3m_") else "ctl6"
        counts.setdefault(key, {})
        counts[key][s] = counts[key].get(s, 0) + 1
    return {"graded": graded, "status": status, "counts": counts,
            "times": {n: r.get("wall_seconds") for n, r in results.items()},
            "any_sat_6": any(s == "SAT" for n, s in status.items() if n.startswith("r3m_"))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["control6", "leftovers", "grade"], default="grade")
    ap.add_argument("--group", choices=sorted(GROUPS), default="m32")
    ap.add_argument("--budget-minutes", type=float, default=8.0)
    ap.add_argument("--group-minutes", type=float, default=24.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    if args.part == "control6":
        run_controls(args.budget_minutes * 60, args.group_minutes * 60, args.out_dir)
    elif args.part == "leftovers":
        run_leftovers(args.group, args.group_minutes * 60, args.out_dir)
    else:
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} graded {len(out['graded'])} "
              f"any_sat_6 {out['any_sat_6']} {json.dumps(out['counts'], sort_keys=True)}",
              flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
