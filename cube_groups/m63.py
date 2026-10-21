# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m63: Lemma 93 (notes/a52.md) on the split instances of (B5) at t = 7 and dim V = 9 whose
second matrix A_(h_1) has rank 0 on X_1.

Lemma 93 (a): h_1 may be chosen in N = ker phi outside span(u) with the largest rank on X_1, since
that rank is kept by the stabiliser G of (x0, P, A_u) and by h_1 -> h_1 + u. So in an instance
whose representative A_(h_1) has rank r on X_1, every A_n with n in N has rank at most r on X_1.
(b) For r = 0 that is linear: A_(v_i) vanishes on X_1 for every i < kd, which adds t (dim X_1 - 1)
unit clauses for each of v_2, ..., v_(kd-1) (the column at x0 is 0 already by m42's hints). With
(L) of sat_aniso.py and m42's hints it also gives beta(v_i, v_j) = 0 for 1 <= i < j < kd, but that
follows by unit propagation, so no clause is added for it.

The instances are m62's (m60.py's split_spec, m57.py's encoding, hints and unit clauses for
A_(v_1)), imported unchanged, with only the clauses of (b) added, and named r3l_ instead of r3s_.
m63 imports m62, which points m60.py's lists at m62's, so the check is m60's check of m62's group
(m57's own check, m55's classes and counts, the 14 re-opened instances recomputed), plus m63's own.

Group a (job m63a): the rank-0 instances of m62a's re-opened list (o032_c000's a014, a023, a053,
  a083; o000_c000's a031, a098), then TAIL_PLAIN["a"], then TAIL_OPEN["a"].
Group b (job m63b): the 7 of m62b's list (all of o000_c000, rank 0), then TAIL_PLAIN["b"], then
  TAIL_OPEN["b"].
TAIL_OPEN is the rank-0 instances of r3b_t7_B5_o000_c001 (a) and o000_c002 (b) that m62 left open at
its 15 to 20 s CaDiCaL budgets, run with Lemma 93. TAIL_PLAIN is the ones of rank 1 or 2 that m62
left open at 10 to 16 s; Lemma 93 (b) says nothing linear for them, so they run as m62's instances,
unchanged (m60's rule for a split with 1 to 30 open).
Each: CaDiCaL for at most CAP seconds, then, if still open, CryptoMiniSat with native XOR for CAP.

Parts:
    check   m60's graded check of m62's group; m63's: every Lemma 93 entry has rank 0 on X_1 and is
            one of m55's representatives (index, rank and A_(h_1) as recorded), every plain entry
            is one of m55's representatives with its recorded rank, 1 or 2; on the first entry, in
            both arms, the Lemma 93 instance is m62's instance plus exactly
            t (dim X_1 - 1) (kd - 2) negative unit clauses on A_(v_2), ..., A_(v_(kd-1)),
            consistent with the other units.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; status and time of every instance in each arm;
            whether the tail class is now empty (m62's UNSAT plus this group's).

Usage: python m63.py --part check|solve|grade|child [--group a|b] [--group-minutes 150]
                     [--out-dir DIR]
"""
import argparse
import json
import os
import subprocess
import sys
import time

import m62
import m60
import m57 as m

T = 7
CAP = 300.0
C1, C2 = m62.C1, m62.C2
# Tail instances that m62 left open, rank 0 on X_1: (class, m55 order k, m55 index, 0, A_(h_1)),
# copied from m62a's and m62b's out/r3s_t7_B5_o000_c00?_aKKK__cadical.json (2026-10-21).
TAIL_OPEN = {
    "a": ((C1, 74, 512, 0, 262144), (C1, 137, 1024, 0, 2048), (C1, 165, 2560, 0, 262160),
          (C1, 311, 6656, 0, 786448), (C1, 318, 8192, 0, 4096), (C1, 348, 10752, 0, 266256),
          (C1, 402, 20992, 0, 786464), (C1, 429, 65536, 0, 8192), (C1, 488, 66560, 0, 10240),
          (C1, 573, 73728, 0, 12288), (C1, 587, 75264, 0, 276480), (C1, 592, 75776, 0, 12304),
          (C1, 593, 76288, 0, 274448), (C1, 643, 131072, 0, 1048576),
          (C1, 664, 131584, 0, 1310720), (C1, 676, 132096, 0, 1050624),
          (C1, 755, 139264, 0, 1052672), (C1, 757, 140288, 0, 1054720),
          (C1, 758, 140800, 0, 1316864), (C1, 760, 141824, 0, 1314832),
          (C1, 777, 145408, 0, 1576976), (C1, 821, 159744, 0, 1576992),
          (C1, 887, 264704, 0, 134479888), (C1, 933, 270336, 0, 134221824)),
    "b": ((C2, 74, 512, 0, 262144), (C2, 233, 2560, 0, 262160), (C2, 248, 4096, 0, 524288),
          (C2, 278, 4608, 0, 786432), (C2, 382, 8192, 0, 4096), (C2, 420, 8704, 0, 266240),
          (C2, 529, 16384, 0, 32), (C2, 533, 16896, 0, 262176), (C2, 539, 18432, 0, 48),
          (C2, 559, 20480, 0, 524320), (C2, 582, 25088, 0, 266272), (C2, 696, 41472, 0, 266304),
          (C2, 732, 49152, 0, 96), (C2, 736, 49664, 0, 262240), (C2, 773, 131072, 0, 1048576),
          (C2, 827, 184320, 0, 1572960), (C2, 953, 295424, 0, 134479936),
          (C2, 1119, 557056, 0, 17179869248), (C2, 1123, 557568, 0, 17180131392),
          (C2, 1656, 3145728, 0, 283673999966208)),
}
# Tail instances that m62 left open, rank 1 or 2 on X_1, from the same files.
TAIL_PLAIN = {
    "a": ((C1, 1229, 547331, 1, 17180688688), (C1, 1788, 3166376, 2, 283674000557092),
          (C1, 1793, 3168264, 1, 283674000556080)),
    "b": ((C2, 478, 10249, 1, 102416), (C2, 616, 32848, 2, 131648), (C2, 674, 37568, 1, 918592),
          (C2, 1325, 1572897, 2, 2216203157508), (C2, 1492, 2097165, 2, 281474976808962)),
}
# m62's tail totals (m62a/m62b grade.json "tail"): (instances, UNSAT).
M62_TAIL = {C1: (1798, 1771), C2: (1827, 1802)}

_base_build_plain = m.build_plain


def entries(group):
    """m62's re-opened instances of rank 0 on X_1, then TAIL_OPEN, in order."""
    return [row for row in m62.REOPEN[group] if row[3] == 0] + list(TAIL_OPEN[group])


def x1_cols(spec):
    """The columns at X_1's basis vectors other than x0 = e_0."""
    return [v.bit_length() - 1 for v in spec["x1"] if v != 1]


def lemma93_units(spec):
    return T * len(x1_cols(spec)) * (spec["d"] - spec["p"] - 2)


def add_lemma93(cnf, names, spec):
    """Lemma 93 (b): A_(v_i) = 0 on X_1 for 2 <= i < kd. Returns the number of clauses added."""
    A = names[0]
    n = 0
    for i in range(2, spec["d"] - spec["p"]):
        for r in range(spec["t"]):
            for c in x1_cols(spec):
                cnf.clauses.append([-A[i][r][c]])
                n += 1
    return n


def build_plain93(spec):
    cnf, names, hints, units = _base_build_plain(spec)
    if spec.get("lemma93"):
        units += add_lemma93(cnf, names, spec)
    return cnf, names, hints, units


def install():
    """m57.build (and so m57.child) builds with the clauses of Lemma 93 (b) when a spec asks."""
    m62.install()
    m.build_plain = build_plain93


install()


def spec93(name, k, rep):
    sp = m60.split_spec(name, k, rep)
    sp["name"] = sp["name"].replace("r3s_", "r3l_", 1)
    sp["lemma93"] = True
    return sp


def plan(group, reps):
    """[(spec, arm, cap seconds, condition)]; "open" runs the entry only if still undecided.
    m62's re-opened rank-0 instances first (the control), then TAIL_PLAIN, then TAIL_OPEN."""
    controls = [row for row in m62.REOPEN[group] if row[3] == 0]
    specs = [spec93(name, k, reps[name][k]) for name, k, *_ in controls]
    specs += [m60.split_spec(name, k, reps[name][k]) for name, k, *_ in TAIL_PLAIN[group]]
    specs += [spec93(name, k, reps[name][k]) for name, k, *_ in TAIL_OPEN[group]]
    out = []
    for sp in specs:
        out += [(sp, "cadical", CAP, None), (dict(sp), "xor", CAP, "open")]
    return out


def rows_match(reps, rows):
    return all(name in reps and k < len(reps[name]) and reps[name][k]["index"] == idx
               and reps[name][k]["rank_x1"] == rk and reps[name][k]["a1"] == a1
               and m60.rank_on(a1, m60.m55.CLASSES[name][1]) == rk
               for name, k, idx, rk, a1 in rows)


# ---------- check ----------

def check(group, out_dir):
    st = m60.check(group, out_dir)
    graded = st["graded"]
    reps = m60.load_reps(out_dir)
    rows = entries(group)
    graded["m63_entries"] = (len(rows) > 0 and all(rk == 0 for _, _, _, rk, _ in rows)
                             and rows_match(reps, rows))
    graded["m63_plain"] = (all(rk in (1, 2) for _, _, _, rk, _ in TAIL_PLAIN[group])
                           and rows_match(reps, TAIL_PLAIN[group]))
    tail = m62.TAIL[group]
    graded["m63_tail_counts"] = (
        all(r[0] == tail for r in TAIL_OPEN[group] + TAIL_PLAIN[group])
        and len(TAIL_OPEN[group]) + len(TAIL_PLAIN[group]) == M62_TAIL[tail][0] - M62_TAIL[tail][1])
    name, k = rows[0][:2]
    probes = {}
    for arm in ("cadical", "xor"):
        base = m60.split_spec(name, k, reps[name][k])
        sp = spec93(name, k, reps[name][k])
        c0, _, h0, u0 = m.build(base, arm)
        c1, names, h1, u1 = m.build(sp, arm)
        extra = c1.clauses[len(c0.clauses):]
        a_vars = {names[0][i][r][c] for i in range(2, sp["d"] - sp["p"]) for r in range(T)
                  for c in x1_cols(sp)}
        probes[arm] = [c1.nv, len(c1.clauses), h1, u1, len(extra)]
        graded["m63_probe_" + arm] = (
            c1.nv == c0.nv and c1.clauses[:len(c0.clauses)] == c0.clauses
            and len(extra) == lemma93_units(sp) == u1 - u0 and h1 == h0 == m.HAND_HINTS["B5"]
            and all(len(cl) == 1 and cl[0] < 0 and -cl[0] in a_vars for cl in extra)
            and len({-cl[0] for cl in extra}) == len(extra) and m.units_consistent(c1)
            and len(getattr(c1, "xors", ())) == len(getattr(c0, "xors", ())))
    st["m63_probes"] = probes
    st["m63_entries"] = [[n, kk] for n, kk, *_ in rows]
    st["m63_plain"] = [[n, kk] for n, kk, *_ in TAIL_PLAIN[group]]
    return st


# ---------- solving ----------

def solve_one(spec, arm, budget, out_dir):
    """m57.solve_one with this file as the child, so that the child builds with Lemma 93."""
    tag = m.tag_of(spec, arm)
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
        m.verify(spec, res)
    with open(os.path.join(out_dir, tag + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {tag}: {res['status']} {res['wall_seconds']} s", flush=True)
    return res


def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    counts, decided = {}, set()
    for spec, arm, cap, cond in plan(group, m60.load_reps(out_dir)):
        if cond == "open" and spec["name"] in decided:
            continue
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(spec, arm, min(cap, left), out_dir)
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m63-predictions.md) ----------

def grade(group, out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
        reps = m60.load_reps(out_dir)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
        return {"group": group, "graded": graded, "ungraded": ungraded, "rows": {},
                "any_sat_7": False}
    rows = {}
    for spec, arm, _, _ in plan(group, reps):
        path = os.path.join(out_dir, m.tag_of(spec, arm) + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows.setdefault(spec["name"], {})[arm] = [s, r.get("wall_seconds"), r.get("budget_seconds")]
        if s == "SAT":
            tag = m.tag_of(spec, arm)
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
    status = {n: ("UNSAT" if any(v[0] == "UNSAT" for v in a.values())
                  else "SAT" if any(v[0] == "SAT" for v in a.values()) else "open")
              for n, a in rows.items()}
    tail = m62.TAIL[group]
    tail_names = ([spec93(n, k, reps[n][k])["name"] for n, k, *_ in TAIL_OPEN[group]]
                  + [m60.split_spec(n, k, reps[n][k])["name"] for n, k, *_ in TAIL_PLAIN[group]])
    total, before = M62_TAIL[tail]
    here = sum(status.get(n) == "UNSAT" for n in tail_names)
    return {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows,
            "status": status, "unsat": sorted(n for n, s in status.items() if s == "UNSAT"),
            "open": sorted(n for n, s in status.items() if s == "open"),
            "tail": {"name": tail, "total": total, "unsat": before + here,
                     "open": [n for n in tail_names if status.get(n) != "UNSAT"],
                     "empty": before + here == total},
            "any_sat_7": any(s == "SAT" for s in status.values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade", "child"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--arm")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    install()
    if args.part == "child":
        m.child(json.loads(args.spec), args.arm, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade group {args.group} all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} unsat {len(out.get('unsat', []))} "
              f"open {out.get('open')} tail {json.dumps(out.get('tail'))}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.group, args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
