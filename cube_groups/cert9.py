# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job cert9: DRAT proof certificates for the 42 split instances of (B6) that job m82 re-ran, the
ones that closed the classes o008_c000, o008_c001 and o008_c003 (Corollaries 99 to 101;
notes/a69.md) (cube_groups/cert9-predictions.md; notes/a86.md).

What came back on 2026-10-23: jobs cert7 and cert8 certified the 77 instances of jobs m85 and m83
(all VERIFIED by drat-trim, notes/a86.md). m82's 42 are the 5-minute re-runs of the instances that
m79a and m79b left open: UNSAT in CaDiCaL (through python-sat) in 1.17 to 89.20 s each (m82a and
m82b), every one in the CaDiCaL arm, saved without certificates. This job rebuilds each with the
very same code, solves it with a standalone CaDiCaL that writes a DRAT proof, and checks the proof
with drat-trim.

Group a (job cert9a): m82's group a, the 21 of r3b_t7_B6_o008_c000 (a0619 and a0658 of rank 1,
  the rest of rank 0, with Lemma 93 (b)).
Group b (job cert9b): m82's group b, the 7 of r3b_t7_B6_o008_c001 and the 14 of
  r3b_t7_B6_o008_c003 (all of rank 0).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

This file is cert8.py with m82's rows in place of m83's. m82.py keeps the re-runs in OPEN_M79, the
counts of m79's split in M79 and the rank-1 count per group in NAMED_RANK1 (m83.py: OPEN_PREV,
BEFORE, NAMED_RANKS), so groups_ok and specs_ok read those. Everything else is cert1.py's, imported
unchanged: the two programs (built by cert1_tools.py), the controls, and one instance's certificate
(certify_one). The instances, the class gates, the roots (recomputed as m82's check did, with its
seed, in its order) and the rows are m82.py's, imported unchanged; m69.py's split_spec builds each
instance. Group a has instances of rank 1, so it has an "s" probe, as cert8's group b.

Parts:
    check    cert1's 10 graded checks, then the group: each of its classes against m66's run (m82's
             gate) and its roots recomputed; its instances, once each, equal to m82's rows (name,
             m66 index, orbit size, A_(v_1), rank), Lemma 93 (b) on every one of rank 0; the
             variable, clause, hint and unit counts of the first instance of each kind equal to
             m82's own check. Writes cert9_specs.json and check.json.
    certify  each instance of the group in m82's order, as cert1 does; the proof is deleted after
             it is checked.
    grade    counts and times, by class; which instances are not VERIFIED.

Usage: python cert9.py --part check|certify|grade --group a|b [--tools tools] [--minutes 120]
       [--out-dir DIR]
"""
import argparse
import json
import os
import random
import statistics
import tempfile
import time

import cert1 as c1
import m82

b, m = c1.b, c1.m
GROUPS = ("a", "b")
# m82's own check (compete-results/m82a-b6rerun-v1 and m82b-b6rerun-v1, check.json probes
# named_l_cadical and named_s_cadical, 2026-10-21): [vars, clauses, hints, units] of the first
# instance of rank 0 ("l") and of the first of rank 1 ("s", group a only: a0619), CaDiCaL arm.
M82_PROBES = {"a": {"l": [48587, 286225, 79, 70], "s": [48587, 286204, 79, 49]},
              "b": {"l": [48587, 286225, 79, 70]}}
SPECS_FILE = "cert9_specs.json"


def rows(group):
    """m82's rows of the group: (class, k, rank on X_1, m66 index, orbit size, A_(v_1))."""
    return m82.named_rows(group)


def classes(group):
    """The group's classes in the order m82's check recomputed their roots."""
    return list(m82.NAMED_CLASSES[group])


def per_class(group):
    """Re-runs per class of the group: the instances m79a and m79b left open."""
    return {n: m82.M79[n][0] - m82.M79[n][1] for n in classes(group)}


def group_specs(group, reps):
    """m82's re-runs as they ran: m69's split instance at each root, with Lemma 93 (b) when of
    rank 0."""
    return m82.named_specs(group, reps)


def groups_ok():
    """The two groups are m82's, with its 21 and 21 rows over its three classes, once each."""
    every = [row for g in GROUPS for row in rows(g)]
    return (len(every) == len(m82.OPEN_M79) == 42
            and len({(r[0], r[1]) for r in every}) == len(every)
            and sorted(n for g in GROUPS for n in classes(g)) == sorted(m82.NAMED_GATE)
            == sorted(m82.M79)
            and [len(rows(g)) for g in GROUPS] == [m82.NAMED_COUNT[g] for g in GROUPS] == [21, 21]
            and all(r[2] in (0, 1) for r in every)
            and [sum(r[2] == 1 for r in rows(g)) for g in GROUPS]
            == [m82.NAMED_RANK1[g] for g in GROUPS] == [2, 0]
            and [sum(per_class(g).values()) for g in GROUPS] == [21, 21])


def specs_ok(group, specs):
    rs = rows(group)
    per = {}
    for sp in specs:
        per[sp["parent"]] = per.get(sp["parent"], 0) + 1
    return (len(specs) == len(rs) == m82.NAMED_COUNT[group]
            and len({sp["name"] for sp in specs}) == len(specs)
            and per == per_class(group)
            and sum(sp["rank_x1"] == 1 for sp in specs) == m82.NAMED_RANK1[group]
            and all(sp["parent"] == name and sp["name"] == m82.named_name(name, k, rk)
                    and sp["m66_index"] == index and sp["size"] == size and sp["a1"] == a1
                    and sp["rank_x1"] == rk and bool(sp.get("lemma93")) == (rk == 0)
                    for sp, (name, k, rk, index, size, a1) in zip(specs, rs)))


def probe(sp):
    c, _, h, u = m.build(dict(sp), "cadical")
    return [c.nv, len(c.clauses), h, u], m.units_consistent(c)


# ---------- parts ----------

def check(tools, group, out_dir):
    start = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        st = c1.check(tools, tmp)
    graded, probes = dict(st["graded"]), dict(st["probes"])
    rng = random.Random(82)
    reps = {}
    for name in classes(group):
        gate = m82.NAMED_GATE[name]
        r, rr = b.class_reps(name, rng)
        graded["class_" + name[10:]] = m82.class_ok(r, gate)
        graded["class_reps_" + name[10:]] = m82.reps_ok(name, rr, gate)
        reps[name] = rr
    graded["groups"] = groups_ok()
    specs = group_specs(group, reps)
    graded["group"] = specs_ok(group, specs)
    for tag, want in M82_PROBES[group].items():
        sp = next(x for x in specs if bool(x.get("lemma93")) == (tag == "l"))
        got, consistent = probe(sp)
        probes["m82_" + tag] = [sp["name"]] + got
        graded["m82_probe_" + tag] = got == want and consistent
    with open(os.path.join(out_dir, SPECS_FILE), "w") as f:
        json.dump(specs, f)
    out = {"group": group, "classes": classes(group), "graded": graded, "probes": probes,
           "instances": len(specs),
           "ranks": {str(k): sum(sp["rank_x1"] == k for sp in specs) for k in (0, 1, 2)},
           "seconds": round(time.time() - start, 1)}
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(out, f, indent=1)
    return out


def certify(tools, minutes, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing certified")
    with open(os.path.join(out_dir, SPECS_FILE)) as f:
        specs = json.load(f)
    counts = {}
    with tempfile.TemporaryDirectory() as tmp:
        for sp in specs:
            if time.time() - start > minutes * 60:
                out = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "SKIPPED"}
            else:
                out = c1.certify_one(tools, sp, tmp)
            with open(os.path.join(out_dir, f"cert9_{sp['name']}.json"), "w") as f:
                json.dump(out, f, indent=1)
            counts[out["status"]] = counts.get(out["status"], 0) + 1
            print(f"certify {sp['name']}: {out['status']} cadical "
                  f"{out.get('cadical', {}).get('seconds')} s drat "
                  f"{(out.get('drat') or {}).get('seconds')} s proof {out.get('proof_bytes')} B",
                  flush=True)
    print(f"SUMMARY certify {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def grade(group, out_dir):
    with open(os.path.join(out_dir, "check.json")) as f:
        graded = json.load(f)["graded"]
    with open(os.path.join(out_dir, SPECS_FILE)) as f:
        specs = json.load(f)
    rs = []
    for sp in specs:
        p = os.path.join(out_dir, f"cert9_{sp['name']}.json")
        r = (json.load(open(p)) if os.path.exists(p) else
             {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "MISSING"})
        rs.append(dict(r, parent=sp["parent"]))
    done = [r for r in rs if r["status"] == "VERIFIED"]
    cad = [r["cadical"]["seconds"] for r in done]
    drt = [r["drat"]["seconds"] for r in done]
    big = max(done, key=lambda r: r["proof_bytes"], default=None)
    slow = max(done, key=lambda r: r["cadical"]["seconds"], default=None)
    counts = {}
    for r in rs:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    by_class = {name: {"instances": sum(r["parent"] == name for r in rs),
                       "verified": sum(r["parent"] == name for r in done)}
                for name in classes(group)}
    tj = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tools", "tools.json")
    return {"classes": classes(group), "group": group, "graded": graded, "instances": len(specs),
            "tools": json.load(open(tj)) if os.path.exists(tj) else None,
            "counts": counts, "verified": len(done), "by_class": by_class,
            "not_verified": [r["name"] for r in rs if r["status"] != "VERIFIED"],
            "any_sat": any(r["status"] == "SAT" for r in rs),
            "cadical_sum": round(sum(cad), 2), "drat_sum": round(sum(drt), 2),
            "cadical_median": statistics.median(cad) if cad else None,
            "drat_median": statistics.median(drt) if drt else None,
            "cadical_max": max(cad, default=None), "drat_max": max(drt, default=None),
            "largest_proof": [big["name"], big["proof_bytes"]] if big else None,
            "slowest": ([slow["name"], slow["cadical"]["seconds"], slow["drat"]["seconds"]]
                        if slow else None),
            "rows": {r["name"]: [r["status"], r.get("cadical", {}).get("seconds"),
                                 (r.get("drat") or {}).get("seconds"), r.get("proof_bytes"),
                                 r.get("cnf_sha256")]
                     for r in rs}}


def summary_line(out):
    by_class = {n[10:]: c for n, c in out["by_class"].items()}
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} graded "
            f"{len(out['graded'])} instances {out['instances']} verified {out['verified']} "
            f"by_class {json.dumps(by_class, sort_keys=True)} "
            f"counts {json.dumps(out['counts'], sort_keys=True)} any_sat {out['any_sat']} "
            f"not_verified {out['not_verified'][:10]} cadical_sum {out['cadical_sum']} drat_sum "
            f"{out['drat_sum']} cadical_median {out['cadical_median']} cadical_max "
            f"{out['cadical_max']} drat_max {out['drat_max']} largest_proof "
            f"{out['largest_proof']} slowest {out['slowest']}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "certify", "grade"], default="check")
    ap.add_argument("--group", choices=GROUPS, default="a")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--minutes", type=float, default=120.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "certify":
        certify(args.tools, args.minutes, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(summary_line(out), flush=True)
    else:
        st = check(args.tools, args.group, args.out_dir)
        print(f"check: {json.dumps({k: v for k, v in st.items() if k != 'probes'}, sort_keys=True)}",
              flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
