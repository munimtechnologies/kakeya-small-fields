# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job cert7: DRAT proof certificates for the 24 split instances of (B6) that job m85 re-ran, the
ones that closed the classes o010_c004 and o010_c006 (Corollaries 106 and 107; notes/a71.md,
a72.md) (cube_groups/cert7-predictions.md; notes/a85.md).

What came back on 2026-10-23: job cert6 certified the 49 instances of job m86 (all VERIFIED by
drat-trim, notes/a85.md). m85's 24 are the next family of 5-minute re-runs with the same row
format: UNSAT in CaDiCaL (through python-sat) in 19.43 to 120.16 s each (m85a and m85b), saved
without certificates. This job rebuilds each with the very same code, solves it with a standalone
CaDiCaL that writes a DRAT proof, and checks the proof with drat-trim.

Group a (job cert7a): m85's group a, the 12 of r3b_t7_B6_o010_c004 (all of rank 0, with
  Lemma 93 (b)).
Group b (job cert7b): m85's group b, the 12 of r3b_t7_B6_o010_c006 (all of rank 0).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

This file is cert6.py with m85's rows in place of m86's. m85.py, like m86.py, has no lists_ok and
keeps its class lists per group, so its named_list check is written out here (groups_ok,
specs_ok). Everything else is cert1.py's, imported unchanged: the two programs (built by
cert1_tools.py), the controls, and one instance's certificate (certify_one). The instances, the
class gates, the roots (recomputed as m85's check did, with its seed, in its order) and the rows
are m85.py's, imported unchanged; m69.py's split_spec builds each instance. One change from
cert6.py: grade's "slowest" is the slowest by CaDiCaL alone, as the predictions say, not by
CaDiCaL plus drat-trim.

Parts:
    check    cert1's 10 graded checks, then the group: its class against m66's run (m85's gate) and
             its roots recomputed; its instances, once each, equal to m85's rows (name, m66 index,
             orbit size, A_(v_1), rank), Lemma 93 (b) on every one (all of rank 0); the variable,
             clause, hint and unit counts of the first instance equal to m85's own check. Writes
             cert7_specs.json and check.json.
    certify  each instance of the group in m85's order, as cert1 does; the proof is deleted after
             it is checked.
    grade    counts and times, by class; which instances are not VERIFIED.

Usage: python cert7.py --part check|certify|grade --group a|b [--tools tools] [--minutes 120]
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
import m85

b, m = c1.b, c1.m
GROUPS = ("a", "b")
# m85's own check (compete-results/m85a-b6rerun-v1 and m85b-b6rerun-v1, check.json probe
# named_l_cadical, 2026-10-22): [vars, clauses, hints, units] of the first rank-0 instance of the
# group, CaDiCaL arm. Every re-run of m85 is of rank 0, so there is no "s" probe.
M85_PROBES = {"a": {"l": [48587, 286239, 79, 70]}, "b": {"l": [48587, 286239, 79, 70]}}
SPECS_FILE = "cert7_specs.json"


def rows(group):
    """m85's rows of the group: (class, k, rank on X_1, m66 index, orbit size, A_(v_1))."""
    return m85.named_rows(group)


def classes(group):
    """The group's classes in the order m85's check recomputed their roots."""
    return list(m85.NAMED_CLASSES[group])


def per_class(group):
    """Re-runs per class of the group: the instances m83a and m83b left open."""
    return {n: m85.BEFORE[n][0] - m85.BEFORE[n][1] for n in classes(group)}


def group_specs(group, reps):
    """m85's re-runs as they ran: m69's split instance at each root, with Lemma 93 (b) when of
    rank 0."""
    return m85.named_specs(group, reps)


def groups_ok():
    """The two groups are m85's, with its 12 and 12 rows over its two classes, once each."""
    every = [row for g in GROUPS for row in rows(g)]
    return (len(every) == len(m85.OPEN_PREV) == 24
            and len({(r[0], r[1]) for r in every}) == len(every)
            and sorted(n for g in GROUPS for n in classes(g)) == sorted(m85.NAMED_GATE)
            == sorted(m85.BEFORE)
            and [len(rows(g)) for g in GROUPS] == [m85.NAMED_COUNT[g] for g in GROUPS] == [12, 12]
            and all(sum(m85.NAMED_RANKS[g].values()) == m85.NAMED_COUNT[g] for g in GROUPS)
            and [sum(per_class(g).values()) for g in GROUPS] == [12, 12])


def specs_ok(group, specs):
    rs = rows(group)
    per = {}
    for sp in specs:
        per[sp["parent"]] = per.get(sp["parent"], 0) + 1
    return (len(specs) == len(rs) == m85.NAMED_COUNT[group]
            and len({sp["name"] for sp in specs}) == len(specs)
            and per == per_class(group)
            and all(sum(sp["rank_x1"] == rk for sp in specs) == c
                    for rk, c in m85.NAMED_RANKS[group].items())
            and all(sp["parent"] == name and sp["name"] == m85.named_name(name, k, rk)
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
    rng = random.Random(85)
    reps = {}
    for name in classes(group):
        gate = m85.NAMED_GATE[name]
        r, rr = b.class_reps(name, rng)
        graded["class_" + name[10:]] = m85.class_ok(r, gate)
        graded["class_reps_" + name[10:]] = m85.reps_ok(name, rr, gate)
        reps[name] = rr
    graded["groups"] = groups_ok()
    specs = group_specs(group, reps)
    graded["group"] = specs_ok(group, specs)
    for tag, want in M85_PROBES[group].items():
        sp = next(x for x in specs if bool(x.get("lemma93")) == (tag == "l"))
        got, consistent = probe(sp)
        probes["m85_" + tag] = [sp["name"]] + got
        graded["m85_probe_" + tag] = got == want and consistent
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
            with open(os.path.join(out_dir, f"cert7_{sp['name']}.json"), "w") as f:
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
        p = os.path.join(out_dir, f"cert7_{sp['name']}.json")
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
