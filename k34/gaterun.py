# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Shared body of the gate run tests: a positive control in F_4^3 (the search must reach a
28-point set when asked for sets below 29, on the orbit of the 2 x 2 slice of the
Kopparty-Saraf-Sudan set) and the resumable main search for sets below 28."""
import json
import os
import time

try:
    from . import slices, verify
except ImportError:  # pragma: no cover
    import slices
    import verify

OUT = os.environ.get("K34_OUT") or r"E:\MV2-Pursuit\work\20261128T050555Z-mathematics\gate-out\k34"


def orbit_rep_of(geo, S):
    """Orbit representative (as produced by slices.orbits) of the plane subset S."""
    S = tuple(sorted(S))
    for rep, _sz in slices.orbits(geo, len(S)):
        orb = {rep}
        todo = [rep]
        gens = geo.generators()
        while todo:
            A = todo.pop()
            for g in gens:
                B = tuple(sorted(g[p] for p in A))
                if B not in orb:
                    orb.add(B)
                    todo.append(B)
        if S in orb:
            return rep
    raise AssertionError("no orbit found")


def positive_control(cap):
    geo = slices.Geo(4)
    grid = [geo.idx(0, 0), geo.idx(0, 1), geo.idx(1, 0), geo.idx(1, 1)]
    rep = orbit_rep_of(geo, grid)
    s = slices.SliceSearch(geo, rep, 29, deadline=time.time() + cap, stop_at_first=True,
                           max_solutions=1)
    t0 = time.time()
    try:
        rec = s.run()
        rec["timed_out"] = False
    except slices.Timeout:
        rec = {"r": 4, "S0": list(rep), "T": 29, "nodes": s.nodes, "complete": False,
               "timed_out": True, "solutions": []}
    rec["seconds"] = round(time.time() - t0, 1)
    found = bool(rec["solutions"])
    ok = None
    if found:
        sol = rec["solutions"][0]
        ok = verify.is_kakeya3(sol["points"], 4)[0] and len(sol["points"]) == sol["size"]
    out = {"what": "positive control: search F_4^3 for sets below 29 on the orbit of the 2x2 "
                   "slice of the 28-point KSS set, stop at the first leaf below 29",
           "rep": list(rep), "found": found, "verified": ok, "record": rec,
           "made_with": "AI agents working in MV2's name; not checked by a human mathematician"}
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "control-q4-T29.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    return out


def main_search(budget, label):
    return slices.run_queue(4, 28, OUT, budget, label)
