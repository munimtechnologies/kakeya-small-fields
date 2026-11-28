# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Arithmetic re-check of an f3cert gate run (results.json, best_cert.json, control_cert.json).

For each exported certificate it recomputes, in exact rational arithmetic and without the LP
code, the bound

    cost . h >= -sum_r mult_r const_r + sum_k min(0, r_k) hi_k,   r = cost - sum_r mult_r a_r,

from the listed rows (each a_r . h + const_r >= 0) and boxes 0 <= h_k <= hi_k, and checks that it
equals the stated bound.  It also checks the boxes (hi <= number of vertices; in uniform variants
hi <= the F_3-dimension of the listed generators), that the control certifies at least 1 and that
the verdict matches the numbers.  It does NOT re-derive the entropy classes or the validity of
each row from the configuration; that independent modelling check is separate work."""
import json
import os
from fractions import Fraction

KLSS_W = Fraction(0.579380164285695)
RECORD_W = Fraction(114631769327023765, 209357544569848128)
MARGIN = Fraction(1, 10 ** 6)


def recompute(cert):
    r = {k: Fraction(v) for k, v in cert["objective"].items()}
    val = Fraction(0)
    for row in cert["rows"]:
        q = Fraction(row["mult"])
        if q <= 0:
            raise AssertionError("non-positive multiplier")
        val -= q * Fraction(row["const"])
        for k, a in row["coeffs"].items():
            r[k] = r.get(k, Fraction(0)) - q * Fraction(a)
    nv = int(cert["nverts"])
    for k, rv in r.items():
        if rv >= 0:
            continue
        lo, hi = cert["box"][k]
        if lo != 0 or not 0 <= hi <= nv:
            raise AssertionError("bad box for %s" % k)
        if cert.get("uniform"):
            dim = len(cert["keys"][k]["gens"])
            if hi > dim:
                raise AssertionError("uniform box above dimension for %s" % k)
        elif hi != nv:
            raise AssertionError("box differs from the vertex count for %s" % k)
        val += rv * hi
    return val


def load(dirpath):
    with open(os.path.join(dirpath, "results.json")) as fh:
        rep = json.load(fh)
    certs = {}
    for name in ("best_cert.json", "control_cert.json"):
        with open(os.path.join(dirpath, name)) as fh:
            certs[name] = json.load(fh)
    return rep, certs


def check(dirpath):
    rep, certs = load(dirpath)
    assert rep.get("complete"), "run incomplete"
    v = rep["verdict"]
    assert "UNSOUND" not in v and "CONTROL_FAIL" not in v, v
    assert rep.get("replay_nonzero_classes", 0) == 0
    best = certs["best_cert.json"]
    out = {"verdict": v}
    if not best.get("none"):
        val = recompute(best)
        assert val == Fraction(best["lb"]), (val, best["lb"])
        assert Fraction(rep["best_lb_exact"]) == val
        assert val <= KLSS_W, "above the KLSS ceiling"
        out["best"] = val
    ctl = certs["control_cert.json"]
    if not ctl.get("none"):
        cval = recompute(ctl)
        assert cval == Fraction(ctl["lb"])
        assert cval >= 1 - MARGIN, "control below 1"
        out["control"] = cval
    # the verdict follows from the symmetric bounds
    claimed = rep.get("claimed_C")
    own = 1 / Fraction(claimed) if claimed else Fraction(1, 2)
    want = "NO_GAIN"
    for info in rep["variants"].values():
        if info.get("symmetric") and "lb_exact" in info:
            lb = Fraction(info["lb_exact"])
            if lb > RECORD_W:
                want = "F3_RECORD"
            elif lb > own + MARGIN and want == "NO_GAIN":
                want = "F3_GAIN"
    assert v == want, (v, want)
    return out
