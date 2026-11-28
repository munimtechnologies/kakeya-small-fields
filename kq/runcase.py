# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Shared body of the gate run tests test_run_kq_<q><n>.py: run kq.run_case and re-check
every reported set with the independent checker."""
import os

try:
    from . import kq, check
except ImportError:  # pragma: no cover
    import kq
    import check

OUT = os.environ.get("KQ_OUT") or r"E:\MV2-Pursuit\work\20261128T013852Z-mathematics\gate-out\kq"


def sets_of(rep):
    out = [("local_search", rep["local_search"]["set"])]
    for form, r in (rep.get("milp") or {}).items():
        if r.get("set"):
            out.append(("milp-" + form, r["set"]))
    return out


def run_and_check(tc, n, q, budget, forms=("A", "B"), ls_share=0.25, tag=""):
    rep = kq.run_case(n, q, OUT, budget, forms=forms, ls_share=ls_share, tag=tag)
    tc.assertTrue(rep["complete"])
    for name, S in sets_of(rep):
        ok, why = check.is_kakeya(S, n, q)
        tc.assertTrue(ok, (name, why))
    return rep
