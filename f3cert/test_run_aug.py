# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Runs the pre-registered f3cert plan "aug" (f3cert/PREREG.md: certificate rows plus all pairs
of reading lines, their F_3 cross lines and the neighbours of every certificate row) on
Farnamfar's standard-five-page certificate (arXiv:2611.19594, CC BY 4.0).  Passes when the run
completes without a soundness alarm; numbers go to F3CERT_OUT for a separately tested commit."""
import os
import sys
import tempfile
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import gaterun as G
except ImportError:  # pragma: no cover
    import gaterun as G

OUT_BASE = os.environ.get("F3CERT_OUT") or r"E:\MV2-Pursuit\work\20261128T000550Z-mathematics\gate-out"


def out_dir(sub):
    path = os.path.join(OUT_BASE, sub)
    try:
        os.makedirs(path, exist_ok=True)
        return path
    except OSError:
        return tempfile.mkdtemp(prefix="f3cert-" + sub + "-")


class TestRunAug(unittest.TestCase):
    def test_five_page_augmented(self):
        cert, sha, _how = G.fetch("standard-five-page.json", out_dir("data"))
        rep = G.run("aug", cert, out_dir("aug"), budget=470, log=print,
                    cfg_name="standard-five-page.json", sha=sha)
        self.assertTrue(rep["complete"])
        self.assertNotIn("UNSOUND", rep["verdict"])


if __name__ == "__main__":
    unittest.main()
