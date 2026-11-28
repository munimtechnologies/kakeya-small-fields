# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Runs the pre-registered f3cert plan "five" (f3cert/PREREG.md) on Farnamfar's public
standard-five-page certificate (arXiv:2611.19594 ancillary file, CC BY 4.0; C = 152/83).
Passes when the run completes and raises no soundness alarm; the numbers themselves are written
to F3CERT_OUT (default: the folder of the MV2 run that filed this test) for a later,
separately tested commit of the results."""
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


class TestRunFive(unittest.TestCase):
    def test_five_page(self):
        cert, sha, _how = G.fetch("standard-five-page.json", out_dir("data"))
        rep = G.run("five", cert, out_dir("five"), budget=470, log=print,
                    cfg_name="standard-five-page.json", sha=sha)
        self.assertTrue(rep["complete"])
        self.assertNotIn("UNSOUND", rep["verdict"])


if __name__ == "__main__":
    unittest.main()
