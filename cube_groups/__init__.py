# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Exact checks for finite-groups.md (sections 13 and 14 of the README).

The modules import each other by their plain names (as they do when run as scripts), so this
folder is put on sys.path when `python -m unittest` discovers the tests here.
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)
