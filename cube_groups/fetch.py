# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Setup step of job m111 (as jobs m103's to m110's): download published files of
kakeya-small-fields (paths under cube_groups/, saved under their base name), waiting (up to 40
minutes) for a file that is not committed yet.

Usage: python fetch.py PATH [PATH ...]     e.g. m110.py results/m110a/m110a_grade.json
"""
import os
import sys
import time
import urllib.request

BASE = "https://raw.githubusercontent.com/munimtechnologies/kakeya-small-fields/main/cube_groups/"

for path in sys.argv[1:]:
    name = os.path.basename(path)
    for attempt in range(40):
        try:
            urllib.request.urlretrieve(BASE + path, name)
            print(f"{path}: downloaded", flush=True)
            break
        except Exception as e:
            print(f"{path}: attempt {attempt + 1} failed ({e}); waiting 60 s", flush=True)
            time.sleep(60)
    else:
        sys.exit(f"could not download {path}")
