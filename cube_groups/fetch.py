# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Setup step of job m103: download the published modules it imports from kakeya-small-fields,
waiting (up to 40 minutes) for a file that is not committed yet.

Usage: python fetch.py NAME [NAME ...]
"""
import sys
import time
import urllib.request

BASE = "https://raw.githubusercontent.com/munimtechnologies/kakeya-small-fields/main/cube_groups/"

for name in sys.argv[1:]:
    for attempt in range(40):
        try:
            urllib.request.urlretrieve(BASE + name, name)
            print(f"{name}: downloaded", flush=True)
            break
        except Exception as e:
            print(f"{name}: attempt {attempt + 1} failed ({e}); waiting 60 s", flush=True)
            time.sleep(60)
    else:
        sys.exit(f"could not download {name}")
