# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Builds the two outside programs job cert1 uses, from their published sources:

    CaDiCaL (A. Biere et al., MIT licence), tag rel-2.2.1, the solver that writes DRAT proofs;
    drat-trim (M. Heule et al., MIT licence), drat-trim.c from its master branch, the checker.

Writes tools/cadical, tools/drat-trim and tools/tools.json (sources and their SHA-256), so that
the run records exactly what was built.

Usage: python cert1_tools.py [--dest tools]
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tarfile
import urllib.request

CADICAL_TAG = "rel-2.2.1"
CADICAL_URL = f"https://github.com/arminbiere/cadical/archive/refs/tags/{CADICAL_TAG}.tar.gz"
DRAT_URL = "https://raw.githubusercontent.com/marijnheule/drat-trim/master/drat-trim.c"


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def build(dest):
    os.makedirs(dest, exist_ok=True)
    tgz = os.path.join(dest, "cadical.tar.gz")
    urllib.request.urlretrieve(CADICAL_URL, tgz)
    with tarfile.open(tgz) as tf:
        tf.extractall(dest, filter="data")
    src = os.path.join(dest, f"cadical-{CADICAL_TAG}")
    subprocess.run(["sh", "./configure"], cwd=src, check=True)
    subprocess.run(["make", "-j2"], cwd=src, check=True)
    shutil.copy(os.path.join(src, "build", "cadical"), os.path.join(dest, "cadical"))
    c = os.path.join(dest, "drat-trim.c")
    urllib.request.urlretrieve(DRAT_URL, c)
    subprocess.run(["gcc", "-O2", "-o", os.path.join(dest, "drat-trim"), c], check=True)
    for exe in ("cadical", "drat-trim"):
        os.chmod(os.path.join(dest, exe), 0o755)
    info = {"cadical": {"url": CADICAL_URL, "sha256": sha256(tgz)},
            "drat_trim": {"url": DRAT_URL, "sha256": sha256(c)}}
    with open(os.path.join(dest, "tools.json"), "w") as f:
        json.dump(info, f, indent=1)
    print(f"tools: {json.dumps(info)}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dest", default="tools")
    build(ap.parse_args().dest)


if __name__ == "__main__":
    main()
