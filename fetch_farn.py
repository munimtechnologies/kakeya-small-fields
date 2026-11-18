"""fetch_farn.py -- fetch the ancillary certificates of arXiv:2611.19594v1 and replay them
with the author's own verifiers (in the sealed job container only).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence of this script: Apache-2.0. The downloaded files keep their own licences
(LICENSE-check630.txt, LICENSE-data.txt in the arXiv ancillary folder); nothing downloaded
is redistributed by MV2's repository.

Usage: python fetch_farn.py DEST
Writes DEST/certs/*.json, DEST/fetch.json (sources, SHA-256, author-verifier exit codes and
output tails). Always exits 0: failures are recorded, and kakeya_sparse.py reports missing
files.
"""

import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import urllib.request

ARXIV = "2611.19594v1"
SOURCES = ["https://arxiv.org/src/%s" % ARXIV, "https://arxiv.org/e-print/%s" % ARXIV]
CERTS = ["standard-five-page.json", "standard.json", "record.json", "all-groups.json"]
AUTHOR_CHECKS = [
    ["anc/verify_group.py", "anc/certificates/standard-five-page.json"],
    ["anc/verify_group.py", "anc/certificates/standard.json"],
    ["anc/verify_group.py", "anc/certificates/record.json", "--invert", "2"],
]
UA = {"User-Agent": "MV2-Munim-research/1.0 (mv2@munimtech.com)"}


def get(url):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=180) as r:
        return r.read()


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        h.update(fh.read())
    return h.hexdigest()


def find_root(src):
    for dirpath, dirnames, _ in os.walk(src):
        if "anc" in dirnames:
            return dirpath
    return None


def main(argv):
    dest = argv[1] if len(argv) > 1 else "farn"
    os.makedirs(dest, exist_ok=True)
    src = os.path.join(dest, "src")
    certdir = os.path.join(dest, "certs")
    os.makedirs(certdir, exist_ok=True)
    log = {"arxiv": ARXIV, "errors": [], "certs": {}, "author_checks": []}
    root = None
    for url in SOURCES:
        try:
            data = get(url)
            log["tarball_sha256"] = hashlib.sha256(data).hexdigest()
            with tarfile.open(fileobj=io.BytesIO(data), mode="r:*") as tf:
                tf.extractall(src, filter="data")
            root = find_root(src)
            log["source"] = url
            if root:
                break
        except Exception as e:  # noqa: BLE001
            log["errors"].append("%s: %r" % (url, e))
    for name in CERTS:
        out = os.path.join(certdir, name)
        p = os.path.join(root, "anc", "certificates", name) if root else None
        try:
            if p and os.path.exists(p):
                shutil.copy(p, out)
                how = "tarball"
            else:
                with open(out, "wb") as fh:
                    fh.write(get("https://arxiv.org/src/%s/anc/certificates/%s" % (ARXIV, name)))
                how = "direct"
            with open(out) as fh:
                cert = json.load(fh)
            log["certs"][name] = {"how": how, "sha256": sha(out),
                                  "claimed_C": cert.get("claimed_C"),
                                  "rows": len(cert.get("rows", [])),
                                  "steps": len(cert.get("steps", [])),
                                  "extra": len(cert.get("extra") or [])}
        except Exception as e:  # noqa: BLE001
            log["errors"].append("%s: %r" % (name, e))
            if os.path.exists(out):
                os.remove(out)
    if root:
        for args in AUTHOR_CHECKS:
            try:
                p = subprocess.run([sys.executable] + args, cwd=root, capture_output=True,
                                   text=True, timeout=1800)
                log["author_checks"].append({"args": args, "exit": p.returncode,
                                             "stdout_tail": p.stdout[-3000:],
                                             "stderr_tail": p.stderr[-2000:]})
            except Exception as e:  # noqa: BLE001
                log["author_checks"].append({"args": args, "error": repr(e)})
    with open(os.path.join(dest, "fetch.json"), "w") as fh:
        json.dump(log, fh, indent=1)
    print(json.dumps({k: v for k, v in log.items() if k != "author_checks"}, indent=1))
    for c in log["author_checks"]:
        print(c.get("args"), "exit", c.get("exit"), c.get("error", ""))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
