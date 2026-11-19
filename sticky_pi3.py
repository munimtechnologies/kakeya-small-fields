# sticky_pi3.py -- a lower bound for pi_3 (note a188): the least slice product of a full sticky tree
# of height 3.  Every real slice-size vector of height 2 is computed exhaustively (27^4 trees).  A
# node of height 3 has slice sizes at least sum over its value classes of the MAX of the children's
# sizes (the union is at least the largest set), which is monotone in the children, so it is
# enough to try the coordinatewise-minimal height-2 vectors under all 27 root maps.  If the result
# is 512 = 8^3, then pi_3 = 512 and no certificate for S7 exists at height <= 3.
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only, self-contained.

import itertools
import json
import sys

ALL_MAPS = list(itertools.product(range(3), repeat=3))
POP = [bin(i).count("1") for i in range(8)]


def vmask(g, t):
    m = 0
    for z in range(3):
        m |= 1 << ((g[z] + t * z) % 3)
    return m


def height2_vectors():
    V = [[vmask(g, t) for t in range(3)] for g in ALL_MAPS]
    vecs = set()
    for r in ALL_MAPS:
        planes = [[(r[x] + t * x) % 3 for x in range(3)] for t in range(3)]
        for h in itertools.product(range(27), repeat=3):
            s = []
            for t in range(3):
                acc = [0, 0, 0]
                for x in range(3):
                    acc[planes[t][x]] |= V[h[x]][t]
                s.append(POP[acc[0]] + POP[acc[1]] + POP[acc[2]])
            vecs.add(tuple(s))
    return vecs


def minimal(vecs):
    out = []
    for v in vecs:
        if not any(u != v and all(u[i] <= v[i] for i in range(3)) for u in vecs):
            out.append(v)
    return sorted(out)


def node_lower(root, kids):
    L = []
    for t in range(3):
        classes = {}
        for x in range(3):
            classes.setdefault((root[x] + t * x) % 3, []).append(kids[x][t])
        L.append(sum(max(v) for v in classes.values()))
    return L


def bounds(mins):
    best_p = None
    best_s = None
    for kids in itertools.product(mins, repeat=3):
        for root in ALL_MAPS:
            L = node_lower(root, kids)
            p = L[0] * L[1] * L[2]
            s = L[0] + L[1] + L[2]
            if best_p is None or p < best_p[0]:
                best_p = (p, list(L), [list(k) for k in kids], list(root))
            if best_s is None or s < best_s[0]:
                best_s = (s, list(L), [list(k) for k in kids], list(root))
    return best_p, best_s


def main():
    vecs = height2_vectors()
    mins = minimal(vecs)
    bp, bs = bounds(mins)
    out = {
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "height2_vectors": sorted(list(v) for v in vecs),
        "height2_minimal": [list(v) for v in mins],
        "pi3_lower_bound": bp[0], "pi3_witness": bp[1:],
        "sigma3_lower_bound": bs[0], "sigma3_witness": bs[1:],
        "classical_height3": {"product": 512, "sum": 24},
        "pi3_equals_512": bp[0] >= 512,
    }
    path = sys.argv[1] if len(sys.argv) > 1 else "pi3.json"
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("pi3 lower bound", bp[0], "sigma3 lower bound", bs[0], flush=True)


if __name__ == "__main__":
    main()
