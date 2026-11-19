# sticky_beam.py -- pre-registered search (notes/prereg-sticky-beam.md, note a188) for a full sticky
# tree over F_3 whose three slices have product below 8^k.  By Theorem 78 (note a188), ONE such tree,
# of any height k, proves that the smallest sticky Kakeya sets in F_3^n have at most C * b^n points
# for some b < 2, i.e. it answers question S7 ("is the sticky Kakeya base below 2?") with yes.
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only, self-contained.
#
# Trees.  A full tree of height k is a dict of node maps, prefix (tuple of length j < k) -> 3-tuple
# (g(0), g(1), g(2)), with P(d)_j = g_{d[:j]}(d_j); slice t is S_t = {P(d) + t d : d in F_3^k}.
# A node of height k + 1 is a root map r and three children of height k: plane v of its slice t is
# the union of the slices t of the children x with r(x) + t x = v (unions are exact, not maxima).
#
# Bitsets.  A subset of F_3^k is an int; point y has bit index sum_j y_j 3^(k-1-j).
#
# Free symmetries (Lemma 161, a188): P'(d) = P(eps d) + c d has S'_t = S_(eps (c + t)) (eps = 1, 2;
# all six permutations of the three slices), and adding a constant w_j at level j translates every
# slice by w.  The beam keeps, at each height, a few dozen base trees chosen for small weighted
# log-sizes (a grid of 28 weight vectors, so lopsided trees survive too) and for small product, and
# builds the next height from all their slice permutations and some translates.
#
# Every claimed hit is rebuilt as explicit node maps from its recipe and its slices are recomputed
# from the maps by direct enumeration, independently of the bitset arithmetic.

import argparse
import itertools
import json
import math
import os
import random
import time

ALL_MAPS = list(itertools.product(range(3), repeat=3))
TRIANGLE = (0, 1, 1)          # x -> x^2: child t is alone in slice t
BETAS = [(i / 6.0, j / 6.0, (6 - i - j) / 6.0) for i in range(7) for j in range(7 - i)]

try:
    popcount = int.bit_count
except AttributeError:        # Python < 3.10
    def popcount(x):
        return bin(x).count("1")


def prod3(s):
    return s[0] * s[1] * s[2]


# ----------------------------------------------------------------------------- bitsets

_TABLES = {}


def translation_table(w, k):
    key = (w, k)
    tab = _TABLES.get(key)
    if tab is None:
        tab = [0]
        for j in range(k):
            tab = [i * 3 + (v + w[j]) % 3 for i in tab for v in range(3)]
        if len(_TABLES) > 4000:
            _TABLES.clear()
        _TABLES[key] = tab
    return tab


def translate_bits(bits, w, k):
    """The set {y + w : y in bits} as a bitset over F_3^k."""
    if bits == 0 or w is None or not any(w):
        return bits
    tab = translation_table(w, k)
    n = 3 ** k
    chars = ["0"] * n
    s = bin(bits)[2:][::-1]
    for i, ch in enumerate(s):
        if ch == "1":
            chars[n - 1 - tab[i]] = "1"
    return int("".join(chars), 2)


def combine(root, kids, k):
    """Slices of the node with root map `root` over three children of height k (bitset triples)."""
    block = 3 ** k
    out = []
    for t in range(3):
        acc = 0
        for x in range(3):
            acc |= kids[x][t] << (((root[x] + t * x) % 3) * block)
        out.append(acc)
    return tuple(out)


def perm_slices(S, eps, c):
    return tuple(S[(eps * (c + t)) % 3] for t in range(3))


# ----------------------------------------------------------------------------- explicit maps


def perm_maps(maps, eps, c):
    """P'(d) = P(eps d) + c d."""
    out = {}
    for a in maps:
        g = maps[tuple((eps * v) % 3 for v in a)]
        out[a] = tuple((g[(eps * y) % 3] + c * y) % 3 for y in range(3))
    return out


def translate_maps(maps, w):
    if w is None:
        return dict(maps)
    return {a: tuple((g[y] + w[len(a)]) % 3 for y in range(3)) for a, g in maps.items()}


def node_maps(root, kid_maps):
    out = {(): tuple(root)}
    for x in range(3):
        for a, g in kid_maps[x].items():
            out[(x,) + a] = g
    return out


def is_full(maps, k):
    want = {a for j in range(k) for a in itertools.product(range(3), repeat=j)}
    if set(maps) != want:
        return False
    return all(len(g) == 3 and all(v in (0, 1, 2) for v in g) for g in maps.values())


def slices_from_maps(maps, k):
    """Slices of a full tree by direct enumeration of all 3^k directions (bitsets)."""
    n = 3 ** k
    flags = [bytearray(n) for _ in range(3)]
    for d in itertools.product(range(3), repeat=k):
        p = [maps[d[:j]][d[j]] for j in range(k)]
        for t in range(3):
            idx = 0
            for j in range(k):
                idx = idx * 3 + (p[j] + t * d[j]) % 3
            flags[t][idx] = 1
    out = []
    for f in flags:
        out.append(int("".join("1" if f[i] else "0" for i in range(n - 1, -1, -1)), 2))
    return tuple(out)


def maps_of_base(k, i, bases, memo):
    key = (k, i)
    if key not in memo:
        rec = bases[k][i]["recipe"]
        if rec[0] == "leaf":
            memo[key] = {}
        else:
            memo[key] = node_maps(rec[1], [maps_of_entry(er, bases, memo) for er in rec[2]])
    return memo[key]


def maps_of_entry(er, bases, memo):
    k, i, eps, c, w = er
    return translate_maps(perm_maps(maps_of_base(k, i, bases, memo), eps, c), w)


# ----------------------------------------------------------------------------- the beam


def default_config():
    return {"kmax": 10, "cands": 40000, "cap": 1500, "per_beta": 3, "top_prod": 16,
            "translates": 1, "trans_bases": 24, "local_top": 12, "local_tries": 150,
            "passes": 2, "exhaust": 200000, "max_hits": 5}


def build_entries(k, blist, rng, cfg):
    """All slice permutations of every base, plus random translates of the first few bases."""
    out = []
    for i, b in enumerate(blist):
        ws = [None]
        if k > 0 and i < cfg["trans_bases"]:
            for _ in range(cfg["translates"]):
                w = tuple(rng.randrange(3) for _ in range(k))
                if any(w):
                    ws.append(w)
        for eps in (1, 2):
            for c in range(3):
                Sp = perm_slices(b["S"], eps, c)
                for w in ws:
                    St = Sp if w is None else tuple(translate_bits(s, w, k) for s in Sp)
                    out.append((St, (k, i, eps, c, w)))
    return out


def select(pool, cfg):
    """Keys to keep: for each weight vector the best few by weighted log of the sorted sizes, and
    the best few by product.  pool: key -> (sizes, S, root, ids, order)."""
    items = list(pool.items())
    logs = {}
    for key, v in items:
        s = sorted(v[0])
        logs[key] = (math.log(s[0]), math.log(s[1]), math.log(s[2]))
    keep = set()
    for b in BETAS:
        ranked = sorted(items, key=lambda kv: (b[0] * logs[kv[0]][0] + b[1] * logs[kv[0]][1]
                                               + b[2] * logs[kv[0]][2], kv[1][4]))
        for kv in ranked[:cfg["per_beta"]]:
            keep.add(kv[0])
    ranked = sorted(items, key=lambda kv: (prod3(kv[1][0]), kv[1][4]))
    for kv in ranked[:cfg["top_prod"]]:
        keep.add(kv[0])
    return keep


def grow(k, entries, rng, cfg):
    """Candidates of height k + 1 built from entries of height k.
    Returns (pool, hits, evaluations); hits are (root, ids, sizes) with product < 8^(k+1)."""
    pool = {}
    hits = []
    counter = [0, 0]                      # insertion order, evaluations
    target = 8 ** (k + 1)
    E = len(entries)

    def consider(root, ids):
        counter[1] += 1
        S = combine(root, [entries[i][0] for i in ids], k)
        sizes = (popcount(S[0]), popcount(S[1]), popcount(S[2]))
        p = prod3(sizes)
        if p < target and len(hits) < cfg["max_hits"]:
            hits.append((tuple(root), tuple(ids), sizes))
        key = tuple(sorted(S))
        if key not in pool:
            counter[0] += 1
            pool[key] = (sizes, S, tuple(root), tuple(ids), counter[0])
            if len(pool) > cfg["cap"]:
                keep = select(pool, cfg)
                for kk in list(pool):
                    if kk not in keep:
                        del pool[kk]
        return p

    if 27 * E ** 3 <= cfg["exhaust"]:
        for root in ALL_MAPS:
            for ids in itertools.product(range(E), repeat=3):
                consider(root, ids)
        return pool, hits, counter[1]

    for i, (S, er) in enumerate(entries):
        if er[2] == 1 and er[3] == 0 and er[4] is None:
            consider(TRIANGLE, (i, i, i))          # doubling: keeps the classical ratio
    for _ in range(cfg["cands"]):
        consider(rng.choice(ALL_MAPS), (rng.randrange(E), rng.randrange(E), rng.randrange(E)))
    for _ in range(cfg["passes"]):
        top = sorted(pool.values(), key=lambda v: (prod3(v[0]), v[4]))[:cfg["local_top"]]
        for v in top:
            root, ids, cur = v[2], list(v[3]), prod3(v[0])
            for r in ALL_MAPS:
                p = consider(r, tuple(ids))
                if p < cur:
                    cur, root = p, r
            for slot in range(3):
                for _ in range(cfg["local_tries"]):
                    trial = list(ids)
                    trial[slot] = rng.randrange(E)
                    p = consider(root, tuple(trial))
                    if p < cur:
                        cur, ids = p, trial
    return pool, hits, counter[1]


def maps_to_json(maps):
    return [[list(a), list(g)] for a, g in sorted(maps.items(), key=lambda kv: (len(kv[0]), kv[0]))]


def verify(root, kid_recipes, bases, height):
    """Rebuild the explicit node maps and recompute the slices from them."""
    memo = {}
    maps = node_maps(root, [maps_of_entry(er, bases, memo) for er in kid_recipes])
    S = slices_from_maps(maps, height)
    return maps, is_full(maps, height), S


def run(cfg, seed, deadline=None, log=None):
    rng = random.Random(seed)
    bases = {0: [{"S": (1, 1, 1), "sizes": (1, 1, 1), "recipe": ("leaf",)}]}
    heights = {}
    hits = []
    for k in range(cfg["kmax"]):
        if deadline is not None and time.time() > deadline:
            break
        entries = build_entries(k, bases[k], rng, cfg)
        pool, raw_hits, nevals = grow(k, entries, rng, cfg)
        keep = select(pool, cfg)
        new = []
        for key in sorted(keep, key=lambda kk: pool[kk][4]):
            sizes, S, root, ids, _ = pool[key]
            new.append({"S": S, "sizes": sizes,
                        "recipe": ("node", root, tuple(entries[i][1] for i in ids))})
        bases[k + 1] = new
        best = min(new, key=lambda b: (prod3(b["sizes"]), sorted(b["sizes"])))
        h = k + 1
        heights[h] = {"best_product": prod3(best["sizes"]), "eight_to_k": 8 ** h,
                      "best_sizes": sorted(best["sizes"]), "evaluations": nevals,
                      "bases_kept": len(new)}
        for root, ids, sizes in raw_hits:
            kid_recipes = tuple(entries[i][1] for i in ids)
            maps, full, S = verify(root, kid_recipes, bases, h)
            sz = [popcount(s) for s in S]
            hits.append({"height": h, "claimed_sizes": list(sizes), "recomputed_sizes": sz,
                         "full_tree": full, "verified": bool(full and prod3(sz) < 8 ** h
                                                             and tuple(sz) == tuple(sizes)),
                         "maps": maps_to_json(maps) if h <= 10 else None})
        if log:
            log("seed %d height %d: best %d vs 8^k %d (ratio %.6f) sizes %s, %d evaluations, %d hits"
                % (seed, h, heights[h]["best_product"], 8 ** h, heights[h]["best_product"] / 8.0 ** h,
                   heights[h]["best_sizes"], nevals, len(raw_hits)))
    return {"seed": seed, "heights": heights, "hits": hits, "bases": bases}


def best_maps(result, h):
    """Explicit maps of the best-product base at height h of a run (for near-miss reports)."""
    blist = result["bases"][h]
    i = min(range(len(blist)), key=lambda j: (prod3(blist[j]["sizes"]), sorted(blist[j]["sizes"])))
    return maps_of_base(h, i, result["bases"], {})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--minutes", type=float, default=150.0)
    ap.add_argument("--kmax", type=int, default=10)
    ap.add_argument("--cands", type=int, default=40000)
    ap.add_argument("--seed0", type=int, default=20261119)
    args = ap.parse_args()
    cfg = default_config()
    cfg["kmax"] = args.kmax
    cfg["cands"] = args.cands
    os.makedirs(args.out_dir, exist_ok=True)
    deadline = time.time() + 60.0 * args.minutes
    overall = {}
    all_hits = []
    near = {}
    restarts = 0
    seed = args.seed0
    while time.time() < deadline:
        res = run(cfg, seed, deadline=deadline, log=lambda s: print(s, flush=True))
        restarts += 1
        for h, v in res["heights"].items():
            cur = overall.get(h)
            if cur is None or v["best_product"] < cur["best_product"]:
                overall[h] = dict(v, seed=seed)
                if h <= 7:
                    near[h] = maps_to_json(best_maps(res, h))
        all_hits.extend(dict(x, seed=seed) for x in res["hits"])
        out = {
            "job": "sticky-beam-v1",
            "made_with": "AI agents working in MV2's name; no human has checked this",
            "config": cfg, "restarts": restarts,
            "per_height": {str(h): overall[h] for h in sorted(overall)},
            "hits": all_hits[:50],
            "verified_hit": any(x["verified"] for x in all_hits),
            "outcome": ("S7-CERT" if any(x["verified"] for x in all_hits) else "S7-NONE"),
        }
        with open(os.path.join(args.out_dir, "beam_summary.json"), "w") as fh:
            json.dump(out, fh, indent=1)
        with open(os.path.join(args.out_dir, "beam_best_maps.json"), "w") as fh:
            json.dump({str(h): m for h, m in sorted(near.items())}, fh)
        seed += 1
    print("OUTCOME", "S7-CERT" if any(x["verified"] for x in all_hits) else "S7-NONE", flush=True)


if __name__ == "__main__":
    main()
