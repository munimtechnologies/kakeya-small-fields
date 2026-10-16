"""Search the Z_4^k framework (Lemma 22 of robust-cubes-v5i) for k = 3.

Setting: L a finite 2-group whose involutions are all central, A = Z_4^k normal and
self-centralising with Omega_1(L) = 2A, H = L/A embedded as an n-dim subspace V of
(M_k(F_2), +) by h -> M_h. A counterexample to |L| <= |Omega_1(L)|^(e+1) needs e = 3 and
n >= 2k + 1, so for k = 3 it contains one with n = 7 (restrict to a 7-dim subspace of H).

Necessary conditions on the data (sigma: H -> F_2^k quadratic with polar form beta):
  (c) M_(h') sigma(h) = (I + M_h) beta(h, h')   for all h, h'
  (d) h != 0 and sigma(h) = 0  =>  I + M_h singular
  (e3) sigma is not identically zero.
(c) is linear in (sigma, beta), so for each V it is solved exactly; (d) and (e3) are then
searched over the solution space. V runs over conjugacy-class representatives of
7-dim subspaces of M_3(F_2) (orthogonal complements of 2-dim subspaces W).

By MV2 of Munim, Inc. Licence: Apache-2.0.
"""

import argparse
import json
import os
import time


def rows(M, k):
    m = (1 << k) - 1
    return [(M >> (k * i)) & m for i in range(k)]


def from_rows(R, k):
    M = 0
    for i, r in enumerate(R):
        M |= r << (k * i)
    return M


def identity(k):
    return from_rows([1 << i for i in range(k)], k)


def matmul(A, B, k):
    RB = rows(B, k)
    out = []
    for ra in rows(A, k):
        r = 0
        for l in range(k):
            if (ra >> l) & 1:
                r ^= RB[l]
        out.append(r)
    return from_rows(out, k)


def insert(piv, r):
    """Add r to a XOR basis keyed by highest bit; True if r was independent."""
    while r:
        hb = r.bit_length() - 1
        if hb in piv:
            r ^= piv[hb]
        else:
            piv[hb] = r
            return True
    return False


def invertible(M, k):
    piv = {}
    return all(insert(piv, r) for r in rows(M, k))


def parity(x):
    return x.bit_count() & 1


def apply(M, forms, k):
    """M times a vector whose k components are linear forms (bitmasks)."""
    out = []
    for r in rows(M, k):
        m = 0
        for c in range(k):
            if (r >> c) & 1:
                m ^= forms[c]
        out.append(m)
    return out


_FORMS = {}


def forms(n, k):
    """Linear forms for sigma(h) and beta(h, e_j) in the unknowns
    sigma(e_i)_c and beta(e_i, e_j)_c (i < j)."""
    if (n, k) in _FORMS:
        return _FORMS[(n, k)]
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    pidx = {p: t for t, p in enumerate(pairs)}
    nv = n * k + len(pairs) * k

    def bvar(i, j, c):
        if i > j:
            i, j = j, i
        return 1 << (n * k + pidx[(i, j)] * k + c)

    sig = []
    for h in range(1 << n):
        bits = [i for i in range(n) if (h >> i) & 1]
        f = []
        for c in range(k):
            m = 0
            for i in bits:
                m ^= 1 << (i * k + c)
            for a in range(len(bits)):
                for b in range(a + 1, len(bits)):
                    m ^= bvar(bits[a], bits[b], c)
            f.append(m)
        sig.append(f)
    bet = []
    for h in range(1 << n):
        row = []
        for j in range(n):
            f = []
            for c in range(k):
                m = 0
                for i in range(n):
                    if i != j and (h >> i) & 1:
                        m ^= bvar(i, j, c)
                f.append(m)
            row.append(f)
        bet.append(row)
    _FORMS[(n, k)] = (nv, sig, bet, pairs)
    return _FORMS[(n, k)]


def nullspace(piv, nv):
    keys = sorted(piv)
    for p in keys:
        for q in keys:
            if q != p and (piv[q] >> p) & 1:
                piv[q] ^= piv[p]
    basis = []
    for f in range(nv):
        if f in piv:
            continue
        x = 1 << f
        for p in keys:
            if (piv[p] >> f) & 1:
                x |= 1 << p
        basis.append(x)
    return basis


def equations(k, Mh, n):
    nv, sig, bet, _ = forms(n, k)
    I = identity(k)
    eqs = []
    for h in range(1 << n):
        for j in range(n):
            lhs = apply(Mh[1 << j], sig[h], k)
            rhs = apply(I ^ Mh[h], bet[h][j], k)
            eqs.extend(lhs[r] ^ rhs[r] for r in range(k))
    return eqs


def span_table(basis):
    T = [0] * (1 << len(basis))
    for h in range(1, len(T)):
        t = (h & -h).bit_length() - 1
        T[h] = T[h & (h - 1)] ^ basis[t]
    return T


def analyze(k, basis, cap=20):
    n = len(basis)
    nv, sig, _, pairs = forms(n, k)
    I = identity(k)
    Mh = span_table(basis)
    piv = {}
    for e in equations(k, Mh, n):
        insert(piv, e)
    rank = len(piv)
    null = nullspace(piv, nv)
    # signature of a solution x: bit h*k + c is sigma(h)_c
    pairs_sx = []
    for x in null:
        s = 0
        for h in range(1 << n):
            for c in range(k):
                if parity(sig[h][c] & x):
                    s |= 1 << (h * k + c)
        pairs_sx.append((s, x))
    ind = []
    pv = {}
    for s, x in pairs_sx:
        while s:
            hb = s.bit_length() - 1
            if hb in pv:
                ps, px = pv[hb]
                s ^= ps
                x ^= px
            else:
                pv[hb] = (s, x)
                ind.append((s, x))
                break
    N = [h for h in range(1, 1 << n) if invertible(I ^ Mh[h], k)]
    N_mask = 0
    for h in N:
        N_mask |= 1 << (h * k)
    eigen_killed = any(invertible(Mh[h], k) for h in N)
    res = {"n": n, "rank": rank, "nullity": len(null), "sigma_dim": len(ind),
           "N_size": len(N), "eigen_killed": eigen_killed, "sigma0_ok": not N}
    d = len(ind)
    limit = 12 if eigen_killed else cap
    if d > limit:
        res["e3"] = False if eigen_killed else None
        return res
    s = 0
    x = 0
    found = None
    for i in range(1, 1 << d):
        t = (i & -i).bit_length() - 1
        s ^= ind[t][0]
        x ^= ind[t][1]
        nz = 0
        for c in range(k):
            nz |= s >> c
        if (nz & N_mask) == N_mask:
            found = x
            break
    res["e3"] = found is not None
    if found is not None:
        res["witness"] = {
            "sigma_basis": [sum(((found >> (i * k + c)) & 1) << c for c in range(k))
                            for i in range(n)],
            "beta_basis": {f"{i},{j}": sum(((found >> (n * k + t * k + c)) & 1) << c
                                           for c in range(k))
                           for t, (i, j) in enumerate(pairs)},
        }
    return res


def check_solution(k, basis, x):
    """Every equation of (c) vanishes on x (used by the tests)."""
    Mh = span_table(basis)
    return all(parity(e & x) == 0 for e in equations(k, Mh, len(basis)))


def gl(k):
    return [M for M in range(1 << (k * k)) if invertible(M, k)]


def conj_tables(k):
    G = gl(k)
    I = identity(k)
    tabs = []
    for P in G:
        Pi = next(Q for Q in G if matmul(P, Q, k) == I)
        tabs.append([matmul(matmul(P, M, k), Pi, k) for M in range(1 << (k * k))])
    return tabs


def w_key(a, b):
    return tuple(sorted((a, b, a ^ b)))


def orbit_reps(k):
    """Conjugacy-class representatives of 2-dim subspaces W of M_k(F_2)."""
    tabs = conj_tables(k)
    size = 1 << (k * k)
    seen = set()
    reps = []
    for a in range(1, size):
        for b in range(a + 1, size):
            key = w_key(a, b)
            if key in seen:
                continue
            orb = {w_key(t[a], t[b]) for t in tabs}
            seen |= orb
            reps.append(([key[0], key[1]], len(orb)))
    return reps


def perp_basis(W, k):
    piv = {}
    basis = []
    for M in range(1 << (k * k)):
        if all(parity(M & w) == 0 for w in W) and insert(piv, M):
            basis.append(M)
    return basis


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--cap", type=int, default=20)
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    t0 = time.time()
    k = 3
    reps = orbit_reps(k)
    results = []
    for W, size in reps:
        V = perp_basis(W, k)
        r = analyze(k, V, args.cap)
        r.update(W=W, V_basis=V, orbit_size=size)
        results.append(r)
    summary = {
        "k": k,
        "orbits": len(results),
        "subspaces": sum(r["orbit_size"] for r in results),
        "eigen_killed_orbits": sum(r["eigen_killed"] for r in results),
        "e3_true_orbits": sum(r["e3"] is True for r in results),
        "e3_false_orbits": sum(r["e3"] is False for r in results),
        "undecided_orbits": sum(r["e3"] is None for r in results),
        "inconsistent": sum(r["eigen_killed"] and r["e3"] is True for r in results),
        "max_sigma_dim": max(r["sigma_dim"] for r in results),
        "seconds": round(time.time() - t0, 1),
    }
    with open(os.path.join(args.out_dir, "z4_k3_results.json"), "w") as f:
        json.dump({"summary": summary, "orbits": results}, f, indent=1)
    print(json.dumps(summary, indent=1))
    for r in results:
        if r["e3"] is not False:
            print("candidate or undecided:", json.dumps(r))


if __name__ == "__main__":
    main()
