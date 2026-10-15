"""Numerical checks of Lemma 4 (README section 7) and Theorem 4 (README section 8).

Self-contained, pure Python. By MV2 of Munim, Inc.; researched and written with AI agents working
in MV2's name. Code Apache-2.0."""
import math
import random
import unittest


def H(p):
    return -sum(x * math.log2(x) for x in p if x > 0)


def slices(k0, k1):
    """M_t(z) = (k0(z) + k1(z - t)) / 2 on F_3, for t = 0, 1, 2."""
    return [[(k0[z] + k1[(z - t) % 3]) / 2 for z in range(3)] for t in range(3)]


def worst(k0, k1):
    return max(H(M) for M in slices(k0, k1))


def simplex(N):
    return [(i / N, j / N, (N - i - j) / N) for i in range(N + 1) for j in range(N + 1 - i)]


def F(alpha, g):
    """The lower bound for H(M_t) in case (iii) of the proof of Lemma 4."""
    return H([(alpha + g) / 2, (2 - alpha - 2 * g) / 2, g / 2])


def digits(q, k, v):
    return [(v // q ** i) % q for i in range(k)]


def number(q, ds):
    return sum(d * q ** i for i, d in enumerate(ds))


def score(q, k, P):
    """S(P) = sum over t and over the fibres of x -> P(x) + t x of s log2 s (P: list of codes)."""
    total = 0.0
    for t in range(q):
        counts = {}
        for x in range(q ** k):
            y = tuple((p + t * d) % q for p, d in zip(digits(q, k, P[x]), digits(q, k, x)))
            counts[y] = counts.get(y, 0) + 1
        total += sum(c * math.log2(c) for c in counts.values() if c > 1)
    return total


def threshold(q, k):
    return k * (q - 1) * q ** k


def compatible_map(q, k, l, rng):
    """A random P with P(x + w) - P(x) in W = span(e_1, ..., e_l) for all w in W: the last k - l
    coordinates of P(x) depend only on the last k - l coordinates of x."""
    n = q ** k
    low = {}
    P = []
    for x in range(n):
        xs = digits(q, k, x)
        key = tuple(xs[l:])
        if key not in low:
            low[key] = [rng.randrange(q) for _ in range(k - l)]
        P.append(number(q, [rng.randrange(q) for _ in range(l)] + low[key]))
    return P


def affine_map(q, k, A, b):
    out = []
    for x in range(q ** k):
        xs = digits(q, k, x)
        out.append(number(q, [(sum(A[i][j] * xs[j] for j in range(k)) + b[i]) % q
                              for i in range(k)]))
    return out


class Lemma4(unittest.TestCase):
    def test_point_masses_give_exactly_one(self):
        for a in range(3):
            for b in range(3):
                k0 = [1.0 if z == a else 0.0 for z in range(3)]
                k1 = [1.0 if z == b else 0.0 for z in range(3)]
                self.assertAlmostEqual(worst(k0, k1), 1.0, places=12)

    def test_grid(self):
        pts = simplex(12)
        low = min(worst(k0, k1) for k0 in pts for k1 in pts)
        self.assertAlmostEqual(low, 1.0, places=12)

    def test_random_and_local(self):
        rng = random.Random(3)

        def rand_dist():
            w = [rng.random() ** 3 for _ in range(3)]
            s = sum(w)
            return [x / s for x in w]

        for _ in range(20000):
            self.assertGreaterEqual(worst(rand_dist(), rand_dist()), 1 - 1e-12)
        # near the point masses, where the minimum is attained
        for _ in range(5000):
            e = [rng.random() * 0.05 for _ in range(4)]
            k0 = [1 - e[0] - e[1], e[0], e[1]]
            k1 = [e[2], 1 - e[2] - e[3], e[3]]
            self.assertGreaterEqual(worst(k0, k1), 1 - 1e-12)

    def test_case_iii_bound(self):
        self.assertAlmostEqual(F(1, 0), 1.0, places=12)
        self.assertAlmostEqual(F(1, 1 / 3), H([2 / 3, 1 / 6, 1 / 6]), places=12)
        self.assertAlmostEqual(F(1, 1 / 3), 1.2516, places=4)
        self.assertAlmostEqual(F(2 / 3, 1 / 3), H([1 / 2, 1 / 3, 1 / 6]), places=12)
        self.assertAlmostEqual(F(2 / 3, 1 / 3), 1.4591, places=4)
        N = 300
        for i in range(N + 1):
            alpha = 2 / 3 + i / (3 * N)
            for j in range(N + 1):
                g = (1 - alpha) + j * (1 / 3 - (1 - alpha)) / N
                self.assertGreaterEqual(F(alpha, g), 1 - 1e-12)

    def test_case_iii_bound_holds_for_actual_slices(self):
        # whenever every symbol z_t of case (iii) is 0, the slice with the smallest k1(-t) is >= F
        rng = random.Random(8)
        checked = 0
        for _ in range(40000):
            alpha = 2 / 3 + rng.random() / 3
            b1 = rng.random() * (1 - alpha)
            k0 = [alpha, b1, 1 - alpha - b1]
            w = [rng.random() for _ in range(3)]
            k1 = [x / sum(w) for x in w]
            Ms = slices(k0, k1)
            if not all(M[0] > 0.5 for M in Ms):
                continue
            checked += 1
            g = min(k1)
            t = [t for t in range(3) if k1[(-t) % 3] == g][0]
            self.assertGreater(alpha, 2 / 3)
            self.assertGreater(g, 1 - alpha)
            self.assertGreaterEqual(H(Ms[t]), F(alpha, g) - 1e-12)
            self.assertGreaterEqual(F(alpha, g), 1 - 1e-12)
        self.assertGreater(checked, 1000)

    def test_symmetric_two_symbol_set(self):
        # Theorem 3(b): the vectors of F_3^n using at most two symbols, 3 * 2^n - 3 of them,
        # form a Kakeya set (the line through u*u in direction u); its base 2 is optimal.
        from itertools import product
        for n in range(1, 5):
            vs = list(product(range(3), repeat=n))
            K = {v for v in vs if len(set(v)) <= 2}
            self.assertEqual(len(K), 3 * 2 ** n - 3)
            for u in vs:
                if any(u):
                    a = tuple(x * x % 3 for x in u)
                    for t in range(3):
                        self.assertIn(tuple((ai + t * ui) % 3 for ai, ui in zip(a, u)), K)
            if n % 2 == 0:
                self.assertLessEqual(2 ** n / (n + 1) ** 3, len(K))


class Theorem4(unittest.TestCase):
    def test_compatible_maps_never_beat_k2(self):
        rng = random.Random(1)
        for q, trials in [(2, 300), (3, 1500), (5, 300)]:
            for _ in range(trials):
                P = compatible_map(q, 2, 1, rng)
                self.assertLessEqual(score(q, 2, P), threshold(q, 2) + 1e-9)

    def test_compatible_maps_can_reach_the_threshold(self):
        # the coordinatewise squares are compatible with both coordinate axes
        q, k = 3, 2
        sq = [number(q, [d * d % q for d in digits(q, k, x)]) for x in range(q ** k)]
        self.assertAlmostEqual(score(q, k, sq), threshold(q, k), places=9)

    def test_affine_maps(self):
        # S(Ax + b) <= k q^k log2 q, which is below k (q - 1) q^k for q >= 3
        from itertools import product
        q, k = 3, 2
        for entries in product(range(q), repeat=4):
            A = [list(entries[:2]), list(entries[2:])]
            s = score(q, k, affine_map(q, k, A, [1, 2]))
            self.assertLessEqual(s, k * q ** k * math.log2(q) + 1e-9)
            self.assertLess(s, threshold(q, k))
        rng = random.Random(4)
        for q, k in [(5, 2), (3, 3), (2, 3)]:
            for _ in range(60):
                A = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
                b = [rng.randrange(q) for _ in range(k)]
                s = score(q, k, affine_map(q, k, A, b))
                self.assertLessEqual(s, k * q ** k * math.log2(q) + 1e-9)
                self.assertLessEqual(s, threshold(q, k) + 1e-9)

    def test_affine_bound_is_attained(self):
        # A = 0 puts slice 0 in one point: S = q^k * k log2 q
        q, k = 3, 2
        s = score(q, k, affine_map(q, k, [[0, 0], [0, 0]], [0, 0]))
        self.assertAlmostEqual(s, k * q ** k * math.log2(q), places=9)


if __name__ == "__main__":
    unittest.main()
