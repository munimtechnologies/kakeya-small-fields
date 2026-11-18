"""Tests for note a174 (frames.py). MV2 of Munim, Inc. Apache-2.0.
Made with AI agents working in MV2's name. Standard library only, self-contained.
Every assertion checks a fact proved in a174 (or the exact identities its proofs use).
Every entropy is computed by brute force over every point of F_q^k (q prime)."""
import itertools
import math
import random
import unittest
from fractions import Fraction

import frames as fr


def _rand_matrix(rng, q, k, density=1.0):
    return [[(rng.randrange(1, q) if rng.random() < density else 0) for _ in range(k)]
            for _ in range(k)]


def _rand_sc_matrix(rng, q, k):
    while True:
        M = _rand_matrix(rng, q, k, density=rng.choice([0.3, 0.5, 0.8]))
        for i in range(k):
            M[i][i] = rng.randrange(q)
        if fr.strongly_connected(M):
            return M


def _mat_inv(A, q):
    k = len(A)
    aug = [list(A[i]) + [1 if j == i else 0 for j in range(k)] for i in range(k)]
    for c in range(k):
        piv = next((i for i in range(c, k) if aug[i][c] % q), None)
        if piv is None:
            return None
        aug[c], aug[piv] = aug[piv], aug[c]
        inv = pow(aug[c][c], q - 2, q)
        aug[c] = [(x * inv) % q for x in aug[c]]
        for i in range(k):
            if i != c and aug[i][c] % q:
                f = aug[i][c]
                aug[i] = [(a - f * b) % q for a, b in zip(aug[i], aug[c])]
    return [row[k:] for row in aug]


def _mat_mul(A, B, q):
    return [[sum(A[i][l] * B[l][j] for l in range(len(B))) % q for j in range(len(B[0]))]
            for i in range(len(A))]


def _rand_invertible(rng, q, k):
    while True:
        A = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
        if fr.rank_mod(A, q) == k:
            return A


SIZES_SMALL = [(3, 2), (3, 3), (3, 4), (3, 5), (5, 2), (5, 3), (7, 2)]
SIZES = [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (5, 2), (5, 3), (5, 4), (7, 2), (7, 3)]


class TestTheorem58PairFormula(unittest.TestCase):
    """E N = sum_T q^-|T| V(T), V(T) <= (q-1)^(|T| - rank M_(T^c,T)); strongly connected bound."""

    def test_pair_identity_and_V_bound(self):
        rng = random.Random(58)
        for q, k in SIZES_SMALL:
            for _ in range(5):
                M = _rand_matrix(rng, q, k, density=rng.choice([0.2, 0.5, 1.0]))
                for i in range(k):
                    M[i][i] = rng.randrange(q)
                pts = fr.all_points(q, k)
                EN = fr.mean_fibre(pts, fr.frame_map(q, M))
                self.assertEqual(EN, fr.pair_formula(q, M))
                tot = Fraction(0)
                for m in range(k + 1):
                    for T in itertools.combinations(range(k), m):
                        T = list(T)
                        Tc = [i for i in range(k) if i not in T]
                        V = fr.V_count(q, M, T)
                        rk = fr.rank_mod(fr.submatrix(M, Tc, T), q) if Tc and T else 0
                        self.assertLessEqual(V, (q - 1) ** (len(T) - rk))
                        tot += Fraction(V, q ** len(T))
                self.assertEqual(EN, tot)

    def test_strongly_connected_bound(self):
        rng = random.Random(580)
        for q, k in SIZES:
            self.assertLess(math.log2(fr.phi_bound(q, k)), k * (q - 1) / q - 1e-3)
            for _ in range(6):
                M = _rand_sc_matrix(rng, q, k)
                pts = fr.all_points(q, k)
                F = fr.frame_map(q, M)
                H = fr.fibre_entropy(pts, F)
                EN = fr.mean_fibre(pts, F)
                self.assertLessEqual(H, math.log2(EN) + 1e-12)
                self.assertLessEqual(float(EN), fr.phi_bound(q, k) + 1e-12)
                self.assertLess(H, k * (q - 1) / q - 1e-3)

    def test_cycles(self):
        rng = random.Random(581)
        for q, k in SIZES:
            M = [[0] * k for _ in range(k)]
            for i in range(k):
                M[i][(i + 1) % k] = rng.randrange(1, q)
                M[i][i] = rng.randrange(q)
            pts = fr.all_points(q, k)
            F = fr.frame_map(q, M)
            EN = fr.mean_fibre(pts, F)
            self.assertEqual(EN, 1 + Fraction(q - 1, q) ** k)
            H = fr.fibre_entropy(pts, F)
            self.assertLessEqual(H, math.log2(1 + ((q - 1) / q) ** k) + 1e-12)
            self.assertLess(H, 1.0)


class TestK0(unittest.TestCase):
    def test_values(self):
        self.assertEqual(fr.K0(3), 14)
        self.assertEqual(fr.K0(5), 41)
        self.assertEqual(fr.K0(7), 71)
        # the defining inequality, checked directly at the ends
        self.assertLess(math.log2(fr.phi_bound(3, 14)), 14 * 2 / 3)
        self.assertGreater(math.log2(fr.phi_bound(3, 15)), 15 * 2 / 3)


class TestChainRuleAndNormalForm(unittest.TestCase):
    def test_diagonal_is_free(self):
        rng = random.Random(66)
        for q, k in SIZES_SMALL:
            M = _rand_matrix(rng, q, k, density=0.6)
            D = [row[:] for row in M]
            for i in range(k):
                D[i][i] = (D[i][i] + rng.randrange(q)) % q
            self.assertAlmostEqual(fr.frame_entropy(q, M), fr.frame_entropy(q, D), places=12)

    def test_scc_chain_rule(self):
        rng = random.Random(661)
        for q, k in SIZES:
            for _ in range(5):
                perm = list(range(k))
                rng.shuffle(perm)
                cut = sorted(rng.sample(range(1, k), rng.randrange(1, k))) if k > 1 else []
                block = {}
                b = 0
                for pos in range(k):
                    if b < len(cut) and pos >= cut[b]:
                        b += 1
                    block[perm[pos]] = b
                M = [[0] * k for _ in range(k)]
                for i in range(k):
                    for j in range(k):
                        if block[i] <= block[j] and rng.random() < 0.6:
                            M[i][j] = rng.randrange(1, q)
                H = fr.frame_entropy(q, M)
                parts = 0.0
                for C in fr.sccs(M):
                    parts += fr.frame_entropy(q, fr.submatrix(M, C, C))
                self.assertLessEqual(H, parts + 1e-12)
                self.assertLessEqual(H, fr.scc_bound(q, M) + 1e-12)
                self.assertLessEqual(H, k * (q - 1) / q + 1e-12)


class TestCorollary582(unittest.TestCase):
    """P(x) = A((Sx) o (Sx)) + Lx: slice t has the fibres of the frame with M_t = A^-1 (L+tI) S^-1."""

    def test_frame_equivalent_maps(self):
        rng = random.Random(582)
        for q, k in [(3, 2), (3, 3), (3, 4), (5, 2), (5, 3), (7, 2)]:
            for _ in range(3):
                A = _rand_invertible(rng, q, k)
                S = _rand_invertible(rng, q, k)
                L = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
                Ai, Si = _mat_inv(A, q), _mat_inv(S, q)
                pts = fr.all_points(q, k)
                for t in range(q):
                    def At(x, t=t):
                        u = [sum(S[i][j] * x[j] for j in range(k)) % q for i in range(k)]
                        sq = [u[i] * u[i] for i in range(k)]
                        return tuple((sum(A[i][j] * sq[j] for j in range(k))
                                      + sum(L[i][j] * x[j] for j in range(k)) + t * x[i]) % q
                                     for i in range(k))
                    Lt = [[(L[i][j] + (t if i == j else 0)) % q for j in range(k)]
                          for i in range(k)]
                    Mt = _mat_mul(_mat_mul(Ai, Lt, q), Si, q)
                    H = fr.fibre_entropy(pts, At)
                    self.assertAlmostEqual(H, fr.frame_entropy(q, Mt), places=12)
                    self.assertLessEqual(H, k * (q - 1) / q + 1e-12)


class TestLowRank(unittest.TestCase):
    def test_rank_one_upper_and_lower(self):
        rng = random.Random(59)
        theta = lambda q: (q + 1) / (2 * q)
        for q, k in SIZES:
            for _ in range(8):
                u = [rng.randrange(q) if rng.random() < 0.7 else 0 for _ in range(k)]
                v = [rng.randrange(q) if rng.random() < 0.7 else 0 for _ in range(k)]
                M = fr.uvT(q, [[x] for x in u], [[x] for x in v])
                for i in range(k):
                    M[i][i] = (M[i][i] + rng.randrange(q)) % q
                H = fr.frame_entropy(q, M)
                self.assertLessEqual(H, k * (q - 1) / q + 1e-12)
                self.assertGreaterEqual(H, k * (q - 1) / q - (q - 1) - 1e-12)
                U = [i for i in range(k) if u[i]]
                V = [i for i in range(k) if v[i]]
                if len(U) >= 2 and set(U) & set(V):
                    bound = (k - 1) * (q - 1) / q + math.log2(
                        1 + (q - 1) / q * theta(q) ** (len(U) - 1))
                    self.assertLessEqual(H, bound + 1e-12)
                    self.assertLess(bound, k * (q - 1) / q - 1e-3)

    def test_rank_one_pointwise_lower(self):
        rng = random.Random(591)
        for q, k in [(3, 3), (3, 4), (3, 5), (5, 3), (7, 2)]:
            for _ in range(4):
                u = [rng.randrange(q) for _ in range(k)]
                v = [rng.randrange(q) for _ in range(k)]
                M = fr.uvT(q, [[x] for x in u], [[x] for x in v])
                pts = fr.all_points(q, k)
                N = fr.fibre_sizes(pts, fr.frame_map(q, M))
                for y in pts:
                    Z = fr.zero_sum_subsets(q, y, v)
                    s = sum(1 for x in y if x)
                    self.assertGreaterEqual(N[y], Z)
                    self.assertGreaterEqual(Z, 2 ** (s - (q - 1)))

    def test_all_ones_family(self):
        for q, k in [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (5, 3), (5, 4), (7, 3)]:
            for c in range(1, q):
                M = [[c] * k for _ in range(k)]
                H = fr.frame_entropy(q, M)
                th = (q + 1) / (2 * q)
                up = (k - 1) * (q - 1) / q + math.log2(1 + (q - 1) / q * th ** (k - 1))
                self.assertLessEqual(H, up + 1e-12)
                self.assertGreaterEqual(H, k * (q - 1) / q - (q - 1) - 1e-12)

    def test_low_rank_criterion_and_averaging(self):
        rng = random.Random(60)
        for q, k, r in [(3, 3, 2), (3, 4, 2), (3, 5, 2), (3, 6, 2), (5, 3, 2), (5, 4, 2),
                        (3, 4, 3), (3, 5, 1), (7, 3, 1)]:
            done = 0
            while done < 4:
                U = [[rng.randrange(q) for _ in range(r)] for _ in range(k)]
                V = [[rng.randrange(q) for _ in range(r)] for _ in range(k)]
                J = fr.find_J(q, V)
                if J is None:
                    continue
                done += 1
                M = fr.uvT(q, U, V)
                pts = fr.all_points(q, k)
                N = fr.fibre_sizes(pts, fr.frame_map(q, M))
                H = fr.fibre_entropy(pts, fr.frame_map(q, M))
                self.assertLessEqual(H, fr.low_rank_bound(q, U, J) + 1e-12)
                # pointwise averaging inequality: E_{y_J} N(y) <= 2^{s'} + beta(y_{J^c})
                C = [i for i in range(k) if i not in J]
                for yC in itertools.product(range(q), repeat=len(C)):
                    tot = 0
                    for yJ in itertools.product(range(q), repeat=len(J)):
                        y = [0] * k
                        for a, i in enumerate(C):
                            y[i] = yC[a]
                        for a, i in enumerate(J):
                            y[i] = yJ[a]
                        tot += N[tuple(y)]
                    avg = Fraction(tot, q ** len(J))
                    sprime = sum(1 for x in yC if x)
                    self.assertLessEqual(avg, 2 ** sprime + fr.beta_pointwise(q, U, J, yC, C))
                # with a diagonal added the entropy (hence the bound) is unchanged
                D = [row[:] for row in M]
                for i in range(k):
                    D[i][i] = (D[i][i] + rng.randrange(q)) % q
                self.assertAlmostEqual(fr.frame_entropy(q, D), H, places=12)


class TestTheorem57(unittest.TestCase):
    def test_rank_profile_bound_random_algebras(self):
        rng = random.Random(57)
        for q, k in [(3, 2), (3, 3), (5, 2), (5, 3), (7, 2)]:
            for _ in range(3):
                C = [[None] * k for _ in range(k)]
                for i in range(k):
                    for j in range(i, k):
                        C[i][j] = C[j][i] = tuple(rng.randrange(q) for _ in range(k))
                L = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
                rh = fr.rho(C, q)
                pts = fr.all_points(q, k)
                for t in range(q):
                    A = fr.slice_map(C, L, t, q)
                    self.assertLessEqual(fr.mean_fibre(pts, A), rh)
                    self.assertLessEqual(fr.fibre_entropy(pts, A), math.log2(rh) + 1e-12)

    def test_planar_fields_and_twisted_fields(self):
        rng = random.Random(571)
        cases = [(3, 2, 0), (3, 3, 0), (5, 2, 0), (7, 2, 0), (3, 3, 1)]
        for p, k, tw in cases:
            C = fr.field_structure(p, k, tw)
            self.assertTrue(fr.is_planar(C, p))
            self.assertEqual(fr.rho(C, p), 2 - Fraction(1, p ** k))
            for _ in range(2):
                L = [[rng.randrange(p) for _ in range(k)] for _ in range(k)]
                lam = fr.Lambda(C, L, p)
                bound = p * math.log2(2 - p ** (-k))
                self.assertLessEqual(lam, bound + 1e-9)
                self.assertLess(bound, p)
                self.assertLess(p, k * (p - 1) + 1e-12)
        # x^(q+1) on F_(q^2) is the norm form: not planar (k/gcd(i,k) = 2 is even)
        self.assertFalse(fr.is_planar(fr.field_structure(3, 2, 1), 3))

    def test_field_multiplication_is_commutative_and_unital(self):
        for p, k in [(3, 2), (3, 3), (5, 2)]:
            C = fr.field_structure(p, k, 0)
            mul = fr.algebra_mul(C, p)
            one = tuple(1 if s == 0 else 0 for s in range(k))
            for x in fr.all_points(p, k):
                self.assertEqual(mul(one, x), x)
            for x, y in itertools.product(fr.all_points(p, k), repeat=2):
                self.assertEqual(mul(x, y), mul(y, x))


if __name__ == "__main__":
    unittest.main()
