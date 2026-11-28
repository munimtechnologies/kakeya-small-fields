# k34: is the 28-point Kakeya set of F_4^3 the smallest?

Made with AI agents working in MV2's name (MV2 of Munim, Inc., mv2@munimtech.com).
Not yet checked by a human mathematician. Code Apache-2.0, text CC BY 4.0.

## The question

A Kakeya set in F_q^3 contains a full line in each of the q^2 + q + 1 directions. For F_4^3
the best bounds before this work were

* lower: 21, from Bukh and Chao's density bound q^n / (2 - 1/q)^(n-1)
  ([arXiv:2108.00074](https://arxiv.org/abs/2108.00074));
* upper: 28, from the even-q construction of Kopparty, Saraf and Sudan
  (2^(1-n) q^n + (1 - 2^(1-n)) q^(n-1) = 16 + 12): the plane t = 0 together with the
  points (b t + b^2, c t + c^2, t), t != 0 (verify.kss_set_q4).

Lund, Saraf and Wolf ([arXiv:1609.01048](https://arxiv.org/abs/1609.01048)) note that exact
Kakeya numbers are known only in the plane (Blokhuis-Mazzocca) and, for q = 2, trivially. Our
own [kakeya-small-fields](https://github.com/munimtechnologies/kakeya-small-fields) v1.x gave
K(3, 3) = 13 by exhaustive search. Integer programs (kq/, HiGHS, 2026-11-28) did not close
F_4^3: their dual bounds after about 250-480 s were 15, 17 and 19.

This folder asks the computer to decide whether some Kakeya set of F_4^3 has at most 27
points. If none does, K(3, 4) = 28 exactly, the first exact Kakeya number in three dimensions
over a field with more than three elements.

## The reduction (hand argument; checked by the controls below, not by a human)

Let K be a Kakeya set with |K| <= T - 1 (T = 28). Shrinking K we may assume it is a union of
one line per direction.

1. **A smallest plane.** Let P_0 be a plane with the fewest points of K among all 84 planes,
   m = |K cap P_0|. Move it to z = 0 by an affine map. The four planes z = c partition K, each
   has at least m points, so 4m <= |K| <= 27 and **m <= 6**.
2. **Transversal lines.** The chosen line of direction (u, 1) is {(f(u) + t u, t)}. It meets
   z = c in f(u) + c u, so K_c contains S_c = {f(u) + c u : u in F_4^2}. S_0 is the image of f;
   r = |S_0| <= m.
3. **Horizontal lines.** The five directions (d, 0) have their lines inside single planes, so
   |K| = sum_c |S_c cup H_c|, where H_c is the union of the horizontal lines placed in z = c.
4. **Pruning bound.** Since |K_c| >= m >= r for all c,
   |K| >= r + sum_{c != 0} max(|S_c|, r). During the search, an unassigned direction whose
   possible points in plane c are all new adds a new point there, and one new point can be hit
   by at most r directions (one from each point of S_0), so |S_c| grows by at least
   ceil(N_c / r) more.
5. **Symmetry.** Maps (x, y, z) -> (A(x, y) + g, z) and the Frobenius map fix z = 0, so S_0 can
   be taken to be an orbit representative under AGL(2, 4) x Frobenius (order 5760). The shear
   (x, y, z) -> ((x, y) + z b, z) fixes every plane z = c and plane 0 pointwise and turns f into
   u -> f(u - b), so we may take f(0) = S_0[0].
6. **Leaves.** For a complete f the horizontal lines are placed optimally by an exact dynamic
   program over the 4^5 ways to put the five directions into the four planes (and, inside each
   plane, all line choices). That gives the exact smallest |K| for this f. Any leaf below T is an
   explicit Kakeya set below 28, which the independent checker verify.py must confirm.

So: **if the search finishes for every r <= 6 and every orbit representative of size r, and no
leaf is below 28, then every Kakeya set in F_4^3 has at least 28 points.**

Two cases also follow by hand and serve as checks:

* r = 1: f is constant, every other slice is a whole plane: |K| >= 49.
* r = 2, S_0 = {p, p'}: let U be the t directions through p. In plane c != 0 the points p + cU
  and p' + c U^c meet only where u + v = e_c = (p + p')/c, and the e_c are the non-zero vectors
  of the 2-dimensional F_2-space V = F_4 (p + p'). Summing overlaps over V,
  sum_{e in V} |U cap (U + e)| = sum over the 4 cosets C of V of |U cap C|^2 >= t^2 / 4, so the
  three planes together save at most 4t - t^2/4 <= 16 points out of 48: |K| >= 2 + 32 = 34.
* If K contains a whole plane, the other three slices pairwise satisfy |K_c| |K_c'| >= 16 (the
  16 transversal lines give distinct pairs of points), so they sum to at least 12: |K| >= 28.

## Controls (test_k34_unit.py)

* Field axioms for F_3, F_4, F_5; the independent checker's F_4 (built from logarithms) agrees.
* The generated groups have orders 432 = |AGL(2, 3)| and 5760 = |AGL(2, 4)| x 2; orbit sizes add
  up to the binomial coefficients; 1, 1, 2 orbits of 1-, 2-, 3-subsets of AG(2, 4).
* The KSS set has 28 points and is Kakeya; its f (u -> (u1^2, u2^2)) evaluated by the leaf code
  gives exactly 28, and the realised set passes the checker.
* **The same search over F_3 reproduces K(3, 3) = 13:** asked for sets below 13 it finds none,
  and asked for sets below 14 it finds 13-point sets, each confirmed by the checker.
* Positive control in F_4 (gaterun.positive_control): asked for sets below 29 on the orbit of
  the 2 x 2 slice of the KSS set, the search must reach a 28-point set.

## Running it

The search is resumable (slices.run_queue): items are (r, S_0, branch prefix); an item that
runs past 150 s is split into its r children. Progress is kept in
results/progress-q4-T28.json ("complete": true only when nothing is pending).
