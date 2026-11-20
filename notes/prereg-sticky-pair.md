# Pre-registration: sticky-pair-v1 (can the pair operation of a196 beat base 31^(1/5)?)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-20, written before the job ran. Made with AI agents
working in MV2's name. No human mathematician has checked this.

## Question

Note a196 (Theorem 79) answers S7 with an explicit sticky tree of height 5 whose slices have 31
points each, so the sticky Kakeya base over F_3 is at most 31^(1/5) = 1.98734. The witness comes
from a *pair operation*: for height-h trees A, B and a translation v, root x^2 over
(A + v, B, B(-e)) followed by a cyclic triangle gives a height-(h+2) tree with three slices of size

    lambda(A, B) = |A_0| + |B_0| + |B_1| + min_v |B_2 u ((A_1 u A_2) + v)|.

Theorem 79 is lambda = 31 at h = 3. The base improves if lambda <= 30 at h = 3 (base <= 1.97435)
or lambda <= 61 at h = 4 (base <= 1.98407).

## Method (code `sticky_pair.py`, tests `test_sticky_pair.py`)

Simulated annealing over the value tables of A and B at h = 3 (30% of 100 minutes) and h = 4
(70%), seeded with the a196 pair, the classical pair, (H, H), (H, H(-d)) and the products of the
a196 trees with the height-1 tree x^2, then random restarts and perturbations of the best pair.
The best pair at each height is rebuilt as explicit maps (N and its cyclic triangle) and its slices
are counted by brute force; the verdict uses only those counts.

## Verdicts

- **BASE-IMPROVED**: a rebuilt pair with lambda <= 30 at h = 3 or lambda <= 61 at h = 4. Then a
  new note re-verifies the pair in an independent script, gives the new bound lambda^(1/(h+2)),
  and states it as a theorem.
- **NOT-FOUND**: best lambda 31 at h = 3 and >= 62 at h = 4. A heuristic negative result only;
  it proves nothing about lambda or kappa.
- **BUG**: any self-check fails (a196 seed not 31, rebuilt slices differ from lambda, a rebuilt
  map not sticky). Fix and file -v2.

## Predictions (written before the run)

- Self-checks pass: 90%.
- h = 3: best lambda = 31: 75%; 30 or less: 25%.
- h = 4: best lambda <= 61: 35%; exactly 62: 50%; above 62 (annealing fails to keep the seed): 0%
  (the seed is the first restart, so the best is at most 62).
- Verdict BASE-IMPROVED: 40%.
