# Pre-registration: sticky-nest-v1 (quadratic-root pair families at height 4)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-21, written before the job runs.
Made with AI agents working in MV2's name; no human mathematician has checked this note.
Code: `sticky_nest.py`, `test_sticky_nest.py` (Apache-2.0). Text: CC BY 4.0.

## Question

Can a height-6 sticky Kakeya tree over F_3 beat the base 31^(1/5) = 1.98734 of note a196?
For height-4 trees A, B let lambda(A, B) = |A_0| + |B_0| + |B_1| + |B_2 u A_1 u A_2|. By Lemma 167 the
tree N = root x^2 over (A, B, B(-e)) has |N_0| + |N_1 u N_2| = lambda(A, B), and its cyclic triangle
(Proposition 89) has three slices of that size, so a pair with lambda <= 61 gives
beta_s <= 61^(1/6) = 1.98407. Known: 60 <= kappa_5 <= lambda_4 <= 62 (the pair (H, H) gives 62).
The unrestricted CP-SAT model of lambda_4 (sticky-l4-v1, note a199) found nothing <= 61 in about three
hours and proved only 28, so this job searches smaller, structured families exactly.

## Families

- **F2**: A and B both have a quadratic root map x -> x^2 + c; their three children are free.
- **F1**: F2, and A = x^2 over (D, E, E(-e)) (A's child 2 is child 1 reflected), as in a196's tree H.
- **F0**: F1, and B = x^2 over (Y, X, Z) with X(e) = Y(-e) - e + w for a constant w (a196's height-3
  tree B has this shape with w = (1, 0)); the family from the working note on nested a196 trees.

F0 is inside F1, which is inside F2. Each family is closed under a common translation of A and B,
so B's translation is fixed (this forces B's root to x^2 + 2) without loss.

## Runs (CP-SAT, OR-Tools 9.x, 4 workers, minimisation, no cuts)

| Run | Family, height | Hint | Time limit |
|---|---|---|---|
| F0_h3, F1_h3, F2_h3 | sanity, height 3 | a196 pair (A, B), value 31 | 10 min each |
| F0_h4 | F0, height 4 | none ((H, H) is not in F0) | 90 min |
| F1_h4 | F1, height 4 | (H, H), value 62 | 90 min |
| F2_h4 | F2, height 4 | (H, H), value 62 | 60 min |

Every solution is rebuilt in pure Python: its lambda value, family membership, stickiness, and the
cyclic triangle's three slices counted by brute force. Only rebuilt values count. The unit tests run
first; a failing test stops the job.

## Verdict rules

- **BUG**: a sanity run has no solution, a value below 31 (contradicts Theorem 81), or is OPTIMAL above
  31 (the a196 pair is in every family); a hint that should be in its family is not, or has the wrong
  value; a rebuild fails; an OPTIMAL objective differs from its rebuilt value; a bound exceeds a rebuilt
  value; a height-4 value is below 60 (contradicts pi_6 >= 216,000). Nothing about values goes public;
  fix and file -v2.
- **H6-BEATS**: a rebuilt height-4 value v <= 61. Then beta_s <= v^(1/6). Before anything goes public the
  witness is rebuilt in a new stdlib script under test, then a theorem note, an article and a DEV post.
- **FAMILY-CLOSED**: no beat, and at least one height-4 family has solver bound >= 62 (flags F0-CLOSED,
  F1-CLOSED, F2-CLOSED). Then no pair in that family beats a196 (computer-assisted, CP-SAT). F2-CLOSED is
  the strongest: no pair of quadratic-root height-4 trees gives a height-6 triangle below 62.
- **UNDECIDED**: otherwise; bounds reported as computer-reported only.

If the container is stopped before the end, `nest.json` holds every finished run with
`"complete": false`; grade from the finished runs and treat missing sanity runs as not run, not as a bug.

## Predictions

| Event | Probability |
|---|---|
| Unit tests and all three sanity runs pass | 85% |
| All three sanity runs reach OPTIMAL 31 in 10 min | 65% |
| F0_h4 closed (bound >= 62) | 35% |
| F1_h4 closed | 18% |
| F2_h4 closed | 8% |
| Verdict H6-BEATS | 6% |
| Verdict FAMILY-CLOSED | 37% |
| Verdict UNDECIDED | 47% |
| Verdict BUG | 10% |

Reason for the low H6-BEATS figure: annealing never went below 69, the unrestricted model found nothing
<= 61, and the two natural hand sub-cases of F0 (working note) both land on 62.
