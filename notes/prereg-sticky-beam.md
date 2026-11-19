# Pre-registration: sticky-beam-v1 (a search for a finite certificate of S7)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-19, written before any run. Made with AI agents
working in MV2's name. Code: `sticky_beam.py` (tests `test_sticky_beam.py`). Theory: note a188.

## Question

By Theorem 78 (a188), sticky Kakeya sets in F_3^n grow at base beta_s = tau^(1/3), where tau is
the infimum of (|S_0||S_1||S_2|)^(1/k) over full sticky trees of height k. So beta_s < 2 (question
S7) holds exactly when some full tree of some height k has slice product below 8^k. The classical
tree has product exactly 8^k at every height. a187's height-3 tree has 637 > 512.

## Method (fixed now)

A beam over real full trees, heights 1 to 10, with exact unions (bitsets). Height 1 is exhaustive.
At each height a few dozen base trees are kept: for each of 28 weight vectors on the simplex,
the 3 best by the weighted log of their sorted slice sizes, plus the 16 best by product. The next
height is built from all six slice permutations of every base and a random translate of the first
24 bases, using 40,000 random nodes (all 27 root maps), the doubling of every base, and two passes
of local improvement on the 12 best. Restarts with seeds 20261119, 20261120, ... run until 150
minutes have passed. Every node whose product is below 8^k is rebuilt as explicit node maps from
its recipe, checked to be a full tree, and has its slices recomputed by enumerating all 3^k
directions.

Before the beam, `sticky_pi3.py` computes every real slice-size vector of height 2 (all 27^4
trees), keeps the coordinatewise-minimal ones, and takes the least product over all 27 root maps
with "max of the children" in place of each union. Unions are at least that large and the bound
is monotone, so this is a proved lower bound for pi_3.

## Rules

- **Sanity.** The tests must pass. In the run, the best product must be exactly 8 at height 1 and
  64 at height 2 (Proposition 83), and at most 8^k at every height (doubling). Anything else is a
  BUG, and nothing below is used.
- **S7-CERT.** A verified tree (full, recomputed sizes equal to the claimed ones, product < 8^k)
  at any height. Then beta_s <= product^(1/(3k)) < 2, and S7 is answered yes. The tree is
  published with its maps and an independent re-check before any claim is made.
- **S7-NONE.** No verified tree. Then nothing is concluded about S7, because the search is
  heuristic. We report the best ratio product / 8^k at each height.
- **PI3.** If `sticky_pi3.py` returns 512, then pi_3 = 512 exactly, and no certificate exists at
  height 3 or below. A value below 432 = (27/4) · 64 contradicts Lemma 162 and is a BUG. A value
  from 433 to 511 leaves pi_3 open, and the beam's height-3 result is then the best upper bound.
  (A hand case analysis made before the run predicts 512.)
- A verified tree with product below 1.90499^(3k) = 6.913^k would contradict Theorem 72
  (Corollary 78.2). That would mean a BUG in this code or a gap in a183, and it would be reported
  as such.

## Prediction (made before the run)

S7-NONE, with best ratio exactly 1 (the classical doubling) at every height up to 10. Reason: the
game relaxation (a185) needs very lopsided trees, built far from the leaves, to beat 2^h, and real
unions cost at least as much as the game's maxima. A certificate at height <= 10 would be a
surprise.
