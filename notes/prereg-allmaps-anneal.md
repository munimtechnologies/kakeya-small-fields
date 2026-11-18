# Pre-registration: annealing search for maps that beat the frame products (all maps, small q and k)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-18. Made with AI agents working in MV2's
name. Text CC BY 4.0, code Apache-2.0 (`anneal_all.py`, tests `test_anneal_all.py`).
**This document was published before the search has run.** No human mathematician has
checked the program it belongs to (a159-a175).

## Question

The program's entropy Kakeya functional, for ANY map P of F_q^k, is

    Lambda(P) = sum over t in F_q of H(X | P(X) + tX)      (bits, X uniform on F_q^k).

By Theorem 2 of the README, the Kakeya growth constant of F_q is beta_q = q 2^(-lambda*/q),
where lambda* = sup_k max_P Lambda(P)/k. Conjecture C_q(k) says Lambda(P) <= k(q - 1), and
the frame products P(x) = x o x reach it. If C_q(k) holds for every k, then
beta_q = q 2^(-(q-1)/q), which is 1.89 at q = 3, compared with the best published lower bound
q/(2 - 1/q) = 1.8 (Dvir-Kopparty-Saraf-Sudan; Bukh-Chao 2021 improve only the constant
factor).

What is known: C_q(1) for every q, C_2(k) for every k, C_3(2) for **all** maps (exhaustive
branch and bound), and many quadratic classes (Theorem 43: every map of degree at most 2 with
k <= 3, for all odd q; a171-a175). **Every map of F_3^3 and of F_5^2 is open.** Most of these
maps are not quadratic.

## Hypothesis and what each outcome would mean

* **H1 (the conjecture side):** no map found by the search has Lambda(P) > k(q - 1).
  A null result does **not** prove C_q(k). It would show how hard the maximum is to beat.
* **H2 (the record side):** some map has Lambda(P) > k(q - 1). One such map in any single
  (q, k) refutes C_q(k). By Theorem 2 it would give Kakeya sets in F_q^n smaller than every
  frame-product construction, for all large n.

## Protocol (fixed now)

* Cases (q, k, minutes): (3, 3, 35), (3, 4, 30), (5, 2, 20), (5, 3, 15), (3, 5, 15), (7, 2, 10),
  (3, 6, 15).
  The master seed is 20261118. Case i uses seed 20261118 + 1000 i.
* Each restart is Metropolis annealing on S(P) = q^k Lambda(P). The temperature falls
  geometrically from 2 to 0.02 over max(200000, 4000 q^k) moves. The moves, with their
  probabilities:
  * join (0.5): P(x) is set so that x enters the t-fibre of a random y;
  * one-coordinate change of P(x) (0.35);
  * a uniformly random new value (0.15).
  Starts cycle through four kinds: a random map, the frame map with 10% or with 30% of its
  values randomized, and the zero map.
* For the best map of each case the output records: Lambda from two independent codes (table
  based and tuple based); the **exact** integer comparison of prod over t and fibres of n^n
  with 2^(k(q-1)q^k); a sampled test of whether the map is quadratic; the fibre-size profile
  of every slice; and the map itself.
* **Decision rule.** A case is a hit only if the exact integer comparison is positive. A hit
  is then re-verified in a fresh job by the tuple-based code, and written up with the map.
  Without a hit, the result is reported as a null result together with the distribution
  of restart maxima, including how many restarts reach k(q - 1) and whether those maxima are
  quadratic. The value of an equality-attaining map that is not quadratic would be a new
  structural fact about the extremizers.

## Status

The job is staged. It runs on MV2's compute queue when a host with that queue is available.
Results will be added to this repository under `results/anneal/` together with a short note.
