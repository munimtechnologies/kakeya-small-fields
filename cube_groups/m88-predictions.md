# Job m88: predictions, written 2026-10-22 ~08:00Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m88 (cube_groups/m88.py) splits o005_c003, the last class of (B6) not yet split (d = 2, |G| =
512, 1961 orbits: 135, 944, 882 of rank 0, 1, 2 on X_1; rank-0 sweep open in job m64a, so the 135
of rank 0 run with Lemma 93 (b)). It has no re-runs in front and runs beside job m87, which
re-runs the 45 open instances of m85b and m86 and splits the other four classes with d = 2.
Everything is m69.py, imported unchanged; m88.py only sets its lists.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the class, unchanged: m57's 14 checks with the planted control at t = 6 in
   both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank on X_1
   equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u; the plan
   (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units 49 on the
   first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly 21
   negative unit clauses, in both arms.
2. The class not among the 39 closed by the split and its re-runs or the seven re-run or split by
   m87.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

- **Some rank-0 instances open: about 90% (about 5 to 25, low confidence).** o005_c002, the other
  class of pair orbit 5 split so far, left 10 of its 75 rank-0 instances open.
- **At least one open instance of rank 1 or 2: about 40%.**
- **The class empty after this one pass: about 5%.**
- **Median UNSAT wall at most 3 s: high confidence.**
- **No SKIPPED instance: about 95%** (1961 instances at about 1.5 s each is about 50 of the 150
  minutes).

Rules: as in m87-predictions.md. All split instances UNSAT: the class is empty, (B6) goes up by
one, the next corollary. 1 to 30 open (SKIPPED counts as open): re-run each with 5 minutes of
CaDiCaL, then 5 of XOR, in the next job. More than 30: read them by rank and by place in m66's
order before queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
