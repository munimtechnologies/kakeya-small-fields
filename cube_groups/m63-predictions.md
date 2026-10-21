# Job m63: predictions, written 2026-10-21 ~01:10Z before it ran and before m62 reported

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m63 (cube_groups/m63.py) tests Lemma 93 of notes/a52.md: in a split instance whose second
matrix A_(h_1) has rank 0 on X_1, h_1 may be taken with the largest rank on X_1 in N outside
span(u), so every A_n (n in N) vanishes on X_1. That adds 42 negative unit clauses to each (B5)
instance (A_(v_2) and A_(v_3) on the three basis vectors of X_1 other than x0). Nothing else in
the instance changes: it is m62's instance, built by m57.py and m60.py imported unchanged.

When this was written, m61a, m61b, m62a and m62b were queued and none had reported. m63 is
staged, not queued (at most 4 jobs pending). The next run queues it once m62 has reported, and
then fills TAIL_OPEN with the rank-0 tail instances m62 left open (copied from m62's output).

## The plan

- m63a: the 6 rank-0 instances of m62a's re-opened list (o032_c000 a014, a023, a053, a083;
  o000_c000 a031, a098), then TAIL_OPEN["a"]. m63b: the 7 of m62b's (o000_c000 a123, a155, a162,
  a273, a277, a308, a363), then TAIL_OPEN["b"]. Each: CaDiCaL for at most 300 s, then, if open,
  CryptoMiniSat with native XOR for at most 300 s. These are the same caps as m62's re-opened part,
  so the times can be compared instance by instance.
- The 13 run whatever m62 found for them: m62's answer and time are the control.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m60's check of m62's group, unchanged (m57's 14 checks, m55's classes and counts, the 14
   re-opened instances recomputed, the probes).
2. Every m63 entry is one of m55's representatives with the recorded index, rank 0 on its own
   X_1 and the recorded A_(h_1).
3. On the first entry, in both arms: the Lemma 93 instance is m62's instance followed by exactly
   42 negative unit clauses, one on each entry of A_(v_2) and A_(v_3) in the columns of X_1 other
   than x0, consistent with every other unit clause; same variables, hints (111) and XOR count.
4. Any SAT at t = 7 is verified as in m57 (system, anisotropic, normal form with A_u and A_(v_1)).
   A SAT would mean an error in Lemma 93 or a candidate for A(7) = 9: check both by hand before
   any claim.

## Exploratory, with the decision rules

Guesses (low confidence):

- **At least 11 of the 13 UNSAT in CaDiCaL within 300 s, all 13 after both arms.**
- **Lemma 93 helps: on the instances that both m62 and m63 decide in CaDiCaL, the median of
  (m63 time) / (m62 time) is below 0.5.** Basis: in a rank-0 instance the clauses fix 42 of the
  98 entries of A_(v_2), A_(v_3) in place of leaving them to (*); nothing has been measured.
- Each group ends inside 70 minutes of its 150 if TAIL_OPEN is empty.

Rules:

- **Median ratio below 0.5 and no instance slower by more than 2 times:** Lemma 93 becomes part
  of every later split job, for rank-0 instances in (B5) and (B6); a clausal form of "rank at most
  1 on X_1" for the other elements of N is then designed for the rank-1 instances.
- **Median ratio 0.5 to 1:** keep Lemma 93 for rank-0 instances that the plain instance leaves
  open after both arms (it costs nothing); no rank-1 encoding.
- **Median ratio above 1 or more than 2 slower:** Lemma 93 stays a fact in the notes and is not
  used in jobs.
- An instance that m62 left open after both arms and m63 decides is closed by m63 (Lemma 93 is a
  valid symmetry-breaking choice, so its UNSAT is an UNSAT of the m62 instance's case).
- An instance open in both m62 and m63: the third-matrix split by hand (m62's rule) first.

No speed-up is claimed before the run. Every UNSAT is a solver answer saved without a proof
certificate, as in every job of these notes. An UNKNOWN is not evidence either way.
