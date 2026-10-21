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

## Addendum, written 2026-10-21 ~03:50Z after m62 reported and before m63 ran

What m62 found (notes/a55.md): all 14 re-opened instances UNSAT (12 in CaDiCaL, a574 and a031 in
the XOR arm), so the 13 controls of m63 are all known UNSAT, 11 of them in CaDiCaL (a031 needed
the XOR arm). The split of o000_c001 left 27 instances open (24 of rank 0, 3 of rank 1 or 2) and
o000_c002 left 25 (20 of rank 0, 5 of rank 1 or 2), none skipped, each at a budget of 10 to 20 s.

Changes to the plan, made before m63 ran:

- TAIL_OPEN holds the 24 (a) and 20 (b) rank-0 tail instances, copied from m62's output files.
- TAIL_PLAIN is new: the 3 (a) and 5 (b) tail instances of rank 1 or 2. Lemma 93 gives nothing
  linear for them, so they run as m62's instances, unchanged (named r3s_, no extra clauses), with
  the same two arms and caps. This carries out m62's rule for a split with 1 to 30 open.
- Order in each group: the controls, then TAIL_PLAIN, then TAIL_OPEN. Instances not reached in the
  150 minutes are SKIPPED and count as open.
- Added checks: every TAIL_PLAIN entry is one of m55's representatives with its recorded index,
  rank (1 or 2) and A_(h_1); TAIL_OPEN and TAIL_PLAIN together are exactly as many as m62 left
  open in that group's tail class, all from that class.
- The grade reports whether the tail class is now empty: m62's UNSAT plus this group's.

Only m63a is queued now (2 jobs pending before it, m64a and m64b, and m66 queued with it); m63b
is staged.

Guesses for the tail (low confidence, written before m63 ran):

- **TAIL_PLAIN: all UNSAT in CaDiCaL within 300 s** (3 of 3 in a, 5 of 5 in b). Every instance
  of rank 1 or 2 re-opened so far closed (m60b's a219 and a262, m62a's a574, the last in XOR).
- **TAIL_OPEN: at least 20 of 24 (a) and 16 of 20 (b) UNSAT after both arms.** m60's and m62's
  rank-0 instances that had their full 20 s first all closed, in 15 to 272 s.
- **o000_c001 empty after m63a; o000_c002 empty after m63b: guess yes for each, low confidence.**
- **m63a ends without SKIPPED instances**, its 33 entries inside 150 minutes.

Rules for the tail:

- **A tail class all of whose instances are UNSAT** (m62's and m63's): the class is empty, (B5)
  goes up by one (the next corollary).
- **A tail instance still open after both arms:** the third-matrix split by hand first, as for the
  re-opened ones.
- **SKIPPED tail instances:** re-run in the next group (m63c) with the same caps.
- The speed rule above is graded on the 13 controls only: the tail instances have no CaDiCaL time
  from m62 to compare with (UNKNOWN at 10 to 20 s).
