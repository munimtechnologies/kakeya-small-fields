# Job m109: predictions, written 2026-10-25 in the run that started at 18:30Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m108g and m108h came back (notes/a101.md); every graded check held. With the normal form and M
kept, the deletion-minimal sets of the 16 groups of (*) have 7 to 11 groups. Six groups are kept in
all ten cases (Q_vhh, Q_uhh, Q_uvh, L_vh, L_hu, L_uh), and Q_hhh, Q_vvh, Q_vvv and Q_uvv are
dropped in all ten. "M only" is UNSAT in all twelve other k = 6 cases tried. The DRAT jobs m108a-d
had not come back when this was written.

Job m109 (cube_groups/m109.py; jobs m109g, m109h, m109i, m109j) imports m102.py to m108.py
unchanged. An equation of (*) is kept when its group, all its basis indices of V and its row of X
are kept. For each of the ten items (six core cases in g and h, four k = 6 cases in i and j), with
the normal form and M kept and 120 s per solve, after a positive control:

    pass 1   a deletion-minimal set of basis indices, dropped in the order h_1..h_4, h_5..h_7,
             v_1, v_3, v_2, u (all rows, all groups)
    pass 2   with those indices, a deletion-minimal set of rows, dropped in the order 0..7
    pass 3   with those indices and rows, a deletion-minimal set of the groups that still have an
             equation (m108.STAR_DROP)

## Graded (each must hold)

- Unit tests pass (8 in test_m109) in each job.
- Check: with everything kept, encode_sub is sat_aniso.encode clause for clause (hash, count,
  variables) and its group counts are m108's; the counts of the sub-system on u, v_2, v_3, h_5,
  h_6, h_7 and rows 5, 6, 7 are the hand counts (3, 6, 9, 6, 12, 18, 9, 18, 27; 9, 54, 27, 0, 27,
  54, 9), both counted and encoded; build_sub with everything is m108.build_star clause for
  clause; M adds 128 units; the shard has its items (3, 3, 2, 2), core in g and h, k = 6 in i, j.
- No ERROR; the control SAT and verified; every SAT verified outside the encoder (the normal form,
  M, every kept equation); every item UNSAT with everything kept.

## Exploratory

- In every item at least one of h_1..h_4 is dropped: about 70%. All four dropped in every item:
  about 35%.
- h_5, h_6, h_7 all kept in every item: about 50%.
- v_1 dropped in every item: about 50%. u kept in every item: about 85%.
- At most 5 of the 8 rows kept in every item: about 55%. At most 3: about 25%.
- At most 200 equations kept in every item: about 40%. Some item at most 50: about 20%.
- At least half the items with every kept index, row and group proven needed: about 35%.
- The six core cases keep the same index set: about 30%.
- Nothing skipped (all three passes finish in every item within 200 minutes): about 75%.
- Peak memory at most 1 GB in every job: about 90%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V** (any job): re-check it by brute force in a separate
  job before saying anything.
- **Some item keeps a small system (at most 6 indices and 3 rows, or at most 150 equations):** write
  that system out in full in the note, try the transfer test (the smallest kept system on all ten
  items and the twelve "M only" cases, job m110), and attempt Lemma 110 by hand for that item,
  simplest type first (F_8, irr). Write the lemma only if fully proved.
- **Every item keeps 9 or more indices:** the contradiction is spread over V, and a hand proof
  along this route is not promising; say so, and turn to the d = 1 cases at "n" and the DRAT
  certificates.
- Jobs m108a-d (DRAT certificates of the 1,115 d = 2 cases) are graded on their own rules
  (m108-predictions.md); m109 does not change them.
