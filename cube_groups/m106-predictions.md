# Job m106: predictions, written 2026-10-25 in the run that started at 03:11Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m105a-e came back (notes/a98.md). Of the 1,078 k <= 4 cases in the twelve d = 2 classes not
run before, 1,050 were UNSAT within 45 s and 28 UNKNOWN (none SAT, none skipped). In job m105e the
six core cases were UNSAT at all eleven levels, among them anisotropy only on N (15 vectors) and
only on span(h_5, h_6, h_7) without N (7 vectors). The four k = 6 cases were UNSAT at "out3" and
"in4". The positive control (o000_c000, t2 with M = J, anisotropy on N) was SAT, model verified.

Job m106 (cube_groups/m106.py; jobs m106a, m106b and m106e) imports m102.py to m105.py unchanged.
A CNF here keeps every condition of its case (hints, sweep, A_(v_1) = 0, Lemma 105's conditions,
the maps T_n) and asks sigma(h) != 0 only for h in a set S of vectors of V. The full CNF implies
it, so UNSAT for some S means UNSAT for the case.

    m106a  the 28 UNKNOWN cases of m105a-d: S = N ("n", 90 s), S empty ("none", 30 s), then m102's
           sweep CNF (full anisotropy, 120 s; the rule written in m105-predictions.md)
    m106b  transfer to d = 1 and d = 0: two positive controls at "n" (o000_c000 t2 with M = J;
           o011_c000 t3_m001_016, job m103b's relax_n control), then the k <= 4 cases of o007_c008
           (d = 1, 37), o011_c000 (d = 0, 30) and o011_c005 (d = 0, 6) at "n", 60 s each. In job
           m103b, with full anisotropy, o007_c008 gave 31 UNSAT and 6 UNKNOWN; the d = 0 classes
           gave 3 UNSAT, the rest UNKNOWN or not reached
    m106e  the control at "none" and "n"; then, for the six core cases and the four k = 6 cases:
           "none", then a deletion-minimal S inside N (15 vectors) and inside span(h_5, h_6, h_7)
           (7 vectors) with the CNF still UNSAT. Vectors with more basis terms are removed
           first. A kept vector is proven necessary when its removal gives a verified SAT model.
           60 s per solve

## Graded (each must hold)

- Unit tests pass (8 in test_m106) in each job; add_aniso_masks makes the same clauses as
  m101.add_aniso_on on a subspace, and its clause holds exactly when sigma(h) != 0.
- m106a check: the 28 names rebuild to cases with k <= 4 and d = 2, all in m105's sweep list.
- m106b check: 37 + 30 + 6 = 73 cases, d = 1, 0, 0; the two controls have the expected names.
- m106e check: 10 items (six with k <= 4, four with k = 6); N has the 15 masks 1..15, and
  span(h_5, h_6, h_7) has the 7 masks spanned by 256, 512, 1024 in every item.
- Every job: no ERROR; every SAT verified outside the encoder (anisotropic on S, every hand
  condition). m106a: no case SAT with full anisotropy and UNSAT at "n". m106b: both controls SAT,
  verified. m106e: the control SAT at "n", verified; all 10 items ran.

## Exploratory

- m106a: at least 20 of the 28 UNSAT at "n": about 55%. All 28 UNSAT at some level: about 45%.
  At least one UNSAT at "none": about 15%. Any SAT with full anisotropy: about 1%.
- m106b: both controls SAT: about 95%. The 31 o007_c008 cases UNSAT under full anisotropy are
  UNSAT at "n" too: about 65%. At least one of its 6 UNKNOWN UNSAT at "n": about 55%. At least 10
  of the 36 d = 0 cases UNSAT at "n": about 45%. At least one d = 0 case SAT at "n": about 50%.
- m106e: the control SAT at "none": about 97%. At least one of the six core cases UNSAT at
  "none": about 30%. Every minimal S inside N has at most 3 vectors: about 45%. Some core case
  needs only one vector of N: about 30%. u is in every minimal S inside N: about 40%. Some minimal
  S inside span(h_5, h_6, h_7) has at most 2 vectors: about 50%. Every kept vector proven
  necessary (removal SAT, not UNKNOWN): about 65%. At least one k = 6 case UNSAT at "none": about 15%.
- Peak memory at most 1 GB in all three: about 90%. Each finishes within its timeout: about 85%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V** (any job): that would be a system with t = 8 and
  dim V = 11 (A(8) = 11). Re-check it by brute force in a separate job before saying anything.
- **m106a:** every case UNSAT at some level: all 1,115 d = 2 cases with k <= 4 are UNSAT
  (uncertified). Then DRAT certificates (job m107), each built from the smallest CNF that was
  UNSAT for that case ("n" where it was, since it is about 40% smaller), at most four shards per
  run. All certified gives Proposition 39 (computer-assisted): in the rank-0 case of (B7)_8,
  d >= 2 implies k(T(N)) >= 6. Cases still undecided: report them by type; do not certify their
  class.
- **m106b:** "n" decides more of the d = 1 / d = 0 cases than full anisotropy did (m103b): use
  "n" for the 3,876 + 1,500 k <= 4 cases at d <= 1, but only if the median time per case is at
  most 20 s (at most 30 job-hours), queued in shards of at most 3 hours. Otherwise report it
  and do not queue.
- **m106e:** "none" UNSAT for a core case: the hand conditions alone rule out the case; that is
  the first target for a hand proof (Lemma 110), and "none" is run on every k <= 4 case next.
  A small proven-minimal S inside N (at most 3 vectors): try a hand proof that sigma vanishes on
  one of those vectors. Write a lemma only if fully proved. Nothing small: record the SAT models,
  which show what a proof must rule out.
- **k = 6 at "none" or with a small S:** the structure is not special to k <= 4; queue nothing
  more for k = 6 until the core cases are understood by hand (the rule of m105-predictions.md).
