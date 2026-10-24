# Job m105: predictions, written 2026-10-24 in the run that started at 23:30Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m104a, m104b and m104c came back (notes/a97.md). All 57 cases with k(T(N)) <= 4 in the
three d = 3 classes of the rank-0 case of (B7)_8 have DRAT proofs verified by drat-trim
(Proposition 38, computer-assisted). The count over all 68 classes is 6,548 such cases: 57 at
d = 3, 1,115 at d = 2, 3,876 at d = 1 and 1,500 at d = 0. At 60 s each that is 109 job-hours, too
many; the 1,115 cases of the 13 d = 2 classes are 13.9 job-hours at 45 s, so by m104's decision
rule they are queued (at most four shards per run). In m104c's core test, all six cases were UNSAT
with anisotropy kept only on W = N + span(h_5, h_6, h_7) ("out3", dim 7), and all six were UNSAT
with it only on N + span(h_1, ..., h_4) ("in4", dim 8). The third level failed with a KeyError
(an unsorted index list); m105 sorts every index list.

Job m105 (cube_groups/m105.py; five jobs m105a to m105e) imports m102.py, m103.py and m104.py
unchanged.

    m105a-d  check: the 13 d = 2 classes and their k <= 4 counts against job m104a, the 1,078
             cases of the 12 classes other than o004_c000 (its 37 were all UNSAT in job m103b),
             270 / 270 / 269 / 269 per shard; controls: job m102's three positive controls of its
             shard a; sweep: each case with m102's sweep CNF (full anisotropy), 45 s, at most
             125 minutes
    m105e    core: m104c's positive control, then m104's six core cases (types F_8, irr, F_2 x F_4,
             nil3, F_2[x]/(x^3), x(x^2+x+1)) with anisotropy kept only on W at eleven levels, in
             this order: "n" (W = N, 15 vectors); "out1_h5", "out1_h6", "out1_h7" (N + one h,
             31); "noN_out3" (span(h_5, h_6, h_7) without N, 7); "out2_h56", "out2_h57",
             "out2_h67" (63); "in1_h1" (31); "in2_h12" (63); "noN_in4" (span(h_1..h_4), 15).
             Then four k = 6 cases of o000_c000 that were UNSAT under full anisotropy, at "out3"
             and "in4". 90 s each. Every other condition of the case stays in the CNF (hints,
             sweep, A_(v_1) = 0, Lemma 105's conditions, the maps T_n).

## Graded (each must hold)

- Unit tests pass (4 in test_m105) in each job.
- m105a-d check: the 13 classes with d = 2 are exactly those of job m104a's count, with its k <= 4
  numbers; 1,078 distinct cases; every type among irr, nil3, x(x^2+x+1), F_8, F_2 x F_4,
  F_2[x]/(x^3); this shard's share is 270 (a, b) or 269 (c, d).
- m105a-d: the three controls SAT with verified models; no ERROR; every SAT verified outside the
  encoder; rows plus skipped cases = the shard's share.
- m105e check: h_5, h_6, h_7 = indices 8, 9, 10 and h_1..h_4 = 4..7 in all three core classes; the
  sizes of W (15, 31, 31, 31, 7, 63, 63, 63, 31, 63, 15, 127, 255); no repeated index; the six
  core cases and four k = 6 cases known UNSAT; 75 items.
- m105e: all 75 items ran; the control SAT with a verified model; no ERROR; every SAT verified (including anisotropy
  on all of W); no SAT model of a k <= 4 or k = 6 case anisotropic on all of V (that would
  contradict the DRAT proofs and the earlier UNSAT answers).

## Exploratory

- d = 2: all 1,078 UNSAT within 45 s: about 45%. At least 95% UNSAT: about 75%. Any SAT: about 1%.
  No case skipped in any of the four shards: about 70%.
- core, the six k <= 4 cases: at least one UNSAT at "n": about 25%. At least one UNSAT at some
  "out1" level: about 45%. At least one UNSAT at "noN_out3": about 20%. At least one UNSAT at
  some "out2" level: about 60%. At least one UNSAT at "in1_h1" or "in2_h12": about 40%. All six
  SAT at every one of the eleven levels: about 25%.
- k = 6: at least one of the four UNSAT at "out3": about 50%. All four UNSAT at "in4": about 40%.
- Peak memory at most 2 GB in all five: about 90%. Each finishes within 180 minutes: about 85%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A sweep case is SAT:** if the model is verified, it is an anisotropic system with t = 8 and
  dim V = 11 (A(8) = 11): re-check it by brute force in a separate job before saying so. If not,
  the encoder or a solver is wrong: stop and find out which.
- **Every d = 2 case UNSAT** (1,115 of 1,115 with o004_c000): certify them with DRAT (job m106,
  at most four shards per run, as m104) before any claim. All certified gives Proposition 39
  (computer-assisted): in the rank-0 case of (B7)_8, d >= 2 implies k(T(N)) >= 6.
- **Some d = 2 cases UNKNOWN:** re-run only those at 120 s in one job. Any still UNKNOWN: the
  pattern is not uniform at d = 2; report it and do not certify that class.
- **Skipped cases:** re-file only those, same cap.
- **core:** the smallest W at which a case is UNSAT is the target for a hand proof. "n" UNSAT: the
  hand conditions plus anisotropy on N (dim 4) already contradict; prove that first. Some "out1"
  UNSAT: one coset h + N is enough; try Lemma 109 on it. "noN_out3" UNSAT: anisotropy on N is not
  needed beyond what the hand conditions carry. Only "out3" and "in4" UNSAT (every smaller level
  SAT): a hand proof needs at least two cosets with pi phi(h) != 0 or two inside; record the SAT
  models, which show what a proof must rule out.
- **k = 6:** "out3" UNSAT for a k = 6 case: the coset structure is not special to k <= 4; queue no
  more from it until the core cases are understood by hand.
