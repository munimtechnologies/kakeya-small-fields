# Job m80: predictions, written 2026-10-21 ~21:45Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m80 (cube_groups/m80.py) is m78.py's group r with its lists rebound: each of the 7 instances
of r3b_t7_B5_o005_c005 that m78a and m78b left UNKNOWN at their 10 s budgets gets 5 minutes of
CaDiCaL and then, only if still open, 5 minutes of XOR. All 7 are of rank 1 on X_1:

    m78a: a1774 (m55 index 12342)
    m78b: a3821 (262198), a3845 (262534), a4910 (546834), a4982 (560182), a5005 (561206),
          a5032 (564278)

The other 6713 instances of the class were UNSAT (2096 of rank 2 and 4617 of rank 1). Its rank-0
sweep was UNSAT (job m64b), so by Lemma 93 (a) no rank-0 instance is needed.

Queued with m79a, m79b and m81a: four pending, within the habit of at most four.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m75's check, unchanged, for o005_c005: m57.py's 14 checks with the planted control in both
   arms; m55's structure with d = 2; |G| = 512 = Proposition 34 (c); |Adm| = 405566; class counts
   by rank on X_1 equal to m74's run (895, 4624, 2096); every root admissible, of its rank,
   distinct with its sum with A_u; the plan (7 entries, rank 1, one per instance); hints 111 and
   units 49 on the first instance in both arms.
2. m80's own: m55's roots at orders 1774, 3821, 3845, 4910, 4982, 5005 and 5032 of o005_c005 have
   the m55 indices, rank and A_(h_1) that m78a and m78b recorded.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 34): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses:

- **All 7 UNSAT within their 5 minutes of CaDiCaL: about 80%.** Every leftover re-run at 300 s so
  far closed (68 of 68, counting m78r's a1240, which closed in 9.89 s after an UNKNOWN at 10.01 s).
- **Every one of the 7 UNSAT within 60 s of CaDiCaL: about 65%.** the slowest UNSAT instances of
  m75b, m78a, m78b and m78r took 7.59, 7.95, 9.69 and 9.89 s.
- **No XOR arm needed: about 80%.**

Rules:

- **All 7 UNSAT:** o005_c005 is empty (the next corollary), and (B5) is closed at 420 of 420.
  Re-read every dependency (Propositions 32 and 34, Lemma 93, the (B5) list of job m55 and the
  closures of m60, m67, m70, m75, m78) before writing that down.
- **Any still open after 10 minutes:** it is the first leftover that did not close at 300 s.
  Write it down, do not count o005_c005 as empty, and look at a third-matrix split of that
  instance by hand before queueing anything for it.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
