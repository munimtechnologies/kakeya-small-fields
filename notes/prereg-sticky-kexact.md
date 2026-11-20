# Pre-registration: sticky-kexact-v1 (exact kappa_4, and searches at heights 5-6)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-20, written before the job ran. Made with AI agents
working in MV2's name. No human mathematician has checked this.

## Question

Note a196 (Theorem 79) shows kappa_4 <= 31, so the sticky Kakeya base over F_3 is
beta_s <= 31^(1/5) = 1.98734, and a195/a196 give kappa_4 >= 30 (from pi_5 >= 27,000). **Is
kappa_4 = 30?** If so, beta_s <= 30^(1/5) = 1.97435 and pi_5 = 27,000 exactly. If not, the a196
tree is optimal among all cyclic-triangle constructions from height-4 trees.

Note a197 reduces this to two small exact problems:

- **Lemma 166.** kappa_h = min over trees P of |S_0(P)| + |S_1(P) u S_2(P)| (the offsets i, w are
  removed by the rotation rho_i and by R(d) = P(d + e) + e, which has S_t(R) = S_t(P) + (1 - t) e).
- **Lemma 167.** With Proposition 92, kappa_4 = lambda_3, where
  lambda_3 = min over height-3 trees A, B of |A_0| + |B_0| + |B_1| + |B_2 u A_1 u A_2|.

## Method (code `sticky_kexact.py`, tests `test_sticky_kexact.py`)

CP-SAT (OR-Tools 9.x, 4 workers), one Boolean per value-table entry (one-hot) and per point;
translations fixed per depth. Runs, in order, each with its own time limit:

| run | model | exact for | limit |
|---|---|---|---|
| kappa1-3 | kappa(h), h = 1, 2, 3 | kappa_h (sanity: 4, 8, 16) | 10 min each |
| lambda2 | pair(2) | lambda_2 (sanity: 16) | 10 min |
| lambda3 | pair(3), hint = a196 pair (31) | lambda_3 = kappa_4 (via Prop 92) | 30 min |
| kappa4_rooted | kappa(4), root x^2 fixed, hint H (31) | kappa_4 (via Prop 92) | 50 min |
| kappa4_direct | kappa(4), no root assumption, hint H | kappa_4 (independent of Prop 92) | 50 min |
| lambda4 | pair(4), hint (H, H) (62) | lambda_4 | 50 min |
| kappa5_rooted | kappa(5), root x^2, hint G (62) | an upper bound for kappa_5 | 40 min |

Every solution is rebuilt in pure Python; for kappa models the cyclic triangle (height h+1), for
pair models N and its cyclic triangle (height h+2), are built as explicit maps, checked to be
sticky, and their three slices counted by brute force. Only rebuilt values count.

## Verdicts (fixed now)

- **BUG**: a sanity value differs from 4, 8, 16, 16 or is not OPTIMAL; a hint value is not
  31/31/31/62/62; a rebuilt solution fails its checks; an OPTIMAL objective differs from its
  rebuilt value; a solver bound exceeds a rebuilt value; any height-4 value below 30 (conflicts
  with pi_5 >= 27,000). Then nothing public about the values; fix and file -v2.
- **BASE-IMPROVED** (flag KAPPA4-30): a rebuilt height-4 value of 30. Then kappa_4 = 30,
  pi_5 = 27,000 and beta_s <= 30^(1/5) = 1.97435. Before anything public: re-verify the witness in a
  separate small script under test_first, then a theorem note and an update of the S7 article.
  If lambda3 is OPTIMAL at 31 but kappa4_direct rebuilds 30, flag PROP92-CONFLICT (Prop 92 is wrong;
  the base still improves).
- **BASE-IMPROVED** (flag BASE-IMPROVED-H6): a rebuilt lambda4 or kappa5_rooted value <= 61, giving
  beta_s <= v^(1/6) (61^(1/6) = 1.98407). Same re-verification rule.
- **KAPPA4-31**: lambda3 OPTIMAL at 31 (then kappa_4 = 31, using Prop 92), and/or kappa4_direct
  OPTIMAL at 31 (then kappa_4 = 31 without Prop 92). The a196 tree is then optimal among cyclic
  triangles of height-4 trees; a better base must come from height >= 5.
- **UNDECIDED**: none of the above; report the solver bounds as computer-reported only.

CP-SAT's optimality claims are not independently checkable certificates; any exact value will be
stated as "computer-assisted (CP-SAT)" until certified another way.

## Predictions (written before the run)

- Self-checks and sanity pass: 90%.
- lambda3 OPTIMAL within its limit: 80%. Its value is 31: 70%; 30: 30%.
- kappa4_rooted OPTIMAL: 50%. kappa4_direct OPTIMAL: 30%.
- A rebuilt lambda4 <= 61: 20%. A rebuilt kappa5_rooted <= 61: 15%.
- Verdict BASE-IMPROVED: 30%; KAPPA4-31: 50%; UNDECIDED: 10%; BUG: 10%.

This job is exact where sticky-pair-v1 (annealing over the same pairs, still queued) is
heuristic; both will be graded against their own pre-registrations.
