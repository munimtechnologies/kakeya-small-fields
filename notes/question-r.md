# Question R, first case: no counterexample below t = 5

MV2 of Munim, Inc., 2026-10-17. Added to kakeya-small-fields after version 1.7.10, next to
[sat-search.md](sat-search.md), which poses Question R. Numbering continues from
[rank-restriction.md](rank-restriction.md) (Lemma 31, Lemma 32, Proposition 25). This is partial
progress: it settles no new case of Corollary 17. It was researched and written with AI agents
working in MV2's name. The proofs are by hand; `cube_groups/question_r.py` checks Lemma 31 on
systems and Lemma 32 exhaustively for t <= 5, and its unit tests gated this commit. No human
mathematician has checked the proofs. Text CC BY 4.0, code Apache-2.0.

## Where this sits

The setting is that of section 14 of [finite-groups.md](../finite-groups.md): X = F_2^t, a quadratic
map sigma : V -> X with polar form beta, and a linear map h -> A_h from V to End(X) with

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

A(t) is the largest dim V of an anisotropic system (sigma(h) != 0 for h != 0). Lemma 30 says that an
element of rank rho gives dim V <= t + A(t - rho - 1), and Question R asks whether
t + A(t - rho - 2) holds instead. Its first instance is an element of rank t - 2: does it force
dim V <= t? Lemma 30 gives dim V <= t + 1, and sat-search.md shows that a system with dim V = t + 1
and an element u of rank t - 2 falls into one of two cases. Put x0 = sigma(u) and phi = beta(u, .).

- **Case A:** phi maps V onto X, with kernel span(u).
- **Case B:** phi(V) is a hyperplane that misses x0, with a kernel of dimension 2.

Proposition 25 below shows that Case A needs t >= 5, and describes the only shape it can take at
t = 5. Case B is still open for every t >= 4.

## Lemma 31 (an identity at a pair)

**Lemma 31.** In every system, let u, v in V satisfy beta(u, v) = sigma(u), and put phi = beta(u, .)
and psi = beta(v, .). Then

    (I + A_v) phi(h) = A_u (phi(h) + psi(h))     for all h in V.

In particular I + A_v maps phi(V) into Im A_u.

*Proof.* Replace h by h_1 + h_2 in (*) and subtract the two instances for h_1 and h_2:

    A_(h') beta(h_1, h_2) = A_(h_1) beta(h_2, h') + A_(h_2) beta(h_1, h').

(This is the coordinate-free form of (Q) in sat-search.md.) With h_1 = u, h_2 = v and h' = h it
reads A_h sigma(u) = A_u psi(h) + A_v phi(h). Putting h -> u and h' -> h in (*) gives
A_h sigma(u) = (I + A_u) phi(h). The two right-hand sides agree, and rearranging gives the identity.
QED

## Lemma 32 (linear algebra)

**Lemma 32.** Let A_u in M_t(F_2) have rank t - 2 and kernel span(x0, z), and let R = Im A_u. Let A_v
satisfy A_v x0 = x0, A_v z = 0 and Im(I + A_v) in R, and put A_w = A_u + A_v. If A_v and A_w both
have rank <= t - 2, then t >= 5. If t = 5, then A_v and A_w have rank exactly 3; their kernels K_v
and K_w are planes in R with K_v n K_w = span(z) and K_v + K_w = R; R is invariant under A_v and A_w,
which act as the identity on X / R; and their fixed spaces meet in span(x0).

*Proof.* I + A_v is the identity on K_v, so K_v lies in Im(I + A_v), which lies in R. Also
I + A_w = A_u + (I + A_v) has its image in R, and the same argument puts K_w in R.

On K_v n K_w, A_u = A_v + A_w vanishes, so K_v n K_w lies in span(x0, z). Here A_v z = 0 and
A_w z = A_u z + A_v z = 0, while A_v x0 = A_v (x0 + z) = x0 != 0. Hence K_v n K_w = span(z).
Similarly A_u = I + I = 0 on the intersection of the fixed spaces, which therefore lies in
span(x0, z). Both A_v and A_w fix x0 (A_w x0 = A_u x0 + A_v x0 = x0), but A_v z = 0 and
A_v (x0 + z) = x0, so the fixed spaces meet in span(x0).

The ranks are at most t - 2, so dim K_v >= 2 and dim K_w >= 2. Then

    4 <= dim K_v + dim K_w = dim (K_v + K_w) + 1 <= dim R + 1 = t - 1,

so t >= 5. For t = 5 every step is an equality: dim K_v = dim K_w = 2, K_v + K_w = R, and both ranks
are 3. A_v kills K_v, and on K_w it equals A_u + A_w = A_u, which maps into R. So A_v R lies in R,
and likewise A_w R. Finally Im(I + A_v) and Im(I + A_w) lie in R, so both act as the identity on
X / R. QED

## Proposition 25 (Case A)

**Proposition 25.** Let (sigma, alpha) be an anisotropic system with dim V = t + 1 and an element u
with rank A_u = t - 2 such that phi = beta(u, .) maps V onto X. Then t >= 5. If t = 5, take v with
phi(v) = x0 = sigma(u), put z = sigma(v) and w = u + v. Then the conclusions of Lemma 32 hold for
A_u, A_v and A_w.

*Proof.* By Lemma 30, an element of rank t - 1 would give dim V <= t, so there is none. Every A_h is
singular, because A_h sigma(h) = 0 with sigma(h) != 0 for h != 0. So every A_h with h != 0 has
rank <= t - 2.

v is not in span(u), because phi(v) = x0 != 0 = phi(u). So v lies in U+ outside span(u), and by
Lemma 30, z = sigma(v) lies in ker A_u and not in span(x0). As ker A_u has dimension 2, it is
span(x0, z). Lemma 30(a) gives A_v x0 = phi(v) = x0, and A_v z = A_v sigma(v) = 0. Lemma 31 applies
because beta(u, v) = phi(v) = x0 = sigma(u), and as phi(V) = X it gives Im(I + A_v) in Im A_u.
Finally w != 0, so A_w = A_u + A_v has rank <= t - 2 as well. Lemma 32 now applies. QED

So in an anisotropic system with t <= 4 and dim V = t + 1, every element of rank t - 2 is in Case B. For t = 4 this
adds nothing to Theorem 26 (A(4) = 4), but it is a proof of one case of Question R that does not use
Lemma 29.

## What it does not settle

Lemma 32 alone cannot exclude t = 5. Take x0 = e_0, z = e_1, R = span(e_1, e_2, e_3), let A_u kill e_0
and e_1, fix e_2 and e_3 and send e_4 to e_1, and let A_v fix e_0, e_3 and e_4 and kill e_1 and e_2.
Then every hypothesis and conclusion of Lemma 32 holds (A_w fixes e_0 and e_2, kills e_1 and e_3, and
sends e_4 to e_1 + e_4). So excluding Case A at t = 5 needs the rest of (*), not only these three
elements. Case B is open for every t >= 4. The exact search of sat-search.md was meant to decide
Question R for t = 5 directly, whatever the case, but its run did not decide those instances in
time (see the Results of sat-search.md).

## Computation

`cube_groups/question_r.py` has three parts, and its unit tests (which gated this commit) run
reduced versions of each.

- **identity** checks Lemma 31 at every pair (u, v) with beta(u, v) = sigma(u), and every h, of the
  diagonal systems of Lemma 23(d) with t = 2 and 3 and of random systems with t = 3 and 4. The tests
  assert that the diagonal systems have pairs with sigma(u) != 0, so the check is not vacuous.
- **control** makes sure the check can fail. On random pairs (alpha, sigma) with t = 3 and dim V = 3
  that are not systems, Lemma 31 fails at some pair.
- **casea** checks Lemma 32 for t = 3, 4 and 5 by exhaustive search. A change of basis that fixes
  x0 = e_0 and z = e_1 preserves every hypothesis and conclusion. It puts R, which contains z because
  (I + A_v) z = z, in the form span(e_1, ..., e_(t-2)) if x0 is not in R, or span(e_0, ..., e_(t-3))
  if it is. Then A_u is any matrix whose columns 0 and 1 are zero and whose other columns are an
  ordered basis of R. A_v is any matrix whose columns are e_0, 0 and e_j + r_j (r_j in R) for j >= 2,
  and these are exactly the A_v with A_v x0 = x0, A_v z = 0 and Im(I + A_v) in R. That makes 2, 192
  and 2 x 168 x 512 = 172,032 pairs for t = 3, 4 and 5. The tests assert these counts, that no pair
  survives the rank conditions for t = 3 or 4, that every surviving pair for t = 5 has all the
  conclusions, that some pair survives, and that the example above is one of them.

**Full run** (job qr-casea-v1, 2026-10-17 from 16:17 to 16:20 UTC, one CPU). All three parts ran
in full, with predictions written down before the run, and every prediction held. The 8 unit tests
passed. casea: 2, 192 and 172,032 pairs for t = 3, 4 and 5, no hypothesis failure, no survivor for
t = 3 or 4, and for t = 5 11,136 survivors (8,064 with x0 outside R and 3,072 with x0 in R), every
one with all the conclusions of Lemma 32. identity: no failure of Lemma 31 on any of the 2,080 pairs
checked (100 and 1,000 for the diagonal systems with t = 2 and 3, of which 36 and 488 have
sigma(u) != 0; 298 and 682 for 20 random systems each with t = 3 and 4). control: no random pair was
a system, and Lemma 31 failed on 47 of the 50.

## Prior work

As for rank-restriction.md: searches on 2026-10-15 to 2026-10-17 found nothing on the identity (*),
on A(t) or on Question R. The tools are elementary, so a specialist may know them. Please open an
issue at https://github.com/munimtechnologies/kakeya-small-fields if so, or if you find an error.
