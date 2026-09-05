---
title: "Draft: Lemma 5.2(iii), the widened decoration budget"
status: DRAFT — not yet in the manuscript
purpose: close the one interface the architecture table could not
---

# Draft: Lemma 5.2(iii)

## Why

Step 4 of Theorem 5.3 does not use Lemma 5.2 as a black box. The
leftover first-differenced modes \(uW\), \(u'W'\) of Steps (3a) and
(3c) have the algebraic shape of (D1) decorations, but their
coefficients need not obey the printed budget \(|q'|\le4P^{1/24}\), so
the argument opens the lemma: it identifies the two estimates in the
six-stage proof of (i) that use that budget, re-does them, and invokes
the rest of Stages 1--6 unchanged.

That is careful and appears correct, but it means a referee cannot
check Step 4 from Lemma 5.2's *statement*. Part (iii) below states the
widened case as part of the lemma, so Step 4 can cite it.

## Statement

> **Lemma 5.2(iii) (widened decoration budget).**
> Assume (C1)--(C4) and the hypotheses of (i). Suppose that at most two
> of the (D1) terms of \(\rho\) carry, in place of
> \(|q'|\le4P^{1/24}\), the widened budget
> \[
> |q'|\,h'\ \le\ P^{1/2},
> \qquad
> h'\ \le\ P^{1/24}.
> \tag{D1$'$}
> \]
> Then the conclusion of (i) holds for every shift \(h\) satisfying
> \[
> u\,h\,h'\ \ge\ 72
> \qquad\text{for each widened term.}
> \]
> For fixed \(u\) and \(h'\) the shifts violating this are
> \(h<72/(uh')\), at most \(72\) positive integers per widened term.

## Proof

The budget of (D1) enters the six-stage proof of (i) in exactly two
places, both in Stage 6: the \(\theta\)-coefficient and the smooth
curvature ratio. Everything else in Stage 6's (D1) bullet depends on
\(h'\) and not on \(|q'|\) --- in particular the run-boundary cost
\[
\le2.6\,(h/u)^{1/2}P^{7/8}+5.1\,h'(uh)^{-1/2}P^{7/8},
\]
whose second term is the printed fourth term of (i) and is unchanged
because \(h'\le P^{1/24}\) still holds under (D1\('\)). So it is enough
to redo the two comparisons.

*The \(\theta\)-coefficient.* By (D1\('\)), \(|j'|\le3\), \(h'\ge1\)
and \(h\le P^{1/8}\),
\[
|q'|\bigl(2|j'|P^{-1/4}+20hh'P^{-3/4}\bigr)
\ \le\ \frac{6P^{1/4}}{h'}+20\,hP^{-1/4}
\ \le\ 6P^{1/4}+20P^{-1/8}.
\]
Unlike the printed case this is not \(O(P^{-5/24})\): the sawtooth
coefficient \(B\) has size \(\le7P^{1/4}\) rather than \(\le1\), so
the decoration's sawtooth is expanded by the large-\(B\) treatment of
Stage 3(s2) rather than by the small-\(B\) one of (s1). The next
paragraph pays for that.

*The (s2) window inventory.* Every line here is the corresponding line
of Stage 3(s2) with its \(2.25\) replaced by \(7\).

- *Hypothesis.* \(T=P^{1/2}\ge8(1+|B|)\) reads
  \(P^{1/2}\ge8(1{+}7P^{1/4})\), i.e. \(P^{1/4}\ge56.14\), i.e.
  \(P\ge9.9\cdot10^{6}\) --- seven orders below \(P_0\). (The printed
  case needs \(P^{1/4}\ge18.43\).)
- *Windows.* \(B\) is monotone on the dyadic block, so its total drift
  is at most \(\sup|B|\le7P^{1/4}\): at most \(7P^{1/4}+1\) windows on
  which \(B\) moves by \(\le1\). This is the crude count; since \(B\)
  is a degree \(-\tfrac14\) monomial in \(n\), the drift is in fact
  \((1-2^{-1/4})|B(P)|\le1.11P^{1/4}\), but the crude count already
  suffices below.
- *Boundary cost.* Windows times the Lemma 3.3 boundary charge at the
  Stage-4 curvature \(0.35uhP^{-3/4}\):
  \[
  (7P^{1/4}{+}1)\,(0.35uh)^{-1/2}P^{3/8}
  \ \le\ 13.5\,(uh)^{-1/2}P^{5/8}.
  \]
  Note this needs no lower bound on \(uh\). Stage 3(s2) simplifies its
  own boundary cost using \(uh>P^{3/16}\), which is available there
  because (s2) *is* the regime \(uh>P^{3/16}\); here the decoration's
  sawtooth is large independently of the main mode, so a widened
  decoration can occur while the main sawtooth sits in (s1). The bound
  above is stated for every \(uh\ge1\), and is dominated by the fourth
  printed term of (i), which carries
  \((uh)^{-1/2}P^{1/24+7/8}=(uh)^{-1/2}P^{11/12}\), since
  \(\tfrac58<\tfrac{11}{12}\).
- *Flat cost.* \(8(1{+}|B|)P^{1/2}\le64P^{3/4}\) in total, against the
  printed \(19P^{3/4}\); \(\tfrac34<\tfrac78\).
- *Modes.* Per window Lemma 3.7 at the centre \(B_0\) yields
  \(e(w\nu^{3/2})\) with the (s2) weights
  \(\min(2,\tfrac1{\pi|w+B_0|})+\min(2,\tfrac1{\pi|w|})\), which is
  the shape Stage 5 already treats. Their index range is
  \(|w|\le|B_0|+R_0\le2R_0\) at \(P\ge P_0\), so Stage 5's
  dominant-mode sum grows by at most \(\sqrt2\) and its (s2)-tail
  bound by the window ratio \(7/0.6\le12\); both are absorbed by
  \(P^{\varepsilon}\).

*The curvature ratio.* Against the Stage-4 curvature
\(\ge0.35uhP^{-3/4}\), using \(2|j'|\le6\), \(6/0.35\le18\),
\(25/0.35\le71.5\) and \(|q'|h'\le P^{1/2}\) in both summands,
\[
\frac{|q'|\bigl(2|j'|P^{-5/4}+25hh'P^{-7/4}\bigr)}{0.35uhP^{-3/4}}
\ \le\ \frac{18}{u\,h\,h'}+\frac{72}{u}\,P^{-1/2}.
\]
The second summand is \(o(1)\) for \(P\ge P_0\); the first is
\(\le\tfrac14\) as soon as \(uhh'\ge72\). Stage 6 therefore dominates
at margin \(\ge4\), as in the printed case, and Stages 1--5 are
untouched. \(\square\)

## How Step 4 would then read

The paragraph beginning "*Leftover modes.*" becomes:

> The same piece may also carry first-differenced modes \(uW\) and
> \(u'W'\) from Steps (3a) and (3c). After the \(A\)-process of
> Claim C these are
> \(u\,\Delta_{2h_3}\Delta_{d_1}Y\) and
> \(u'\,\Delta_{2h_3}\Delta_{d_2}Y\): (D1) decorations with
> coefficients \(q'=u,u'\) and second shifts \(h'=h_1,h_2\). From
> (3a) and (3c), \(uh_1\le P^{1/2}\) and \(u'h_2\le P^{1/2}\), and
> \(h_1,h_2\le P^{1/24}\), so both satisfy (D1\('\)) and Lemma 5.2(iii)
> applies with main coefficient \(t\) and shift \(h_3\). Its good-shift
> condition is \(t\,h_3\,h_i\ge72\).
>
> The bad set for the \(u\)-mode is \(h_3<72/(th_1)\), at most \(72\)
> integers; likewise for \(u'\); their union has at most \(144\)
> elements. On those \(h_3\) use \(|V_{h_3}|\le P\). The recorded
> \(A\)-process charges
> \(4P H_3^{-1}\cdot144\cdot P=576\,P^2/H_3\le576\,t^{-1/3}P^{23/12}\),
> a constant multiple of the target of Claim G. On the complementary
> good set, Lemma 5.2(iii) gives the same average as for a printed
> decoration, and Claims F--H apply unchanged.

That is roughly fifteen lines shorter than the present passage, and it
cites a statement instead of re-entering a proof.

## What was checked, and what was not

*Checked mechanically.* The string `q'` occurs **zero** times in
Stages 1--5 of the proof of (i) (lines 2359--2532) and exactly twice in
Stage 6 --- the \(\theta\)-coefficient and the curvature ratio. The
other Stage-6 occurrences are `q''`, the (D2) window index, a different
object. So the manuscript's claim that only two estimates use the
budget is structurally confirmed.

*Checked by re-derivation.* Both displays above reproduce Step 4's own
bounds exactly under the substitution \(t\to u\), \(h_3\to h\),
\(h_1\to h'\): Step 4's
\(18/(th_3h_1)+72t^{-1}P^{-1/2}\) and
\(6P^{1/4}/h_1+20h_3P^{-1/4}\) are the same two inequalities in
Theorem 5.3's variable names. The good-shift threshold \(72\) and the
bad-set count \(72\) per mode agree.

### The Stage-2 point, now checked

It splits in two, and only the first half is benign.

*Index range: fine.* Lemma 3.7 produces modes of index
\(\le|B|+J\) with \(J=R_0=P^{5/16}\). In the printed case
\(|B|\le1\), so \(|w|\lesssim R_0\). Under (D1\('\)),
\(|B|\le7P^{1/4}\), and \(7P^{1/4}\le P^{5/16}\) exactly when
\(P\ge7^{16}=3.32\cdot10^{13}\), which \(P_0=8.95\cdot10^{13}\)
clears. So \(|w|\le2R_0\) --- the same shape as the \(2.85R_0\) that
(D2) already carries, and (D2)'s own curvature check is the template.
This half of the worry is discharged.

*Weights: not fine as drafted.* In the printed case \(|B|\le1\) puts
the decoration's \(\theta\)-sawtooth in Stage 3's regime (s1), where
the modes are handed the damping factor
\(\min(2,2\pi|B|)\le14.2P^{-1/16}\). Under (D1\('\)) the coefficient
is \(|B|\le7P^{1/4}\), which is regime (s2): the windowed treatment,
with its own window inventory and boundary cost. Step 4 names this
("the large-\(B\) window treatment of Stage 3(s2)") but does not cost
it out --- no window count for the decoration's sawtooth, no boundary
charge --- and the draft above inherits that omission. **Part (iii)
needs a third paragraph** supplying them before it can be promoted.

### Does the (s1) damping reach the Stage-2 families? No

Two sources feed the same pair of families \(e(r\nu^{3/2})\),
\(e(r(\nu{+}2h)^{3/2})\), and only one of them is damped.

- **Stage 2** Vaaler-expands the *carry* indicator
  \(\kappa=[\theta_\nu\ge1-\{\delta_h\}]\) at truncation \(R_0\). Its
  modes carry weight \(\le1/|r|\) and nothing else --- \(\kappa\) is a
  \(0\)--\(1\) indicator, and no sawtooth coefficient enters.
- **Stage 3(s1)** expands the *\(\theta\)-sawtooth* "into the same two
  mode families", and it is *those* modes that pick up the factor
  \(\min(2,2\pi|B|)\le14.2P^{-1/16}\).

So the damping is a property of the second source, not of the families.
The Stage-2 carry modes are undamped, and the sum below is the sum over
them.

### Where \(P^{29/32}\) is charged

The number is real, and Appendix A.6 confirms it. Of the move from
\(R_0=P^{1/4}\) to \(P^{5/16}\), A.6 says the term "moves from
\(3P^{7/8}\log P\) to \(3P^{29/32}\log P\), still inside
\(P^{23/24}\) with \(P^{5/96}\) to spare" ---
and \(\tfrac{23}{24}-\tfrac{29}{32}=\tfrac5{96}\) exactly. So the term
is verified against **Theorem 5.3's target \(P^{23/24}\)**, not against
Lemma 5.2(i)'s own conclusion. At the earlier \(R_0=P^{1/4}\) it was
\(R_0^{1/2}P^{3/4}=P^{7/8}\), which is exactly (i)'s printed largest
term; raising \(R_0\) moved it to \(P^{29/32}\), and (i)'s conclusion
did not move with it.

The consequence is confined to the statement of (i):

Stage 5's dominant-mode branch gives, per mode,
\(1.4|w|^{1/2}P^{3/4}+1.4|w|^{-1/2}P^{1/4}\). Weighting the Stage-2
families by their \(1/|r|\) and summing over \(1\le|r|\le R_0\),
\[
1.4P^{3/4}\sum_{r\le R_0}r^{-1/2}
\ \le\ 2.8\,R_0^{1/2}P^{3/4}
\ =\ 2.8\,P^{29/32},
\]
which is the manuscript's printed \(3P^{29/32}\log P\). But
\(\tfrac{29}{32}>\tfrac78\), and \(\tfrac78\) is the largest exponent
in the conclusion of (i). At \(u=h=P^{3/32}\) --- admissible, since
\(h\le P^{1/8}\) and \(uh=P^{3/16}\) is the top of regime (s1) --- the
four printed terms are \(P^{23/32}\), \(P^{7/8}\), \(P^{7/8}\) and
\(P^{79/96}\), all below \(P^{29/32}\) by at least \(P^{1/32}\). The
term \((h/u)^{1/2}P^{7/8}\) does cover \(P^{29/32}\) when \(u\) is
small (at \(u=1\), \(h=P^{1/8}\) it reaches \(P^{30/32}\)), but not
when \(u\asymp h\).

There are \(132\) admissible \((u,h)\) pairs in regime (s1) on the
\(1/96\) grid where every printed term is smaller; the worst is
\(u=h=P^{1/24}\), short by \(P^{1/32}\).

**Theorem 5.3 is unaffected**, and so is every other consumer: the
assembly and part (ii) target \(P^{23/24}\), and Step 5b's
mode-dominant regime targets \(P^{15/16}=P^{30/32}\), all of which
exceed \(P^{29/32}\). So the repair is one line in the statement of
(i) --- a fifth term \(R_0^{1/2}P^{3/4}\), or equivalently making the
\(R_0\)-dependence explicit --- with nothing to propagate downstream.
`stage2_mode_accounting.py` prints the comparison in exact rationals.

*A smaller point in the same place.* A.6 calls
\(3R_0^{1/2}P^{3/4}\log P\) "the collision-band sum of Stage 5", but
Stage 5 puts that formula in the *dominant-mode* branch; its collision
band is the middle case, totalling \(\le CP^{7/8}\log P\). Same number,
two names --- worth aligning, since A.6 is where a referee will go to
trace why \(R_0=P^{5/16}\).

### Status

Both halves of the Stage-2 check are now discharged. The index range
was fine at \(P\ge P_0\); the weights needed the (s2) window inventory,
which the proof above now supplies, and whose three costs ---
\(13.5(uh)^{-1/2}P^{5/8}\) boundary, \(64P^{3/4}\) flat, and modes at
the unchanged \(P^{29/32}\) --- all sit inside the conclusion of (i).

Part (iii) therefore rests on one thing outside itself: the amendment
of (i) to carry \(R_0^{1/2}P^{3/4}=P^{29/32}\), which the Stage-2
family sum requires with or without (iii). With that amendment in
place, (iii) is complete as stated. Without it, (iii) inherits an
understated bound.

The remaining work is editorial rather than mathematical: amend (i),
insert (iii), rewrite Step 4's "*Leftover modes*" paragraph as drafted
above, and extend the architecture table with a row for (iii).
