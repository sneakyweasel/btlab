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
coefficient \(B\) has size \(\le7P^{1/4}\) rather than \(\le1\).
Lemma 3.7 at \(T=P^{1/2}\) applies nonetheless, since
\(T\ge8(1+|B|)\) reads \(P^{1/2}\ge8(1+7P^{1/4})\), which holds once
\(P^{1/4}\ge56\). This is the large-\(B\) window treatment of
Stage 3(s2), already used inside the proof of (i).

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

*Not checked.* Whether Stages 1--5 depend on the budget *implicitly* ---
through a quantity derived upstream using \(|q'|\le4P^{1/24}\) but not
naming \(q'\). The one candidate I can see is Stage 6's remark that
"the modes are expanded in the Stage-2 families": if a widened
coefficient produced mode indices outside the range Stage 2 admits,
(iii) would need a further hypothesis. Step 4 does not raise this, which
suggests it is fine, but it is the single point on which this draft
rests on the manuscript rather than on its own verification, and it
should be confirmed before (iii) is promoted out of draft.
