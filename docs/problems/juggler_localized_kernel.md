# Juggler: localizing Paper B's kernel theorem

## Problem

Paper B's Theorem 5.3 bounds the level-2 kernel sum on a dyadic block. How
far does the existing proof localize? A former application additionally
claimed that the answer supplied two companion-paper productions; audit the
landing scale separately from the standalone theorem.

## Exact statement

Let \(c(n)=\tfrac{3k}4n^{9/8}\) with \(1\le k\le P^{1/24}\), let
\(K_c(I)=\sum_{n\in I,\ n\ \mathrm{odd}}e\bigl(c(n)\{\lfloor n^{3/2}\rfloor^{3/2}\}\bigr)\),
and let \(g(n)=\tfrac\ell2n^{9/16}\) with \(\lvert\ell\rvert\le P^{1/24}\) be a
slow twist. For every \(\delta>0\) and every interval \(I\subseteq(P,2P]\) of
length \(Y\ge P^{29/48+\delta}\),
\[
\bigl\lvert K^{g}_c(I)\bigr\rvert\ \ll\ Y\,P^{-1/96+\varepsilon},
\]
uniformly in \(k\), in \(g\), and in the position of \(I\).

The exponent is the one Theorem 5.3 prints. What is new is the admissible
length, and that it is \(29/48\) rather than the \(1/2\) of the depth-\(\le3\)
localization.

This does **not** reach the proposed \(OOOEEE\) and \(OOEOEE\) productions.
Both land at exponent \(27/64\), so their broad inverse scale is
\(P^{37/64}\), and \(37/64<29/48\). The former \(P^{23/32}\) target is the
inverse scale of \(OOEEE\), whose landing exponent is \(9/32\).

## Current literature

`independent`, and internal: this is a statement about Paper B's own proof.
The technique is the one Section 3.5 of that paper uses for Theorems 4.11 and
4.12, namely running the proof with the number of summands in place of the
block length and inventorying the terms that do not scale. No external result
is used beyond the ones Theorem 5.3 already cites (van der Corput,
Erdős–Turán, Vaaler; Lemmas 3.3, 3.5, 3.7, 3.8, 3.9).

## Branch budget

- **Target:** determine the same-saving localization threshold, then compare
  it with the correct \(P^{37/64}\) broad inverse scale of the two proposed
  productions.
- **Novelty hypothesis:** the paper records the localized kernel as unproved and
  guesses that its per-window absolute costs are at most \(P^{7/16}\). If the
  guess is right the localization is routine; if wrong, the interesting question
  is where it stops.
- **Falsifier:** a cost in the proof that is neither proportional to the number
  of summands nor a unit paid \(O(1)\) times; for the advertised application,
  a threshold exceeding \(37/64\).
- **Already killed by?:** none. Not a cycle claim, not a new construction of
  \(e(uw^{3/2})\), not a local attack; it is a transfer of an existing estimate.
- **Existing machinery:** the printed cost displays of Lemma 5.2(i) and
  Theorem 5.3 Steps 2–6; Lemma 4.10 for the twist; the Section 3.5 precedent.
- **Maximum Phase-0 scope:** classify every displayed cost, propagate through the
  three \(A\)-processes, solve for the threshold, and check the classification is
  exhaustive.
- **Promotion criterion:** the standalone threshold is proved and its cost
  inventory closes.
- **Stop criterion:** a cost resists classification; the production
  application stops separately if the threshold exceeds \(37/64\).

## Balanced-ternary formulation

None. The objects are exponential sums over an interval of integers.

## Why BT may be relevant

It is not; recorded for the template.

## Candidate operations / invariants

- the two-kind classification of a cost, proportional or unit:
  **EXACT — HUMAN PROOF** per cost, from the printed display;
- the transfer recursion \(a\mapsto(y+a)/2\) through one \(A\)-process and its
  closed form \((7y+A_1)/8\) through three: **EXACT — LEAN VERIFIED**;
- the threshold \(y\ge A_1+8\cdot\tfrac1{96}\): **EXACT — LEAN VERIFIED**;
- exhaustiveness of the inventory: **COMPUTATIONALLY VERIFIED** by extraction
  from the manuscript text.

## Experiments

`python -m research.juggler_sequence.localized_kernel` writes
`data/research/juggler/localized_kernel/summary.json`: the two cost tables with
each entry's printed exponent and unit, the chain, the threshold, the Claim C
balance, the twist, and the coverage audit.

Three self-checks make the bookkeeping falsifiable rather than asserted.

1. The tables' maxima must be the exponents the manuscript prints:
   \(P^{15/16}\) for Lemma 5.2(i) and \(P^{23/24}\) for \(T_2\).
2. Setting \(Y=P\) must return the paper: \(P^{23/24}\), \(P^{47/48}\),
   \(P^{95/96}\).
3. Every \(P\)-exponent at or above \(P^{1/4}\) displayed in either proof, read
   out of the manuscript by extraction, must be either a tabulated cost or named
   as a count, a length, a parameter, a hypothesis or an intermediate step.
   Fifteen appear in Lemma 5.2(i) and twenty-one in Theorem 5.3; none is left
   over.

As an internal check, the chain at the admissible reference
\(y=23/32\):

| level | proportional | unit |
|---|---|---|
| Lemma 5.2(i) | \(YP^{-1/16}\) | \(P^{25/48}\) |
| Lemma 5.2(ii) | \(YP^{-1/24}\) | \(P^{119/192}\) |
| \(T_2\) | \(YP^{-1/24}\) | \(P^{119/192}\) |
| \(T_1\) | \(YP^{-1/48}\) | \(P^{257/384}\) |
| \(K_c\) | \(YP^{-1/96}\) | \(P^{533/768}\) |

against a target \(P^{17/24}=P^{544/768}\): margin \(P^{11/768}\).

At the actual production scale \(y=37/64\), the final absolute term is
\(P^{877/1536}\), while the same-saving target is
\(P^{109/192}=P^{872/1536}\). Thus the theorem's printed-saving form misses
by \(P^{5/1536}\). The absolute term is nevertheless below the trivial
length \(P^{888/1536}\) by \(P^{11/1536}\); this is formal bookkeeping
outside the theorem's hypothesis, not a proved production estimate.

## Conjectures

None registered.

## Counterexamples

None. The one negative finding is that the paper's guess was optimistic: the
per-window absolute costs are not bounded by \(P^{7/16}\) but reach
\(P^{25/48}\), and \(\tfrac{25}{48}>\tfrac7{16}\).

## Formalization

`formal/Problems/Juggler/LocalizedKernel.lean`, registered in the laboratory
barrel `Problems.Juggler` and in `lean_paths.LAYERS`. It is deliberately **not**
in Paper B's barrel: that barrel's contract is identities, constants and
thresholds, and while this file meets it, the manuscript's certified corpus and
its axiom check are another session's in-flight area, so nothing here is cited
by identifier in the paper.

The legacy names `companionY`, `absTail_companion`,
`target_companion`, `margin_companion` and
`threshold_lt_companion` now explicitly describe the admissible reference
\(23/32\), not the production scale. New arithmetic declarations
`productionLanding`, `productionY`, `productionY_eq_one_sub`,
`absTail_production`, `target_production`,
`production_lt_threshold`, `production_misses_same_saving`,
`production_same_saving_deficit` and
`production_formal_effective_saving` record \(27/64\), \(37/64\), the
same-saving deficit \(5/1536\), and the formal residual saving
\(11/1536\). `twist_uniform_exponent` records the uniform
\(-3/8\) bound. Mathlib's three axioms only. These declarations certify
rational bookkeeping and no estimate.

## Results

**1 (EXACT — HUMAN PROOF).** Theorem 5.5 as stated above, written into Paper B
after Theorem 5.3. Its three ingredients:

*Transfer (Lemma 5.4).* If \(\lvert T_h\rvert\le C(YP^p+P^a)\) for all
\(h\le H=P^{\eta}\le Y\), then the \(A\)-process over \(I\) gives
\(\lvert S\rvert^2\le2Y^2P^{-\eta}+4CY^2P^p+4CYP^a\), so
\(\lvert S\rvert\le C'(YP^{p'}+P^{(y+a)/2})\). The first two terms are the
dyadic balance, unchanged because both carry \(Y^2\); a unit is not squared
away but pushed to the geometric mean with the length. Three \(A\)-processes
send \(P^{a}\) to \(P^{(7y+a)/8}\).

*The balance is against an average.* At \(H_3=t^{1/3}P^{1/12}\) the trivial
term \(2P^2/H_3=2t^{-1/3}P^{23/12}\) is balanced by the \(h_3\)-average of the
second printed term of Lemma 5.2(i),
\((4P/H_3)t^{-1/2}\tfrac23H_3^{3/2}P^{7/8}=\tfrac83t^{-1/3}P^{23/12}\), and by
that term alone: the other four give \(P^{5/3},P^{15/8},P^{15/8},P^{61/32}\).
An average of proportional quantities is proportional, so both sides carry
\((Y/P)^2\) on \(I\) and \(H_3\) is still the balancing choice. The same at
\(H_1,H_2\). No parameter is re-optimized, and the exponent \(\tfrac1{96}\) is
untouched.

*The inventory.* Eleven count-times-unit costs across Lemma 5.2(i) and
Steps 2–6. The largest unit is \(P^{25/48}\), the Stage 5 transition term of
Lemma 5.2(i), at the regime-(s2) constraint \(uh>P^{3/16}\). It is the one unit
that is not a van der Corput inverse root: Lemma 3.8's third term carries no
window-length factor, which is why the manuscript can sum it over windows and
also why one window's worth of it survives localization. The threshold is
\(A_1+8\cdot\tfrac1{96}=\tfrac{25}{48}+\tfrac1{12}=\tfrac{29}{48}\).

*The twist.* Lemma 4.10 after the \(h_1\) differencing, with
\(\mathrm{TV}(\Delta_{2h_1}g)\le0.26YP^{-11/8}\le0.26P^{-3/8}\),
uniformly for \(Y\le P\).

**2 (EXACT — LEAN VERIFIED).** The arithmetic: the closed form, the value
\(533/768\) at \(y=23/32\), the strict inequality against \(17/24\), the margin
\(11/768\), the threshold equivalence and its value \(29/48\), that the
threshold exceeds \(1/2\) and is below \(23/32\), the halving chain
\(-1/24,-1/48,-1/96\), and the Claim C balance with its four dominated terms.
At the actual production scale it also certifies the landing exponent
\(27/64\), inverse exponent \(37/64\), same-saving deficit \(5/1536\), and
formal residual saving \(11/1536\). None of these arithmetic statements
certifies an exponential-sum estimate.

**3 (COMPUTATIONALLY VERIFIED).** The coverage audit and the two self-checks
above.

**4 (Correction to the record).** Section 8 estimated the localized kernel's
per-window absolute costs at \(P^{7/16}\). That is the depth-\(\le3\) figure;
the kernel's largest is \(P^{25/48}\), so the same-saving theorem localizes
to \(P^{29/48}\) and not to \(P^{1/2}\). A second correction is decisive for
the advertised application: \(P^{23/32}\) is the \(OOEEE\) scale, while the
two proposed words require broad scale \(P^{37/64}<P^{29/48}\). Theorem 5.5
therefore remains a standalone theorem and supplies neither production.

## Open questions

- Handling Lemma 3.8's transition term per window rather than absorbing it
  would lower the threshold below \(1/2\).
- Can the formal \(11/1536\) residual saving at \(37/64\) be made into a
  genuine shorter-interval theorem while transporting the exact floor fibers
  and the additional parity restriction? No such theorem is claimed here.
- Only after that transport is proved does the production coefficient become
  meaningful; the stated rule would give \(0.6066\), not the retracted
  \(0.5561\).

## Decision

**PROMOTE.** The standalone theorem is in the manuscript: the printed
\(1/96\) saving persists on intervals of length
\(P^{29/48+\delta}\). The former companion application is retracted because
its correct \(P^{37/64}\) scale is shorter. The formal \(11/1536\) remainder
identifies a proof obligation but is not promoted as a production theorem.

Best next question: can the two-term bookkeeping bound be proved uniformly at
\(P^{37/64}\) together with the exact floor-fiber and parity transport?

## Publication assessment

Status: `THEOREM`. It is a subsection of Paper B, not a separate paper: it
proves a short-interval version of Theorem 5.3 and no companion production.
Its proof rests on the completeness of the unit inventory; a missing unit
above \(P^{25/48}\) would raise the threshold without touching the
proportional exponent.
