# Juggler: localizing Paper B's kernel theorem

## Problem

Paper B's Theorem 5.3 bounds the level-2 kernel sum on a dyadic block. The
companion paper needs it on much shorter intervals. Does the existing proof
give it there, and at what length does it stop?

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

## Current literature

`independent`, and internal: this is a statement about Paper B's own proof.
The technique is the one Section 3.5 of that paper uses for Theorems 4.11 and
4.12, namely running the proof with the number of summands in place of the
block length and inventorying the terms that do not scale. No external result
is used beyond the ones Theorem 5.3 already cites (van der Corput,
Erdős–Turán, Vaaler; Lemmas 3.3, 3.5, 3.7, 3.8, 3.9).

## Branch budget

- **Target:** does Theorem 5.3 hold on intervals of length \(P^{23/32}\), the
  preimage intervals of an even block's landing points?
- **Novelty hypothesis:** the paper records the localized kernel as unproved and
  guesses that its per-window absolute costs are at most \(P^{7/16}\). If the
  guess is right the localization is routine; if wrong, the interesting question
  is where it stops.
- **Falsifier:** a cost in the proof that is neither proportional to the number
  of summands nor a unit paid \(O(1)\) times, or a unit so large that the
  threshold exceeds \(23/32\).
- **Already killed by?:** none. Not a cycle claim, not a new construction of
  \(e(uw^{3/2})\), not a local attack; it is a transfer of an existing estimate.
- **Existing machinery:** the printed cost displays of Lemma 5.2(i) and
  Theorem 5.3 Steps 2–6; Lemma 4.10 for the twist; the Section 3.5 precedent.
- **Maximum Phase-0 scope:** classify every displayed cost, propagate through the
  three \(A\)-processes, solve for the threshold, and check the classification is
  exhaustive.
- **Promotion criterion:** the threshold is below \(23/32\), so the companion's
  productions become available.
- **Stop criterion:** the threshold exceeds \(23/32\), or a cost resists
  classification.

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

The chain at \(y=23/32\):

| level | proportional | unit |
|---|---|---|
| Lemma 5.2(i) | \(YP^{-1/16}\) | \(P^{25/48}\) |
| Lemma 5.2(ii) | \(YP^{-1/24}\) | \(P^{119/192}\) |
| \(T_2\) | \(YP^{-1/24}\) | \(P^{119/192}\) |
| \(T_1\) | \(YP^{-1/48}\) | \(P^{257/384}\) |
| \(K_c\) | \(YP^{-1/96}\) | \(P^{533/768}\) |

against a target \(P^{17/24}=P^{544/768}\): margin \(P^{11/768}\).

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

Declarations: `absStep`, `absTail`, `absTail_eq` (the closed form
\((7y+a)/8\)), `A₁`, `companionY`, `saving`, `absTail_companion`,
`target_companion`, `absTail_lt_target`, `margin_companion`, `threshold_iff`,
`threshold_value`, `threshold_is_equality`, `half_lt_threshold`,
`threshold_lt_companion`, `proportional_chain`, `claimC_balance`,
`claimC_output`, `claimC_others_dominated`, `twist_negligible`,
`twist_exponent_neg`. Mathlib's three axioms only. This certifies the
arithmetic of the bookkeeping and no estimate, exactly as the threshold
certificate of Appendix A certifies no estimate.

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
\(\mathrm{TV}(\Delta_{2h_1}g)\le0.26P^{1/48+23/32+1/24-23/16}=0.26P^{-21/32}\).

**2 (EXACT — LEAN VERIFIED).** The arithmetic: the closed form, the value
\(533/768\) at \(y=23/32\), the strict inequality against \(17/24\), the margin
\(11/768\), the threshold equivalence and its value \(29/48\), that the
threshold exceeds \(1/2\) and is below \(23/32\), the halving chain
\(-1/24,-1/48,-1/96\), and the Claim C balance with its four dominated terms.

**3 (COMPUTATIONALLY VERIFIED).** The coverage audit and the two self-checks
above.

**4 (Correction to the record).** Section 8 estimated the localized kernel's
per-window absolute costs at \(P^{7/16}\). That is the depth-\(\le3\) figure;
the kernel's largest is \(P^{25/48}\). The consequence is not a failure but a
higher floor: the kernel localizes to \(P^{29/48}\) and not to \(P^{1/2}\), so
the two localizations of Section 8 are not interchangeable. The companion's
intervals are longer than \(P^{29/48}\), so nothing it needs is lost.

## Open questions

- Handling Lemma 3.8's transition term per window rather than absorbing it
  would lower the threshold below \(1/2\). Nothing currently needs that.
- The contagion arithmetic downstream. Section 8 prints \(0.5561\) for the two
  new words while its own production rule returns \(0.6066\); that discrepancy
  is the companion's to resolve and is untouched here.
- Whether the depth-five and depth-six productions need the twist at
  \(\lvert\ell\rvert\le P^{1/24}\) or a wider range.

## Decision

**PROMOTE.** The target is answered in the affirmative at the length the
companion needs, the theorem is in the manuscript, and it removes the item the
paper listed as the strongest thing it did not supply to its companion. The
branch also corrects a printed estimate. Its continuation is arithmetic
downstream, which belongs to the companion.

Best next question: does the localized kernel, fed through the production rule
with the two new words, give the printed \(0.5561\) or the \(0.6066\) the rule
returns?

## Publication assessment

Status: `THEOREM`. It is a subsection of Paper B, not a separate paper: it
proves nothing that Theorem 5.3 does not, and its interest is entirely that the
companion can now use it. The honest framing, which the subsection states, is
that the completeness of the unit inventory is what the theorem rests on, and
that a missing unit above \(P^{25/48}\) would raise the threshold without
touching the exponent.
