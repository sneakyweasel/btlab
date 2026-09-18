# Paper B: the Theorem 5.2--5.4 count assembly (Lean)

## Problem

Machine-check the Section 5 assembly of Paper B: that the five minimal
certificates partition the certified words, that the certified count of
`{1,...,N}` is the sum of the five printed prefix-class counts, and that the
printed error exponents dominate in the order the proofs assume.

## Exact statement

Let `certifiedWords d` be the length-`d` parity words with a contracting prefix
(`3^o < 2^L` at some nonempty prefix). Then:

1. `#certifiedWords 4 = 13`, `#certifiedWords 5 = 28`, `#certifiedWords 6 = 56`,
   `#certifiedWords 7 = 115`, so the densities are `13/16`, `7/8`, `7/8`, `115/128`.
2. At depth five the cylinders of `E`, `OE`, `OOEE`, `OOOEE`, `OOEOE` are pairwise
   disjoint with sizes `16, 8, 2, 1, 1` and their union is exactly
   `certifiedWords 5`.
3. For every `N`, the number of starts in `{1,...,N}` certified by depth five is
   `classCount E N + classCount OE N + classCount OOEE N + classCount OOOEE N +
   classCount OOEOE N`, where `classCount w N` counts starts whose length-`|w|`
   itinerary is `w`.
4. `5/6 < 23/24 < 47/48 < 127/128 < 1`, and `N^e <= N^f` for `e <= f`, `N >= 1`.
5. Given the five class counts within errors of their printed main terms, the
   total is within the sum of the errors of `7N/8`.
6. No word of length six is a minimal certificate; exactly three of length seven
   are, namely `OOEOOEE`, `OOOEOEE`, `OOOOEEE`.

## Current literature

`known` for (1)--(5): Paper B Section 5 in
[juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md).
`extended` for (6): the manuscript's Lemma 5.1 stops at length five and states
nothing about six or seven. No literature-wide priority claim.

## Branch budget

- **Target:** is the `7/8` of Theorem 5.4 the actual main-term arithmetic, and
  does the error-exponent chain of 5.2--5.4 close?
- **Novelty hypothesis:** first Lean coverage of the Section 5 count assembly;
  and Lemma 5.1 past the printed length five.
- **Falsifier:** cylinder counts not summing to the certified count, a length-5
  word in two cylinders, or `115/128` wrong.
- **Already killed by?:** none. [negative_knowledge.md](../negative_knowledge.md)
  kills the Paper A x B merge, local attacks, Baker/SdW, DK-arch free-kill,
  kernel localize and harvest counting; the Section 5 assembly is none of these,
  and the three tests concern cycle, termination and local attacks rather than a
  finite word partition. The certificates dossier
  ([juggler_paper_b_certificates.md](juggler_paper_b_certificates.md)) asks this
  exact question at its Decision line.
- **Existing machinery:** `RateFreeDensity` (`allWords`, `classCount`,
  `neverNegWords`, `classCount_fiber_disjoint`, `itinerary_take`),
  `PaperBCertificates` (`IsMinimalCertificate` and its `Decidable` instance),
  `ItineraryStats` (`exponentGap`, `oddCount`, `prefixNoncontracting`).
- **Maximum Phase-0 scope:** one Lean module, umbrella and `AUXILIARY_MODULES`
  wiring, dossier, ledger rows. No exponential sum.
- **Promotion criterion:** the partition and the real-start assembly
  kernel-checked, with every analytic count left as a hypothesis.
- **Stop criterion:** if the assembly cannot be stated without assuming a Fourier
  bound, `PARK` -- that would mean the split is not really combinatorial.

## Balanced-ternary formulation

Not used; the objects are parity words and counts of starts.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`exponentGap` (`3^o < 2^L`), minimality under proper prefixes, and the cylinder
of a word inside `allWords d`. Ledger tag for every statement below:
`EXACT — LEAN VERIFIED`.

## Experiments

Exact enumeration over all `2^d` words for `d = 1..9` gives certified densities
`1/2, 3/4, 3/4, 13/16, 7/8, 7/8, 115/128, 237/256, 237/256` and survivor counts
`N_d = 1, 1, 2, 3, 4, 8, 13, 19, 38`. The `N_d` agree with
`PaperBSurvivorDecay`'s kernel-computed `neverNegCount 5..8 = 4, 8, 13, 19`.
The density is flat at `d = 3, 6, 9`: no minimal certificate has those lengths.

## Conjectures

None.

## Counterexamples

None. The falsifier did not fire: `five_cylinders_cover` and
`five_cylinders_card_sum` both hold by `decide +kernel`.

## Formalization

`formal/Problems/Juggler/PaperBFiveStepDensity.lean`, imported by the umbrella
`Problems.Juggler` and registered in `AUXILIARY_MODULES`. Deliberately **not**
imported by the barrel `Problems.JugglerParityPaper`, which must stay disjoint
from Paper A's itinerary stack: this module depends on `RateFreeDensity` and
`PaperBCertificates`, both of which sit on that stack.

Thirty-eight declarations, no `sorry`. Key names: `certifiedWordCount_four/five/six/seven`,
`five_step_density`, `five_cylinders_cover`, `five_cylinders_card_sum`,
`printed_measures_are_counts`, `sum_classCount_cylinder`, `certifiedCount_five_eq`,
`no_minimal_certificate_six`, `minimal_certificates_seven`, `seven_step_density`,
`error_exponents_ordered`, `error_absorb`, `five_step_error_assembly`.

## Results

`J-paper-b-five-step-count-assembly` and
`J-paper-b-certificates-extend-to-length-seven` — both `EXACT — LEAN VERIFIED`.

The printed `1/2 + 1/4 + 1/16 + 1/32 + 1/32 = 7/8` was a `norm_num` identity
between five rational literals, proved twice (`PaperBCertificates.certificate_measures_sum`
and `DepthFourFive.cor64_density`) and attached to no set of words and no start.
`printed_measures_are_counts` and `five_cylinders_card_sum` now derive those five
literals from the cylinder sizes `16, 8, 2, 1, 1`, and `certifiedCount_five_eq`
carries the partition to a statement about starts.

## Open questions

The five class counts remain the whole content. Theorem 3.1 and Corollaries 4.6,
4.10 and 4.12 -- the van der Corput plus Erdos--Turan estimates -- have no Lean
anywhere, and Mathlib carries neither the second-derivative test nor
Erdos--Turan, so they are a foundational build-out rather than a next step.

The length-seven extension names its own price: `OOEOOEE`, `OOOEOEE` and
`OOOOEEE` would each need a mixed-mode estimate of their own before `115/128`
became a density rather than a word count.

## Decision

`PROMOTE` — the assembly is kernel-checked and the falsifier did not fire. The
`7/8` is now the number of certified words over the number of words, and the
depth-five certified count is provably a sum of five prefix-class counts, which
is the shape Theorems 5.2--5.4 assume. Nothing analytic was proved and the
manuscript's status is unchanged. Best next question: does the same partition
argument close at depth seven, i.e. is `certifiedCount 7 N` a sum of eight
prefix-class counts, so that the only missing input at the next rung is the
three new mixed-mode estimates?

## Publication assessment

Status: `THEOREM`. Supports Paper B Section 5 and supplies one small extension of
its Lemma 5.1, but does not make the preprint independently certified: every
analytic count it assembles is still a written proof.
