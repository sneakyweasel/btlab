# Paper B: Lemma 5.1 minimal certificates (Lean)

## Problem

Machine-check the combinatorial classification behind Paper B Theorems
5.2--5.4: which words of length at most five are minimal power-envelope
certificates.

## Exact statement

The contracting words of length at most five with no proper nonempty
contracting prefix are exactly `E`, `OE`, `OOEE`, `OOOEE`, and `OOEOE`.
Their formal cylinder measures sum to `7/8`.

## Current literature

`known`: the classification is Paper B Lemma 5.1 in
[juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md).
No literature-wide priority claim.

## Branch budget

- **Target:** Lean proof of Lemma 5.1 and the `7/8` measure identity.
- **Novelty hypothesis:** first Lean coverage of the printed certificate list.
- **Falsifier:** a sixth length-`<=5` minimal certificate, or measure sum not `7/8`.
- **Already killed by?:** none — finite word enumeration; three tests do not apply.
- **Existing machinery:** `exponentGap`, `ItineraryStats.oddCount`, Envelope contractions.
- **Maximum Phase-0 scope:** one Lean module, barrel wiring, ledger row; no analysis.
- **Promotion criterion:** `lake build Problems.Juggler.PaperBCertificates` and
  umbrella import; barrel stays free of itinerary deps.
- **Stop criterion:** any need for exponential-sum estimates.

## Balanced-ternary formulation

Not used; the objects are parity words.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

`exponentGap` (`3^o < 2^L`) and minimality under proper prefixes.

## Experiments

Exact enumeration of all `2+4+8+16+32` words of length `1..5` confirms the five
certificates and measure sum `0.875`.

## Conjectures

None.

## Counterexamples

None.

## Formalization

`formal/Problems/Juggler/PaperBCertificates.lean`, imported by the umbrella
`Problems.Juggler` (not by `JugglerParityPaper`, which must stay disjoint from
Paper A's itinerary stack). Theorems `lemma51`, `certificate_measures_sum`,
`lemma51_complete`. No `sorry`.

## Results

`J-paper-b-lemma-5-1-minimal-certificates` — `EXACT — LEAN VERIFIED`.

## Open questions

The analytic counts that turn the five cylinders into
`7N/8 + O_epsilon(N^(127/128+epsilon))` remain outside Lean.

## Decision

`PROMOTE` — Lemma 5.1 is now kernel-checked; the barrel trust boundary is
unchanged for exponential sums. Best next question: can any further algebraic
piece of Theorems 5.2--5.4 (formal-chain to word-count, not the Fourier bound)
be formalised without analysis?

## Publication assessment

Status: `THEOREM`. Supports Paper B but does not by itself make the preprint
independently certified.
