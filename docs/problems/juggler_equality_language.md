# Juggler equality-word language and parity rigidity

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Which realized finite parity itineraries can saturate the one-sided
floor-power envelope? In particular, must every equality word be
monochrome, \(E^k\) or \(O^k\)?

## Exact statement

If a realized itinerary \(w\) of length \(k\) attains

\[
T_w(n)^{2^k}=n^{3^{\#O(w)}},
\]

is \(w\) equal to \(E^k\) or \(O^k\)? If so, are the two families
exactly the even-base and odd-base towers

\[
a^{2^k}\xrightarrow{E^k}a
\qquad\text{and}\qquad
a^{2^k}\xrightarrow{O^k}a^{3^k}?
\]

This is a local arithmetic question. It is not a termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-16 (`juggler_power_algebra`): equality rigidity
  **EXACT — LEAN VERIFIED**. Mixed-word *strictness* remains
  **REFUTED** at word `O`, \(n=9\). That refutation is one-letter
  equality, not a both-letter equality word.
- Phase-17 (`juggler_saturation_budget`): saturation budget
  **EXACT — LEAN VERIFIED**. **extended** here by asking which words
  can saturate.

## Branch budget

```text
Mathematical target     Must a realized equality word be E^k or O^k?
Novelty hypothesis      Exact perfect-power states keep the base parity,
                        so the itinerary cannot switch letters.
Falsifier               MIXED_EQUALITY_WORD_FOUND
Existing machinery      HasPowTwoDepth, exact E/O transitions, rigidity,
                        saturation budget, local-tightness probe
Maximum Phase-0 scope   Parity lemmas; monochromatic theorem; exact E^k/O^k
                        trajectories if cheap; mixed-word probe. No
                        PowerHeight, no census, no engine edits.
Promotion criterion     Lean proves monochromaticity, or a minimized mixed
                        witness is recorded
Stop criterion          PowerHeight; equality-word automaton; termination
                        claim; engine control edits
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Parity of \(a^e\) equals parity of \(a\) for \(e\ge 1\) —
  **EXACT — LEAN VERIFIED**
- Exact branches preserve base parity —
  **EXACT — LEAN VERIFIED**
- Equality implies \(w=E^k\) or \(w=O^k\) —
  **EXACT — LEAN VERIFIED**
- Even family \(T^k(a^{2^k})=a\) —
  **EXACT — LEAN VERIFIED**
- Odd family \(T^k(a^{2^k})=a^{3^k}\) —
  **EXACT — LEAN VERIFIED**
- Equality-itinerary census / `PowerHeight` — not added

## Experiments

- Probe: `research.juggler_sequence.equality_language`
- Mixed-word search via local tightness; no `cmp_pow` on \(n^{3^o}\)
- Records: [juggler_equality_language.md](../research/juggler_equality_language.md),
  [juggler_equality_language.json](../research/juggler_equality_language.json)
- Tests: `tests/research/juggler_sequence/test_equality_language.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened. Monochromaticity, if proved, is a theorem. A catalogue of
numeric witnesses is not a conjecture.

## Counterexamples

- Mixed-word *strictness* remains refuted at word `O`, \(n=9\).
- No `MIXED_EQUALITY_WORD_FOUND` on the searched domain.

## Formalization

`formal/Problems/Engine/FloorPower.lean`. Added:

- `even_iff_pow_even` / `odd_iff_pow_odd`
- `floorPower_sq_preserves_parity`
- `floorPower_pow_two_depth_preserves_parity`
- `power_bound_eq_implies_monochrome`
- `floorPower_iterate_even_pow_two_eq`
- `floorPower_iterate_odd_pow_two_eq`
- `follows_replicate_even_pow_two` / `follows_replicate_odd_pow_two`
- `power_bound_eq_iff_extremal`
- `two_pow_two_pow_extremal_even` / `three_pow_two_pow_extremal_odd`
- `odd_equality_three_pow_le`

No `PowerHeight`. No `sorry`. No ledger row. Existing `PowerBound` and
saturation-budget theorems are unchanged.

## Results

Classification **EXTREMAL_FAMILY_GREEN**.

Envelope equality for a realized itinerary \(w\) is equivalent to one of the
two monochrome towers:

\[
a^{2^k}\xrightarrow{E^k}a
\qquad (a\text{ even}),
\qquad
a^{2^k}\xrightarrow{O^k}a^{3^k}
\qquad (a\text{ odd}).
\]

The even family is formally contracting. The odd family is formally
expanding. For \(n\ge 2\), the even minimum is \(2^{2^k}\). For
\(n\ge 3\), the odd minimum is \(3^{2^k}\).

Computational search (\(n\le 10^4\), depth 8; square towers; prescribed
mixed itineraries `EO`, `OE`, and short alternations): 0
`MIXED_EQUALITY_WORD_FOUND`. This is not a termination theorem.

## Open questions

What exact deficit does a non-monochrome realized itinerary have relative to
the weak envelope? Do not census equality words. Do not return to
global termination from this lemma.

## Decision

**PROMOTE** the monochromatic equality-language theorem and the two
extremal families. Record `EXTREMAL_FAMILY_GREEN`. Do not register an
attack. Do not claim termination.

Best next question: what exact deficit does a non-monochrome realized
word have relative to the one-sided envelope?

## Publication assessment

Status: `EXPLORATORY`. A local equality-language lemma, not a paper
candidate and not a Juggler totality result.
