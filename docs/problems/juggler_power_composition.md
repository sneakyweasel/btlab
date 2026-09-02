# Juggler one-sided floor-power composition

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Is the surviving one-sided envelope \(T_w(n)^{2^{|w|}}\le n^{3^{\#O(w)}}\)
a compositional theorem of realized finite parity itineraries, or only an
empirical regularity requiring word-specific proofs?

## Exact statement

For every finite parity itinerary \(w\) realized by the Juggler orbit of a
positive integer \(n\),

\[
T^{|w|}(n)^{2^{|w|}}\le n^{3^{\#O(w)}}.
\]

If additionally \(3^{\#O(w)}<2^{|w|}\) and \(n\ge 2\), then
\(T^{|w|}(n)<n\). Equality is permitted in the weak bound.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Phase-12: `OOOEE` implies \(T^5(n)<n\) for \(n\ge 2\). **extended**.
- Phase-13 (`juggler_power_itineraries`): two-sided exponent law **REFUTED**;
  one-sided bound computationally survived. This phase packages that
  envelope as an inductive theorem.

## Branch budget

```text
Mathematical target     Does every realized finite parity itinerary satisfy
                        T_w(n)^{2^k} <= n^{3^o} by inductive floor composition?
Novelty hypothesis      OOOEE / OOOEEEOO are instances of one weak bound plus
                        an exponent-gap contraction corollary.
Falsifier               A realized (w,n) with T_w(n)^{2^k} > n^{3^o}.
Existing machinery      power_itineraries cmp_pow; FloorPower even/odd square bounds;
                        pow_sq_le / pow_sq_le_cube.
Maximum Phase-0 scope   Near-equality scan reusing power_itineraries; then a tiny
                        Lean API if the weak bound survives. No engine edits.
Promotion criterion     Weak bound proved for arbitrary realized finite itineraries;
                        existing block contractions follow; no termination claim.
Stop criterion          A onesided counterexample; a second transition engine;
                        a general-word tactic; a frequency theorem.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `PowerBound m n k o` meaning \(m^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED**
- Append even: \((k,o)\mapsto(k+1,o)\) — **EXACT — LEAN VERIFIED**
- Append odd: \((k,o)\mapsto(k+1,o+1)\) — **EXACT — LEAN VERIFIED**
- Strict corollary from \(3^o<2^k\) and \(n\ge 2\) —
  **EXACT — LEAN VERIFIED**
- Two-sided expanding reverse inequality — **REFUTED** (Phase-13)

## Experiments

- Probe: `research.juggler_sequence.power_composition`
- Reuses `research.juggler_sequence.power_itineraries` (`cmp_pow`, itinerary)
- Near-equality focus plus the Phase-13 sweep \(1\le n\le 10^6\),
  \(|w|\le 8\)
- Records: [juggler_power_composition.md](../research/juggler_power_composition.md),
  [juggler_power_composition.json](../research/juggler_power_composition.json)
- Tests: `tests/research/juggler_sequence/test_power_composition.py`

## Conjectures

None opened. The weak bound is a theorem, not a conjecture. Whether
every long trajectory contains a negative-drift word remains out of
scope.

## Counterexamples

- Two-sided expanding law remains refuted at `OO`, \(n=3\).
- No counterexample to the weak one-sided bound was found.
- Mixed-word equality was not observed; equality is the square-tower
  family and the odd fixed point \(n=1\).

## Formalization

`formal/Problems/Engine/FloorPower.lean`. API:

- `power_bound_empty`
- `power_bound_append_even`
- `power_bound_append_odd`
- `power_bound_follows`
- `power_bound_contracts`

Instances: `floorPower_oooee_of_follows`,
`floorPower_oooeeeoo_of_follows`. Existing nested-hyp theorems
`floorPower_oooee_five_step_lt` and
`floorPower_oooeeeoo_eight_step_lt` remain. No `sorry`. No ledger row
(elementary floor arithmetic).

## Results

Classification **POWER_COMPOSITION_GREEN**.

The predicate \(P_k(m,n,o)\equiv m^{2^k}\le n^{3^o}\) is preserved by
appending an even branch or an odd branch. Every realized finite itinerary
therefore satisfies the one-sided envelope. If \(3^o<2^k\) and
\(n\ge 2\), the exponent gap yields \(T_w(n)<n\). `OOOEE` and
`OOOEEEOO` are instances.

This is not a termination theorem.

## Open questions

When does equality \(T_w(n)^{2^k}=n^{3^o}\) occur for mixed itineraries, if
ever? Secondary; do not delay the weak theorem, which is already proved.

## Decision

**PROMOTE** the one-sided finite-itinerary power calculus
(`power_bound_follows` and `power_bound_contracts`). Record the
classification `POWER_COMPOSITION_GREEN`. Do not register an attack.
Do not claim that trajectories contain negative-drift words.

Best next question: is mixed-word equality possible, or is equality
generated only by even perfect-power towers and the odd fixed point
\(n=1\)?

## Publication assessment

Status: `EXPLORATORY`. A local exact composition lemma, not a paper
candidate and not a Juggler totality result.
