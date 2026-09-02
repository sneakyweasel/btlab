# Juggler finite-itinerary envelope defect and strictness

Status: **DEFECT_QUANTITATIVE_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Mixed-word *local* strictness remains
REFUTED. This page records the distance from the one-sided envelope
after the first non-exact branch.

## Branch budget

```text
Mathematical target     Can the first non-exact branch produce a
                        compositional lower bound on Δ_w(n)?
Novelty hypothesis      A local defect δ>0 persists through suffix
                        power maps and yields a reusable strict bound.
Falsifier               DEFECT_NO_SIMPLE_BOUND
Existing machinery      PowerBound, PowerBoundEq, extremal iff,
                        local even/odd square inequalities
Maximum Phase-0 scope   Local defects; StrictPowerBound + append;
                        non-monochrome ⇒ strict; first-defect probe
                        without huge powers. No PowerHeight, no engine edits.
```

## Metadata

- domain layer: `n <= 400`, `k <= 6`
- engine control layer modified: `False`
- classification: **DEFECT_QUANTITATIVE_GREEN**
- computed deficits: `1553`
- mixed computed: `915`
- bit-budget skips: `818`
- unit falsifiers: `0`
- Δ < δ_j falsifiers: `0`
- suffix decreases: `0`
- sorry-free: `True`

A positive first local defect persists through every realized suffix, and the final envelope deficit is at least that defect.

## Local defects

Even: `δ_E(x) = x - T(x)^2`. If `x = q^2 + r` with `0 < r < 2q+1`,
then `T(x) = q` and `δ_E(x) = r`.

Odd: `δ_O(x) = x^3 - T(x)^2`, the integer remainder of `x^3`
under `isqrt`.

- even remainder identity: `True`
- odd cube-remainder identity: `True`
- smallest even non-square defect: `{'n': 2, 'local_defect': 1, 'q': 1, 'r': 1}`
- smallest odd non-square defect: `{'n': 3, 'local_defect': 2, 'q': 5, 'r': 2}`
- odd defect 1 in the local window: `None`

## Witnesses

- word `EO` at 10: first defect `1`,
  Δ `375`
- word `OE` at 15: first defect `11`,
  Δ `974`
- word `OOE` at 9: first defect at 27, δ `83`,
  Δ `173061608`
- word `EEEO` at 36: first defect at 6, δ `2`,
  Δ `46655`
- word `E` at 2: unit defect, Δ `1`
- word `O` at 9 has no first defect: `True`

Same-count mixed itineraries with different first-defect positions do not
obey a position-only order. The certified lower bound uses the first
local defect, not the letter counts. Split groups: `3`.

## Lean

- `localDefectEven_eq_zero_iff`: `True`
- `localDefectOdd_eq_zero_iff`: `True`
- `strict_power_bound_append_even`: `True`
- `strict_power_bound_append_odd`: `True`
- `strict_power_bound_from`: `True`
- `power_bound_word_strict`: `True`
- `power_bound_defect_ge_one`: `True`
- `power_deficit_append_even`: `True`
- `power_deficit_append_odd`: `True`
- `power_deficit_from`: `True`
- `local_defect_even_le_suffix_deficit`: `True`
- `local_defect_odd_le_suffix_deficit`: `True`
- `StrictPowerBound` definition: `True`
- `powerDeficit` definition: `True`
- `PowerHeight` absent: `True`
- `PowerBoundStrict` absent: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**DEFECT_QUANTITATIVE_GREEN**

A positive first local defect persists through every realized suffix, and the final envelope deficit is at least that defect.

This is a finite-itinerary defect statement, not a global halt result.

