# Juggler first-defect bound sharpness

Status: **DEFECT_SHARP_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Mixed-word *local* strictness remains
REFUTED. This page records when Δ_w(n) equals the first local defect.

## Branch budget

```text
Mathematical target     Can a nonempty suffix keep Δ_w(n)=δ_j, or does
                        every later branch strictly amplify?
Novelty hypothesis      Either every |v|>0 is strict, or equality is a
                        rigid exact-even suffix on T(n)
Falsifier               DEFECT_SUFFIX_COUNTEREXAMPLE to a proposed
                        universal amplification law; or no structural
                        equality
Existing machinery      localDefect, powerDeficit, append monotonicity,
                        HasPowTwoDepth, exact even towers
Maximum Phase-0 scope   Cheap Δ=δ_j search; trivial vs nontrivial;
                        one-step algebra; Lean only for the equality
                        law that survives
```

## Metadata

- domain layer: `n <= 400`, `k <= 6`
- engine control layer modified: `False`
- classification: **DEFECT_SHARP_GREEN**
- computed deficits: `1553`
- nonempty sharp: `37`
- nonempty sharp mixed: `1`
- law falsifiers: `0`
- constructed family sharp: `True`
- mixed long-suffix hits: `0`
- sorry-free: `True`

A nonempty suffix preserves Δ = δ_j exactly when it is an exact even tower on T(n) after a first defect at the start.

## Sharpness law

After a first defect at the start, `Δ = δ_j` if and only if the
remaining word is an exact even tower on `T(n)`. An odd letter or
an inexact even letter strictly increases the deficit. A nonempty
exact prefix already makes `Δ > δ_j` before any suffix is applied.

Universal `|v|>0 ⇒ Δ > δ_j` is therefore false, but the first-defect
bound is optimal: it is attained on an infinite exact-even family.

## Witnesses

- mixed `OE` at 11: Δ `35`
  equals δ `35`
- even `EE` at 18: Δ `2`
  equals δ `2`
- even `EEE` at 258: Δ `2`
  equals δ `2`
- trivial `E` at 2: Δ `1`
- prefix then empty suffix `OO` at 9: Δ
  `3260489` > δ
  `83`
- amplified `OE` at 7: Δ `87`
  > δ `19`

## Lean

- `powerDeficit_even_first`: `True`
- `powerDeficit_odd_first`: `True`
- `power_deficit_append_even_eq`: `True`
- `power_deficit_append_even_of_defect`: `True`
- `power_deficit_append_odd_of_strict`: `True`
- `even_defect_gap_gt_of_pos_prefix`: `True`
- `odd_defect_gap_gt_of_pos_prefix`: `True`
- `suffix_deficit_eq_of_exact_even`: `True`
- `suffix_eq_of_deficit_eq`: `True`
- `power_deficit_eq_local_even_iff`: `True`
- `power_deficit_eq_local_odd_iff`: `True`
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

**DEFECT_SHARP_GREEN**

A nonempty suffix preserves Δ = δ_j exactly when it is an exact even tower on T(n) after a first defect at the start.

This is a finite-itinerary sharpness statement, not a global halt result.

