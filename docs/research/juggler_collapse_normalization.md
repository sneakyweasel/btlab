# Juggler collapse normalization

Status: **COLLAPSE_DEPTH_TOO_WEAK**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. An initial even run is a scale change.
Bounded initial even-run length is not enough to restore a family
threshold.

## Branch budget

```text
Mathematical target     T_{E^r u}(a^{2^r})=T_u(a); does bounded r restore Q?
Novelty hypothesis      Collapse depth is the missing family variable
Falsifier               Bounded initial even-run with unbounded contracting q
Existing machinery      iterate_even_pow_two_eq, image_append
Maximum Phase-0 scope   Decomposition; residual identity; bounded-r scan
```

## Metadata

- identity ok: `True`
- engine control layer modified: `False`
- classification: **COLLAPSE_DEPTH_TOO_WEAK**
- sorry-free: `True`

E^r u on a^{2^r} reduces to u on a, but initial even-run length 0 still admits O E^k O^{3k} contractions at arbitrarily large scanned q; the extra parameter is the longest even run.

## Even-tower residuals

- k=`2` q=`4` residual_state=`1` T=`1` r=`2`
- k=`3` q=`16` residual_state=`1` T=`1` r=`3`
- k=`4` q=`256` residual_state=`1` T=`1` r=`4`
- k=`5` q=`65536` residual_state=`1` T=`1` r=`5`

## Internal collapse `O E^k O^{3k}`

- k=`3` q=`17` r=`0` maxE=`3` T=`1`
- k=`4` q=`345` r=`0` maxE=`4` T=`1`
- k=`5` q=`19955` r=`0` maxE=`5` T=`1`

## Lean witness `q=7`

- word=`OEEEOOOOOOOOO` follows=`True` T=`1` superquadratic=`True`

## Lean

- `initialEvenRun`: `True`
- `stripInitialEven`: `True`
- `initial_even_decomposition`: `True`
- `iterate_even_pow_two_eq`: `True`
- `collapse_residual_identity`: `True`
- `collapse_on_pow_two`: `True`
- `collapse_tower_contracts_iff`: `True`
- `even_tower_collapse_residual`: `True`
- `odd_then_even_collapse`: `True`
- `odd_even_tower_seven`: `True`
- `wordOEEE9`: `True`
- `odd_even_tower_seven_superquadratic`: `True`
- `floorPower_iterate_even_pow_two_eq`: `True`
- `image_append`: `True`
- `eventually_no_first_even_contraction`: `True`
- `changing_suffix_unbounded_contraction`: `True`
- `first_even_freeze`: `True`
- certificate unchanged: `True`
- `PowerHeight` absent: `True`
- no bounded-collapse theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**COLLAPSE_DEPTH_TOO_WEAK**

E^r u on a^{2^r} reduces to u on a, but initial even-run length 0 still admits O E^k O^{3k} contractions at arbitrarily large scanned q; the extra parameter is the longest even run.

The fixed-itinerary theorem remains. This is not a halt result.

