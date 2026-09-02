# Juggler internal even-run collapse

Status: **BOUNDED_RUN_COUNTEREXAMPLE**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Internal even runs reduce to residual
evaluation. Bounded max even-run length is not a useful family bound.

## Branch budget

```text
Mathematical target     Does bounding internal even runs restore a family bound?
Novelty hypothesis      Numeric collapse to a small basin is the obstruction
Falsifier               maxEvenRun ≤ R with unbounded contracting q
Existing machinery      image_append, collapse_on_pow_two, odd_even_tower_seven
Maximum Phase-0 scope   Run census; nested R=3 family; Lean residual identity
```

## Metadata

- engine control layer modified: `False`
- classification: **BOUNDED_RUN_COUNTEREXAMPLE**
- sorry-free: `True`

maxEvenRun=3 still admits nested E^3 O collapses onto 1 at q=7, 2500, 6250000, and a 121-bit q; the mechanism is numeric collapse to the inert basin 1.

## Nested `maxEvenRun = 3` family

- `OEEE_O9` q=`7` T=`1` maxE=`3` contracts=`True`
- `EE_OEEE_O12` q=`2500` T=`1` maxE=`3` contracts=`True`
- `EEE_OEEE_O12` q=`6250000` T=`1` maxE=`3` contracts=`True`
- `layer2_z33933` q=`121 bits` T=`1` maxE=`3` contracts=`True`

## Short-word `q_max` by max even-run

- maxE=`0` word=`OO` q_max=`3` T=`11`
- maxE=`1` word=`EOOOO` q_max=`2` T=`1`
- maxE=`2` word=`EEOOOOOO` q_max=`8` T=`1`

## Short contractions with T>1

- `OO` q=`3` T=`11`

## Lean

- `maxEvenRun`: `True`
- `internal_even_collapse`: `True`
- `collapse_basin_one`: `True`
- `nested_even_collapse_2500`: `True`
- `nested_even_collapse_2500_superquadratic`: `True`
- `maxEvenRun_itineraryEE_OEEE12`: `True`
- `odd_even_tower_seven`: `True`
- `collapse_on_pow_two`: `True`
- `image_append`: `True`
- `eventually_no_first_even_contraction`: `True`
- `changing_suffix_unbounded_contraction`: `True`
- `first_even_freeze`: `True`
- certificate unchanged: `True`
- `PowerHeight` absent: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**BOUNDED_RUN_COUNTEREXAMPLE**

maxEvenRun=3 still admits nested E^3 O collapses onto 1 at q=7, 2500, 6250000, and a 121-bit q; the mechanism is numeric collapse to the inert basin 1.

The fixed-itinerary theorem remains. This is not a halt result.

