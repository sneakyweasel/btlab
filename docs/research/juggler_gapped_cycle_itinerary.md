# Juggler gapped three-even CycleItinerary leftovers

Status: **GAPPED_CYCLE_WORD_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Gapped three-even leftovers
only; not a length-8/9 census and not first-E at e>=4.

## Branch budget

```text
Mathematical target     Are gapped three-even leftovers
                        impossible as CycleItineraries?
Novelty hypothesis      Every CycleMin rotation is already
                        excluded; y<n is irrelevant
Falsifier               A bunched or unclassified rotation
Existing machinery      exists_cycleMin; first-E CycleMin;
                        bootstrap; end-odd / start-even / OE
Maximum Phase-0 scope   Classify rotations; Lean both
                        families; no census
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **GAPPED_CYCLE_WORD_GREEN**
- sorry-free: `True`
- row count: `1099`
- all allowed: `True`
- forbidden count: `0`
- class counts: `{'gapped_ee': 35, 'ends_odd': 868, 'bootstrap_oo': 11, 'starts_even': 35, 'gapped_eoe': 42, 'starts_OE': 42, 'bootstrap_ooo': 66}`

every rotation of a gapped three-even leftover is a CycleMin class already excluded; Lean upgrades both families to CycleItinerary; not a length-8/9 census.

## Lean

- `exists_cycleMin`: `True`
- `cycleItinerary_rotateItinerary`: `True`
- `cycleMin_not_end_odd`: `True`
- `cycleMin_not_start_even`: `True`
- `cycleMin_not_odd_even`: `True`
- `no_cycleMin_internal_even_threshold`: `True`
- `no_cycleMin_gapped_three_even_ee`: `True`
- `no_cycleMin_gapped_three_even_eoe`: `True`
- `no_cycle_itinerary_gapped_three_even_ee`: `True`
- `no_cycle_itinerary_gapped_three_even_eoe`: `True`
- length eight open in census: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- three_even_cycles_impossible: `False`
- gapped_cycle_itinerary_lean: `True`
- length_eight_census: `False`
- length_nine_census: `False`
- first_e_at_four: `False`
- induction_on_period: `False`
- induction_on_n: `False`

## Decision

**GAPPED_CYCLE_WORD_GREEN**

every rotation of a gapped three-even leftover is a CycleMin class already excluded; Lean upgrades both families to CycleItinerary; not a length-8/9 census.

This is not a halt result and not a length-8/9 census.

