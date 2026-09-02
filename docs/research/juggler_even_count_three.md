# Juggler even-count ≤ 3 cycle itineraries

Status: **EVEN_COUNT_THREE_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Even-count ≤ 3 only; not a
length-9 or length-10 census and not first-E at e>=4.

## Branch budget

```text
Mathematical target     Is every cycle word with at most
                        three even letters already excluded?
Novelty hypothesis      Theorems 3.12--3.21 plus bootstrap
                        and rotation partition e<=3
Falsifier               An e<=3 necklace that misses every
                        named filter
Existing machinery      leftover families; bootstrap;
                        exists_cycleMin; expansion filter
Maximum Phase-0 scope   Necklace inventory lengths 9..16;
                        one Lean even-count theorem; no
                        length census; Paper A Theorem 3.22
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **EVEN_COUNT_THREE_GREEN**
- sorry-free: `True`
- word count: `604`
- necklace count: `226`
- all allowed: `True`
- missed count: `0`
- necklaces covered: `True`
- class counts: `{'odd_run': 8, 'starts_even': 92, 'starts_OE': 84, 'bootstrap_ooo': 216, 'bootstrap_oo': 60, 'two_even_eoe': 8, 'two_even_ee': 8, 'gapped_eoe': 36, 'gapped_ee': 36, 'bunched_eooeoe': 8, 'bunched_eoooee': 8, 'bunched_eoeoe': 8, 'bunched_eooee': 8, 'bunched_eeoe': 8, 'bunched_eoee': 8, 'bunched_eee': 8}`

every even-terminating expanding word with e<=3 at lengths 9..16 hits a named filter or start-E/OE glue; Lean excludes every CycleItinerary with even-count <= 3, so a nontrivial cycle has period >= 11.

## Lean

- `evenCount`: `True`
- `no_cycleMin_even_count_le_three`: `True`
- `no_cycle_itinerary_even_count_le_three`: `True`
- `cycle_itinerary_even_count_ge_four`: `True`
- `cycle_itinerary_length_ge_eleven`: `True`
- `minimal_first_even_overshoots`: `True`
- `cycleMin_first_even_overshoots`: `True`
- `cycleMin_max_ge_succ_sq`: `True`
- `cycleMax_min_succ_sq_le`: `True`
- `cycleMax_landing_gt_min`: `True`
- `cycleMax_exists_min_succ_sq`: `True`
- `cycle_distinguished_order_succ_sq`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycle_itinerary_two_even_eoe`: `True`
- `no_cycle_itinerary_three_even_eee`: `True`
- `no_cycle_itinerary_three_even_eoee`: `True`
- `no_cycle_itinerary_three_even_eooee`: `True`
- `no_cycle_itinerary_three_even_eoooee`: `True`
- `no_cycle_itinerary_three_even_eeoe`: `True`
- `no_cycle_itinerary_three_even_eoeoe`: `True`
- `no_cycle_itinerary_three_even_eooeoe`: `True`
- `no_cycle_itinerary_gapped_three_even_ee`: `True`
- `no_cycle_itinerary_gapped_three_even_eoe`: `True`
- `no_cycleMin_internal_even_threshold`: `True`
- `exists_cycleMin`: `True`
- laboratory assembler present: `True`
- Paper A imports even-count: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- three_even_cycles_impossible: `True`
- even_count_le_three_impossible: `True`
- length_nine_census: `False`
- length_ten_census: `False`
- length_eleven_census: `False`
- first_e_at_four: `False`
- induction_on_period: `False`
- induction_on_n: `False`
- paper_a_edit: `False`

## Decision

**EVEN_COUNT_THREE_GREEN**

every even-terminating expanding word with e<=3 at lengths 9..16 hits a named filter or start-E/OE glue; Lean excludes every CycleItinerary with even-count <= 3, so a nontrivial cycle has period >= 11.

This is not a halt result and not a length-9 census.

