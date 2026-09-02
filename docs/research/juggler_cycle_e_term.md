# Juggler E-terminating cycle exclusion

Status: **LAST_EVEN_CLASS_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. E-terminating cycles are
separated from O-terminating cycles.

## Branch budget

```text
Mathematical target     suffix threshold ⇒ no cycle vE; close length 4
Novelty hypothesis      OOE cell argument lifts to a reusable class
Falsifier               an expanding length-4 E-cycle other than OOOE
Existing machinery      cycle_last_even_interval, ooo_suffix_threshold
Maximum Phase-0 scope   generic theorem; OOOE; all length-4 E-words
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **LAST_EVEN_CLASS_GREEN**
- secondary: `['E_TERMINATING_LENGTH4_GREEN']`
- sorry-free: `True`

suffix threshold forbids any cycle vE once T_v sits at or above the next square; the only expanding length-4 E-terminating word is OOOE, and it is excluded.

## Length-4 E-terminating words

- `OOOE` o=`3` expanding=`True`
- `OOEE` o=`2` expanding=`False`
- `OEOE` o=`2` expanding=`False`
- `OEEE` o=`1` expanding=`False`
- `EOOE` o=`2` expanding=`False`
- `EOEE` o=`1` expanding=`False`
- `EEOE` o=`1` expanding=`False`
- `EEEE` o=`0` expanding=`False`

- unique expanding itinerary: `['OOOE']`

## Lean

- `cycle_last_even_cell`: `True`
- `cycle_last_even_cell_odd`: `True`
- `no_cycle_append_even_of_suffix_threshold`: `True`
- `no_cycle_itinerary_oooe`: `True`
- `no_cycle_itinerary_length_four_ends_even`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- MinimalNonTerm not rewritten: `True`
- PowerBoundEq not used as cycle attack: `True`
- O-terminating not claimed: `True`
- no all-cycles-impossible theorem: `True`
- no cycle engine: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- O_terminating_cycles_impossible: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`
- last_even_is_exact_square: `False`
- all_odd_orbit: `False`
- finite_progress_for_all: `False`

## Decision

**LAST_EVEN_CLASS_GREEN**

suffix threshold forbids any cycle vE once T_v sits at or above the next square; the only expanding length-4 E-terminating word is OOOE, and it is excluded.

This is not a halt result. Cycles ending in O are not treated.
Cycles are not proved impossible.

