# Juggler cycle-itinerary arithmetic

Status: **OOE_CYCLE_EXCLUDED**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Last-even cycle return is the
square cell, not `z = n^2`.

## Branch budget

```text
Mathematical target     exclude CycleItinerary on OOE and OEO by exact cells
Novelty hypothesis      last-even cell plus OO threshold, or rotation to EOO
Falsifier               an OOE/OEO cycle; or last-even identity z = n^2
Existing machinery      CycleItinerary, oo_suffix_threshold, no_cycle_itinerary_eoo
Maximum Phase-0 scope   last-even interval; min odd; no OOE; no OEO
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **OOE_CYCLE_EXCLUDED**
- secondary: `['OEO_CYCLE_EXCLUDED', 'CYCLE_STRUCTURE_GREEN']`
- sorry-free: `True`

OOE is excluded by the last-even cell against the OO suffix threshold; OEO rotates onto EOO; the cycle minimum is odd; last-even return is not z = n^2.

## Scan

- OOE hits in 2..79: `[]`
- OEO hits in 2..79: `[]`
- OOE at 3 follows: `False`
- last-even exact-square hits: `[]`
- OEO rotates to EOO: `True`

## Lean

- `cycle_last_even_interval`: `True`
- `cycle_last_even_ne_odd_sq`: `True`
- `cycle_last_odd_interval`: `True`
- `cycleItinerary_rotate_cons`: `True`
- `exists_cycle_min_odd`: `True`
- `floorPower_even_lt`: `True`
- `no_cycle_itinerary_ooe`: `True`
- `no_cycle_itinerary_oeo`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- MinimalNonTerm not rewritten: `True`
- PowerBoundEq not used as cycle attack: `True`
- no exact-square identity: `True`
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
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`
- last_even_is_exact_square: `False`
- all_odd_orbit: `False`
- finite_progress_for_all: `False`

## Decision

**OOE_CYCLE_EXCLUDED**

OOE is excluded by the last-even cell against the OO suffix threshold; OEO rotates onto EOO; the cycle minimum is odd; last-even return is not z = n^2.

This is not a halt result. Cycles are not proved impossible.
Last-even return is not `z = n^2`.

