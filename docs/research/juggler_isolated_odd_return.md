# Juggler isolated-odd prefixes versus short-tail return fibres

Status: **ISO_ODD_RETURN_CLOSE**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Isolated-odd CycleMin landings
versus exact `R_{b,c}(n)`. Not Z5, not a length-11 assembler,
and not a four-even leftover cell.

## Branch budget

```text
Mathematical target     P_iso(n) ∩ R_{b,c}(n) empty?
Novelty hypothesis      isolated-odd landings miss the
                        exact short-tail fibres
Falsifier               a broad isolated-odd hit family
Existing machinery      oe_block_contracts; length ≤ 6
Maximum Phase-0 scope   OE block; family landings; no Lean
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **ISO_ODD_RETURN_CLOSE**
- sorry-free: `True`
- OE follows / contracts: `43` / `43`
- OE expands / fixed: `0` / `0`
- admissible isolated-odd words: `['', 'O']`
- extra CycleMin prefixes: `0`
- exact fibre hits: `0`
- empty / single-O hits: `0` / `0`

OE contracts below the CycleMin floor, so the only isolated-odd prefixes are empty and O; those plus a short tail are CycleItineraries of length at most 6.

## Attack 1 — OE block map

`oe_block_contracts`: if `2 ≤ x` and `x` follows `OE`, then
`B(x) = T_OE(x) < x`. The scan through odd `x ≤ 200` has follows=`43`,
contracts=`43`, expands=`0`,
fixed=`0`.

## Attacks 2–5 — landings versus fibres

The isolated-odd family is `O E^{k1} ⋯ O E^{kr}` and the same
words plus a terminal `O`. CycleMin-admissible members in the
window are `['', 'O']`. Extra prefixes:
`0`. Fibre hits:
`0`.

Empty and single-`O` landings plus a short tail are CycleItineraries
of length at most 6, already excluded.

## Lean

- `oe_block_contracts`: `True`
- `oe_block_scale`: `True`
- `no_cycle_itinerary_length_le_six`: `True`
- `CycleMin`: `True`
- `cycleMin_ge_twelve`: `True`
- `CycleItinerary`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- length_eleven_census: `False`
- z5_cells: `False`
- four_even_assembler: `False`

## Decision

**ISO_ODD_RETURN_CLOSE**

OE contracts below the CycleMin floor, so the only isolated-odd prefixes are empty and O; those plus a short tail are CycleItineraries of length at most 6.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler.

