# Juggler leftover-cell lag

Status: **LEFTOVER_CELL_LAG_STAYS_ONE**

Standalone diagnostic. Not a Research Engine experiment
and not a termination theorem. The leftover prefix-cell
for the trailing-evens family O^a E^e is compared at the
first expanding a_*(e) and a few odds later.

## Branch budget

```text
Mathematical target     Does leftover-cell lag of O^{a_*(e)} E^e
                        stay 1 as e grows, or grow?
Novelty hypothesis      lag grows, so leftover induction is
                        permanently parked for e>=4
Falsifier               lag stays 0 or 1 through e<=16
Existing machinery      leftover_prefix_preimage; denomBits; Z=(n+1)^{2^e}
Maximum Phase-0 scope   N0 at a_*, a_*+1, a_*+2 for e=2..16;
                        no Lean, no Z5, no thirty shapes
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **LEFTOVER_CELL_LAG_STAYS_ONE**
- sorry-free: `True`

lag is 0 or 1 on e=2..16; max lag 1; a_*+1 always fires in the window. Leftover induction is a per-e census, not a unifying method.

## Lag table

- e range: `2`..`16`
- window: `800`
- lags: `[0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0]`
- max lag: `1`
- min lag: `0`
- lag grows to 2 or more: `False`
- max N0 at a_*+1: `59`
- e=4 a_*: `7` N0(a_*+1)=`37`
- e=5 cell opened: `False`

| e | a_* | word | slack | N0(a_*) | N0(+1) | N0(+2) | lag |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 4 | `OOOOEE` | 17 | 205 | 14 | 8 | 0 |
| 3 | 6 | `OOOOOOEEE` | 217 | 73 | 13 | 8 | 0 |
| 4 | 7 | `OOOOOOOEEEE` | 139 | 828484409 | 37 | 11 | 1 |
| 5 | 9 | `OOOOOOOOOEEEEE` | 3299 | 3158 | 23 | 10 | 1 |
| 6 | 11 | `OOOOOOOOOOOEEEEEE` | 46075 | 197 | 17 | 9 | 0 |
| 7 | 12 | `OOOOOOOOOOOOEEEEEEE` | 7153 | None | 59 | 13 | 1 |
| 8 | 14 | `OOOOOOOOOOOOOOEEEEEEEE` | 588665 | 75005 | 30 | 11 | 1 |
| 9 | 16 | `OOOOOOOOOOOOOOOOEEEEEEEEE` | 9492289 | 536 | 19 | 9 | 0 |
| 10 | 18 | `OOOOOOOOOOOOOOOOOOEEEEEEEEEE` | 118985033 | 94 | 14 | 8 | 0 |
| 11 | 19 | `OOOOOOOOOOOOOOOOOOOEEEEEEEEEEE` | 88519643 | 79702513 | 39 | 12 | 1 |
| 12 | 21 | `OOOOOOOOOOOOOOOOOOOOOEEEEEEEEEEEE` | 1870418611 | 2330 | 23 | 10 | 1 |
| 13 | 23 | `OOOOOOOOOOOOOOOOOOOOOOOEEEEEEEEEEEEE` | 25423702091 | 173 | 16 | 9 | 0 |
| 14 | 24 | `OOOOOOOOOOOOOOOOOOOOOOOOEEEEEEEEEEEEEE` | 7551629537 | None | 54 | 13 | 1 |
| 15 | 26 | `OOOOOOOOOOOOOOOOOOOOOOOOOOEEEEEEEEEEEEEEE` | 342842572777 | 29088 | 28 | 11 | 1 |
| 16 | 28 | `OOOOOOOOOOOOOOOOOOOOOOOOOOOOEEEEEEEEEEEEEEEE` | 5284606410545 | 408 | 19 | 9 | 0 |

## Lean

- `leftover_prefix_preimage`: `True`
- `denomBits`: `True`
- `cycle_trailing_evens_lt`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycle_itinerary_three_even_eee`: `True`
- no `no_cycle_itinerary_five_even`: `True`
- no `no_cycle_itinerary_e5_cell`: `True`
- no `leftover_cell_lag_inductive`: `True`
- no `juggler_reaches_one`: `True`
- Paper A has no lag theorem: `True`
- FloorPower not rewritten: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycle_impossible: `False`
- finite_progress_for_all: `False`
- five_even_cell: `False`
- leftover_induction: `False`

## Decision

**LEFTOVER_CELL_LAG_STAYS_ONE**

lag is 0 or 1 on e=2..16; max lag 1; a_*+1 always fires in the window. Leftover induction is a per-e census, not a unifying method.

This is not a halt result and not a Z_5 family.
Do not write another leftover cell.

