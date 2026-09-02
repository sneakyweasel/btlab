# Juggler last two-even leftover after an arbitrary prefix

Status: **PREFIX_TWO_EVEN_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Last two-even leftovers after
any CycleMin prefix `u`; not a bunched-short attack, not Z5,
and not a length-11 assembler.

## Branch budget

```text
Mathematical target     CycleMin n (u ++ twoEvenEE/EOE k)
                        is impossible for every prefix u
Novelty hypothesis      y>=n plus the path table at y<256
                        replace first-E tables-for-(a,b)
Falsifier               a path y<256 -> n in [2,y], or the
                        large-y tail failing when y>=n
Existing machinery      two-even leftovers; first-E transport;
                        CycleMin; shared tail; seven-odd
Maximum Phase-0 scope   path census y<256; Lean wrapper;
                        no Z5, no length-11, no bunched-short
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **PREFIX_TWO_EVEN_GREEN**
- sorry-free: `True`
- path tables empty: `True`
- path follows below 256: `10`
- algebra fail pairs at k=6: `2375`
- seven-odd sealed: `True`

Lean excludes CycleMin n (u ++ two-even leftover) for every prefix u; large y is the shared tail at y; below 256 no start follows the leftover and returns into [2, y]; k>=9 EE and k>=10 EOE are seven-odd on the remainder; bunched-short last cluster remains.

The n-cell comparison `y^{3^{k-2}} > 2^{e}(n+1)^{2^k}` fails
for some `12 <= n < y < 256` at `k=6`. Those pairs do not
realize the leftover. The path table is the small-y seal,
not the loose algebra.

## Path rows

- `OOOOEE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOEE` follows=`3` hits=`0` overshoots=`3`
- `OOOOOOEE` follows=`0` hits=`0` overshoots=`0`
- `OOOEOE` follows=`3` hits=`0` overshoots=`3`
- `OOOOEOE` follows=`2` hits=`0` overshoots=`2`
- `OOOOOEOE` follows=`1` hits=`0` overshoots=`1`
- `OOOOOOEOE` follows=`1` hits=`0` overshoots=`1`

## Lean

- `CycleMin`: `True`
- `cycleMin_ge`: `True`
- `cycle_trailing_evens_lt`: `True`
- `shared_two_even_tail`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycle_itinerary_two_even_eoe`: `True`
- `no_cycleMin_gapped_three_even_ee`: `True`
- `no_cycleMin_gapped_three_even_eoe`: `True`
- `returnsIntoB`: `True`
- `no_cycleMin_prefix_two_even_ee`: `True`
- `no_cycleMin_prefix_two_even_eoe`: `True`

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
- bunched_short_attack: `False`

## Decision

**PREFIX_TWO_EVEN_GREEN**

Lean excludes CycleMin n (u ++ two-even leftover) for every prefix u; large y is the shared tail at y; below 256 no start follows the leftover and returns into [2, y]; k>=9 EE and k>=10 EOE are seven-odd on the remainder; bunched-short last cluster remains.

This is not a halt result, not a bunched-short exclusion,
and not a length-11 assembler.

