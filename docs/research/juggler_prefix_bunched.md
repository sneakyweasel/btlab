# Juggler last three-even bunched leftover after an arbitrary prefix

Status: **PREFIX_BUNCHED_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Last three-even bunched leftovers
after any CycleMin prefix `u`; not a bunched-short attack, not Z5,
and not a length-11 assembler.

## Branch budget

```text
Mathematical target     CycleMin n (u ++ threeEvenXXX a)
                        is impossible for every prefix u
Novelty hypothesis      y>=n plus the path table at y replace
                        CycleItinerary tables at the cycle start
Falsifier               a path y -> n in [2,y] below cutoff,
                        or the large-y tail failing when y>=n
Existing machinery      seven bunched CycleItinerary exclusions;
                        CycleMin; family tails; seven-odd
Maximum Phase-0 scope   path census; Lean wrapper; no Z5,
                        no length-11, no bunched-short
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **PREFIX_BUNCHED_GREEN**
- sorry-free: `True`
- path tables empty: `True`
- path follows below cutoff: `6`
- a=3 coarse impossible: `True`
- seven-odd sealed: `True`

Lean excludes CycleMin n (u ++ bunched leftover) for every prefix u and all seven families; large y is the family tail at y; below cutoff no start follows the leftover into [2, y]; a=3 uses the tight split at y; bunched-short last cluster remains.

The coarse comparison `Y^{3^a} > 2^e (Y+1)^{K 2^a}` never
fires at a=3 for EOOOEE or EOOEOE. Those two cells use the
tight split already proved for CycleItinerary, measured at y.

## Path rows

- `OOOOOOEEE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOEOEE` follows=`1` hits=`0` overshoots=`1`
- `OOOOOOEOEE` follows=`1` hits=`0` overshoots=`1`
- `OOOOEOOEE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOEOOEE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOOEOOEE` follows=`0` hits=`0` overshoots=`0`
- `OOOEOOOEE` follows=`2` hits=`0` overshoots=`2`
- `OOOOEOOOEE` follows=`1` hits=`0` overshoots=`1`
- `OOOOOEOOOEE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOOEOOOEE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOEEOE` follows=`1` hits=`0` overshoots=`1`
- `OOOOOOEEOE` follows=`0` hits=`0` overshoots=`0`
- `OOOOEOEOE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOEOEOE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOOEOEOE` follows=`0` hits=`0` overshoots=`0`
- `OOOEOOEOE` follows=`0` hits=`0` overshoots=`0`
- `OOOOEOOEOE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOEOOEOE` follows=`0` hits=`0` overshoots=`0`
- `OOOOOOEOOEOE` follows=`0` hits=`0` overshoots=`0`

## Lean

- `CycleMin`: `True`
- `cycleMin_ge`: `True`
- `cycle_trailing_evens_lt`: `True`
- `three_even_eee_tail`: `True`
- `three_even_eoee_tail_of_five`: `True`
- `three_even_eoee_tail_of_six`: `True`
- `three_even_eooee_tail`: `True`
- `returnsIntoB`: `True`
- `no_cycleMin_prefix_eee`: `True`
- `no_cycleMin_prefix_eoee`: `True`
- `no_cycleMin_prefix_eooee`: `True`
- `no_cycleMin_prefix_eoooee`: `True`
- `no_cycleMin_prefix_eeoe`: `True`
- `no_cycleMin_prefix_eoeoe`: `True`
- `no_cycleMin_prefix_eooeoe`: `True`

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

**PREFIX_BUNCHED_GREEN**

Lean excludes CycleMin n (u ++ bunched leftover) for every prefix u and all seven families; large y is the family tail at y; below cutoff no start follows the leftover into [2, y]; a=3 uses the tight split at y; bunched-short last cluster remains.

This is not a halt result, not a bunched-short exclusion,
and not a length-11 assembler.

