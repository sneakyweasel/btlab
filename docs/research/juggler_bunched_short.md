# Juggler bunched-short last-cluster residual

Status: **BUNCHED_SHORT_PARK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Leftover-suffix path tables for
bunched-short `a < a_min`; not Z5, not a length-11 assembler,
and not a four-even cell.

## Branch budget

```text
Mathematical target     Does the leftover-suffix path table
                        seal CycleMin n (u ++ short leftover)?
Novelty hypothesis      short leftovers never return into [12,y]
Falsifier               a return 12 <= n <= y
Existing machinery      prefix bunched; last-cluster split;
                        CycleMin n>=12
Maximum Phase-0 scope   path census; window split; no Lean,
                        no Z5, no length-11
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **BUNCHED_SHORT_PARK**
- sorry-free: `True`
- short leftovers: `30`
- follows below 256: `187`
- hits [2,y]: `160`
- hits [12,y]: `18`
- overshoots: `0`
- isolated-odd e>=5 exists: `True`

short leftovers return into [12, y]; the leftover-suffix path table is not a seal; isolated-odd e>=5 shapes exist; e=4 short-first-gap is already PARK; no new cell.

## Path rows with n>=12 hits

- `OOOOOEEE` follows=`2` n>=12=`2` expanding=`False` samples=`[{'y': 129, 'n': 100}, {'y': 209, 'n': 159}]`
- `OOOEOEE` follows=`2` n>=12=`2` expanding=`False` samples=`[{'y': 81, 'n': 16}, {'y': 87, 'n': 16}]`
- `OOEOOEE` follows=`2` n>=12=`2` expanding=`False` samples=`[{'y': 69, 'n': 14}, {'y': 109, 'n': 19}]`
- `OOOEOOEE` follows=`2` n>=12=`2` expanding=`False` samples=`[{'y': 99, 'n': 78}, {'y': 247, 'n': 186}]`
- `OEOOOEE` follows=`3` n>=12=`3` expanding=`False` samples=`[{'y': 135, 'n': 21}, {'y': 231, 'n': 31}]`
- `OOEOOOEE` follows=`1` n>=12=`1` expanding=`False` samples=`[{'y': 105, 'n': 82}]`
- `OOOEEOE` follows=`3` n>=12=`1` expanding=`False` samples=`[{'y': 59, 'n': 13}]`
- `OOEOEOE` follows=`3` n>=12=`3` expanding=`False` samples=`[{'y': 97, 'n': 17}, {'y': 137, 'n': 22}]`
- `OOEOOEOE` follows=`2` n>=12=`2` expanding=`False` samples=`[{'y': 89, 'n': 70}, {'y': 111, 'n': 86}]`

## Window split

- counts: `{'e4_oo': 176, 'e4_iso': 64, 'e5_oo': 1212, 'e5_iso': 96, 'e6_oo': 4662, 'e6_iso': 128}`

## Lean

- `CycleMin`: `True`
- `cycleMin_ge_twelve`: `True`
- `no_cycleMin_prefix_eee`: `True`
- `no_cycleMin_prefix_eoooee`: `True`
- `no_cycleMin_prefix_two_even_ee`: `True`
- `no_cycle_itinerary_even_count_le_three`: `True`

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

**BUNCHED_SHORT_PARK**

short leftovers return into [12, y]; the leftover-suffix path table is not a seal; isolated-odd e>=5 shapes exist; e=4 short-first-gap is already PARK; no new cell.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler.

