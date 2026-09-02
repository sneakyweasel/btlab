# Juggler prefix-OOO extra scale

Status: **OOO_SCALE_THRESHOLD_ONLY**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Two leftover itineraries, not a census.

## Branch budget

```text
Mathematical target     prefix-OOO extra scale or OOOOEE rotation
                        excludes CycleItinerary on OOOEOE and OOOOEE
Novelty hypothesis      T^3 >= (n+1)^2 plus the even cell of y
                        forces T(y) >= (n+1)^2; OOOOEE dies by rotation
Falsifier               y=n is the OOO threshold; extra scale is
                        envelope slack or only eventual
Existing machinery      CycleMin, ooo_suffix_threshold, last-even/odd
                        cells, LowerPowerBound, succ_sq_le_cube
Maximum Phase-0 scope   two words; exact identities; Lean iff reusable
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **OOO_SCALE_THRESHOLD_ONLY**
- secondary: `['CYCLEMIN_NOT_END_ODD']`
- sorry-free: `True`

y=n is the OOO threshold plus the even cell; CycleMin cannot end in O by the last-odd cell plus succ_sq_le_cube; LowerPowerBound extra scale is not uniform from n=3; OOOOEE reduces to CycleMin OOOOEE and is not excluded.

The `y = n` landing after prefix `OOO` and an internal `E` is
exactly `ooo_suffix_threshold` against the even cell of `n`.
A cycle minimum cannot end in `O` because `x >= n` and
`x^3 < (n+1)^2` contradict `succ_sq_le_cube`.

## Identities

- leftover itineraries: `['OOOEOE', 'OOOOEE']`
- y=n incompatible: `True`
- y=n is the OOO threshold: `True`
- succ_sq_le_cube on 3,5,7,9: `True`
- lowerDenom(OOO) = 2^38: `True`
- lowerDenom(OOOO) = 2^130: `True`
- first OOO LowerPowerBound overshoot n: `109`
- extra scale uniform from n=3: `False`
- n=3 forced: `False`
- n=5 forced: `False`

## OOOOEE CycleMin orientations

- `OOOOEE` startE=`False` startOE=`False` endO=`False` legal=`True` blocked=`None`
- `OOOEEO` startE=`False` startOE=`False` endO=`True` legal=`False` blocked=`cycleMin_not_end_odd`
- `OOEEOO` startE=`False` startOE=`False` endO=`True` legal=`False` blocked=`cycleMin_not_end_odd`
- `OEEOOO` startE=`False` startOE=`True` endO=`True` legal=`False` blocked=`cycleMin_not_odd_even`
- `EEOOOO` startE=`True` startOE=`False` endO=`True` legal=`False` blocked=`cycleMin_not_start_even`
- `EOOOOE` startE=`True` startOE=`False` endO=`False` legal=`False` blocked=`cycleMin_not_start_even`

- legal CycleMin words: `['OOOOEE']`
- reduces to self: `True`
- n-search: `False`

## Lean

- `cycleMin_not_end_odd`: `True`
- `cycleMin_prefix_ooo_even_sqrt_ne`: `True`
- `no_cycleMin_ooooeoe_of_sqrt_eq`: `True`
- `ooo_suffix_threshold`: `True`
- `odd_run_suffix_threshold`: `True`
- `cycle_last_odd_interval`: `True`
- `succ_sq_le_cube`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- no length-6 theorem: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- O-terminating not claimed: `True`
- no OOOEOE CycleItinerary theorem: `True`
- no OOOOEE CycleItinerary theorem: `True`
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
- length_six_e_cycles_impossible: `False`
- oooEOE_excluded: `False`
- ooooEE_excluded: `False`
- useful_uniform_Q0: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`
- extra_scale_uniform: `False`
- all_odd_orbit: `False`
- finite_progress_for_all: `False`

## Decision

**OOO_SCALE_THRESHOLD_ONLY**

y=n is the OOO threshold plus the even cell; CycleMin cannot end in O by the last-odd cell plus succ_sq_le_cube; LowerPowerBound extra scale is not uniform from n=3; OOOOEE reduces to CycleMin OOOOEE and is not excluded.

This is not a halt result. Neither leftover CycleItinerary is excluded.
Cycles ending in O as CycleItinerary are not treated. Length 7 was not opened.

