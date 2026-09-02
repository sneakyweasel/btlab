# Juggler internal-E scale barriers

Status: **INTERNAL_E_BOOTSTRAP_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Internal-E transport, not a census.

## Branch budget

```text
Mathematical target     internal E plus cycle-min scale bootstraps a suffix threshold
Novelty hypothesis      even cycle states satisfy z ≥ n^2, so T(z) ≥ n feeds a known threshold
Falsifier               y < n still lands in the last-even cell; or z ≥ n^2 is false
Existing machinery      exists_cycle_min_odd, oo/ooo thresholds, last-even cell
Maximum Phase-0 scope   CycleMin barrier; generic bootstrap; OOEOOE; record OOOEOE
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **INTERNAL_E_BOOTSTRAP_GREEN**
- secondary: `['OOOEOE_EXCEPTION']`
- sorry-free: `True`

an internal even cycle state is at least n^2, so its image is at least n; a next-square suffix then overshoots the last-even cell. This excludes CycleMin OEOOOE and the full CycleItinerary OOEOOE. OOOEOE and OOOOEE remain.

The bootstrap uses `y ≥ n`, not `y > n`. If the internal even
state sits in the first square cell, `isqrt` may return `n`, and
that is already enough to fire a next-square suffix.

`OOOOEE` is not free from `OOOOE`: `T_OOOO ≥ (n+1)^2` does
not imply `T_OOOOE ≥ (n+1)^2`.

## Normalized expanding length-6 E-words

- `OOOOOE` α=`243/64` internal_E=`None` suffix=`None` th=`None` bootstrap=`False` Q0_exists=`True` cyclemin=`False` cycleword=`False`
- `OEOOOE` α=`81/64` internal_E=`1` suffix=`OOO` th=`ooo_suffix_threshold` bootstrap=`True` Q0_exists=`True` cyclemin=`True` cycleword=`False`
- `OOEOOE` α=`81/64` internal_E=`2` suffix=`OO` th=`oo_suffix_threshold` bootstrap=`True` Q0_exists=`True` cyclemin=`True` cycleword=`True`
- `OOOEOE` α=`81/64` internal_E=`3` suffix=`O` th=`None` bootstrap=`False` Q0_exists=`True` cyclemin=`False` cycleword=`False`
- `OOOOEE` α=`81/64` internal_E=`4` suffix=`` th=`None` bootstrap=`False` Q0_exists=`True` cyclemin=`False` cycleword=`False`

- bootstrap itineraries: `['OEOOOE', 'OOEOOE']`
- exceptions: `['OOOEOE', 'OOOOEE']`
- all-odd last-E: `['OOOOOE']`
- n-search: `False`

## Lean

- `CycleMin`: `True`
- `cycleMin_even_ge_sq`: `True`
- `cycleMin_not_odd_even`: `True`
- `no_cycleMin_internal_even_threshold`: `True`
- `no_cycleMin_oeoooe`: `True`
- `no_cycleMin_ooeooe`: `True`
- `no_cycle_itinerary_ooeooe`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- no length-6 theorem: `True`
- orbit-min hypothesis unused: `True`
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
- length_six_e_cycles_impossible: `False`
- useful_uniform_Q0: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`
- y_gt_n_required: `False`
- ooooee_free_via_ooooe: `False`
- all_odd_orbit: `False`
- finite_progress_for_all: `False`

## Decision

**INTERNAL_E_BOOTSTRAP_GREEN**

an internal even cycle state is at least n^2, so its image is at least n; a next-square suffix then overshoots the last-even cell. This excludes CycleMin OEOOOE and the full CycleItinerary OOEOOE. OOOEOE and OOOOEE remain.

This is not a halt result. Length-6 E-cycles are not all excluded.
Cycles ending in O are not treated. Q0 was not computed.

