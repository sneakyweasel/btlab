# Juggler cycle extrema

Status: **CYCLE_EXTREMES_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Word-independent extrema, not a census.

## Branch budget

```text
Mathematical target     extrema force M >= (m+1)^2 and a superquadratic min-to-even path
Novelty hypothesis      first-even overshoot excludes first-cell maxima
Falsifier               a CycleMin whose max sits below (m+1)^2
Existing machinery      CycleMin, cycleMin_first_even_overshoots, cycleMin_max_gt_sq
Maximum Phase-0 scope   CycleMax; M >= (m+1)^2; square-scale superquadratic
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **CYCLE_EXTREMES_GREEN**
- secondary: `['ASCENDING_SUPERQUADRATIC_GREEN']`
- sorry-free: `True`

every nontrivial cycle has odd min, even max, and M >= (m+1)^2; any realized path from m to an even cycle state is superquadratic. First-cell maxima are impossible. Ordinary stay-above-min transients often drop before m^2, so the cycle constraint is not vacuous.

A cycle cannot drop below `m` and therefore cannot use the
common transient `OE` collapse before square scale.

## Stay-above-min calibration

- odd starts `3..61`: `30`
- hit `m^2` while staying `≥ m`: `14`
- drop below `m` before `m^2`: `16`
- step cap `40` leftovers: `0`
- all hits superquadratic: `True`
- first-hit words: `['OO']`
- exact-square hits: `0`
- drop examples: `[7, 11, 13, 15, 17, 19, 21, 23]`

### First square-scale hits

- m=`3` word=`OO` cell=`first_cell` superquadratic=`True`
- m=`5` word=`OO` cell=`above_next_sq` superquadratic=`True`
- m=`9` word=`OO` cell=`above_next_sq` superquadratic=`True`
- m=`25` word=`OO` cell=`above_next_sq` superquadratic=`True`
- m=`33` word=`OO` cell=`above_next_sq` superquadratic=`True`
- m=`35` word=`OO` cell=`above_next_sq` superquadratic=`True`

- n-search: `False`
- cycle-itinerary census: `False`

## Lean

- `CycleMax`: `True`
- `exists_cycle_max_even`: `True`
- `cycleMax_start_even`: `True`
- `cycleMin_max_gt_sq`: `True`
- `cycleMax_return_cell`: `True`
- `square_scale_superquadratic`: `True`
- `cycleMin_to_even_superquadratic`: `True`
- `cycleMin_to_max_superquadratic`: `True`
- `cycleMin_max_ge_succ_sq`: `True`
- `cycleMin_max_not_first_cell`: `True`
- `cycleMax_min_succ_sq_le`: `True`
- `cycleMax_landing_gt_min`: `True`
- `cycleMax_exists_min_succ_sq`: `True`
- `cycle_distinguished_order_succ_sq`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- no length-6 theorem: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
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
- word_independent_obstruction: `False`
- max_first_cell_impossible: `True`
- all_odd_orbit: `False`
- finite_progress_for_all: `False`

## Decision

**CYCLE_EXTREMES_GREEN**

every nontrivial cycle has odd min, even max, and M >= (m+1)^2; any realized path from m to an even cycle state is superquadratic. First-cell maxima are impossible. Ordinary stay-above-min transients often drop before m^2, so the cycle constraint is not vacuous.

This is not a halt result. Growth-versus-collapse coexistence
is not refuted. The first-cell family M in [m^2, (m+1)^2) is
excluded by first-even overshoot: M >= (m+1)^2 and T(M) > m.

