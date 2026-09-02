# Juggler top excursions

Status: **TOP_EXCURSION_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Maximum even-runs, not a census.

## Branch budget

```text
Mathematical target     max begins E^r onto odd p with a two-sided scale window
Novelty hypothesis      iterated isqrt cells plus PowerBound give a top normal form
Falsifier               a cycle max with no odd landing; or M outside [p^{2^r}, (p+1)^{2^r})
Existing machinery      CycleMax, square_scale_superquadratic, power_bound_word
Maximum Phase-0 scope   even-run bounds; top normal form; scale-superquadratic; transient tops
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **TOP_EXCURSION_GREEN**
- secondary: `['TOP_SCALE_WINDOW_GREEN', 'TOP_WINDOW_SURVIVES']`
- sorry-free: `True`

every cycle maximum has a finite even run onto an odd landing p with p^{2^r} ≤ M < (p+1)^{2^r}, and the ascent from p is scale-superquadratic. The integer window is nonempty; transients sit inside it without returning to p.

The integer window is nonempty. This does not force T(M)=m and
does not force r=1. Closed top excursions were not found among
the calibrated transients.

## Finite-orbit maxima

- odd starts: `38`
- window holds: `38`
- window fails: `0`
- r counts: `{1: 12, 2: 11, 3: 7, 4: 7, 5: 1}`
- start equals landing: `0`
- closed tops: `0`

### Hard probes and small examples

- start=`37` M=`24906114455136` r=`2` p=`2233` window=`True` lower_gap=`43036463615` upper_gap=`1530996399`
- start=`77` M=`2322378` r=`1` p=`1523` window=`True` lower_gap=`2849` upper_gap=`197`
- start=`3` M=`36` r=`3` p=`1` window=`True` lower_gap=`35` upper_gap=`219`
- start=`7` M=`18` r=`3` p=`1` window=`True` lower_gap=`17` upper_gap=`237`
- start=`9` M=`140` r=`1` p=`11` window=`True` lower_gap=`19` upper_gap=`3`
- start=`25` M=`52214` r=`2` p=`15` window=`True` lower_gap=`1589` upper_gap=`13321`

- n-search: `False`
- cycle-itinerary census: `False`

## Lean

- `even_iter_pow_le`: `True`
- `even_iter_lt_succ_pow`: `True`
- `power_scale_superquadratic`: `True`
- `cycleMax_top_even_run`: `True`
- `cycleMax_top_normal_form`: `True`
- `top_ascent_superquadratic`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- no ascent-contradiction theorem: `True`
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
- word_independent_obstruction: `False`
- top_ascent_impossible: `False`
- max_first_cell_impossible: `False`
- T_of_max_equals_min: `False`
- top_run_length_one: `False`
- useful_uniform_Q0: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`

## Decision

**TOP_EXCURSION_GREEN**

every cycle maximum has a finite even run onto an odd landing p with p^{2^r} ≤ M < (p+1)^{2^r}, and the ascent from p is scale-superquadratic. The integer window is nonempty; transients sit inside it without returning to p.

This is not a halt result. The top window is not empty.
Growth-versus-collapse coexistence is not refuted.

