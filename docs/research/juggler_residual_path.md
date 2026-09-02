# Juggler residual-path regimes

Status: **BOUNDED_RESIDUAL_CYCLE_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. A bounded residual prefix with a
repeat is a Juggler cycle. Every nonempty cycle itinerary satisfies
`2^r < 3^o`. Residual returns need `a ≥ 2`.

## Branch budget

```text
Mathematical target     bounded residual prefix ⇒ cycle; cycle envelope 2^r < 3^o
Novelty hypothesis      residual return needs a ≥ 2; equality 2^r = 3^o is impossible
Falsifier               a residual return with a ≤ 1; or a contracting cycle itinerary
Existing machinery      ResidualStep, power_bound_word, power_bound_contracts
Maximum Phase-0 scope   orbit repeat; cycle envelope; residual-return a≥2; small cycle scan
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **BOUNDED_RESIDUAL_CYCLE_GREEN**
- secondary: `['CYCLE_OBSTRUCTION_GREEN']`
- sorry-free: `True`

a repeated orbit state is a finite cycle; every nonempty cycle itinerary has 2^r < 3^o; residual returns need a ≥ 2; contracting and a = 1 residual returns are excluded; no cycle found in the scan n ≤ 400.

## Cycle scan

- n_max: `400`
- fixed points: `[1]`
- returns to self before 1: `[]`
- residual period-1: `[]`
- a=1 residual return forbidden: `True`

## Hard residual paths

### n = 9

- x=`9` O^2E^1 z=`140` y=`11` edge=`OVERSHOOT` kind=`STAY_AUTO_FP` y<n=`False`
- x=`11` O^1E^3 z=`36` y=`1` edge=`DESCENT` kind=`CAPTURE` y<n=`True`

### n = 37

- x=`37` O^4E^1 z=`86818724` y=`9317` edge=`OVERSHOOT` kind=`PERSISTENT_ODD_ODD` y<n=`False`
- x=`9317` O^3E^2 z=`24906114455136` y=`2233` edge=`DESCENT` kind=`PERSISTENT_ODD_ODD` y<n=`False`
- x=`2233` O^2E^5 z=`34276462` y=`1` edge=`DESCENT` kind=`CAPTURE` y<n=`True`

### n = 49

- x=`49` O^2E^1 z=`6352` y=`79` edge=`OVERSHOOT` kind=`STAY_AUTO_FP` y<n=`False`
- x=`79` O^1E^2 z=`702` y=`5` edge=`DESCENT` kind=`RETURN_BELOW` y<n=`True`

### n = 69

- x=`69` O^2E^1 z=`13716` y=`117` edge=`OVERSHOOT` kind=`PERSISTENT_ODD_ODD` y<n=`False`
- x=`117` O^2E^3 z=`44992` y=`3` edge=`DESCENT` kind=`RETURN_BELOW` y<n=`True`

### n = 77

- x=`77` O^3E^1 z=`2322378` y=`1523` edge=`OVERSHOOT` kind=`STAY_AUTO_FP` y<n=`False`
- x=`1523` O^1E^1 z=`59436` y=`243` edge=`DESCENT` kind=`PERSISTENT_ODD_ODD` y<n=`False`
- x=`243` O^2E^2 z=`233046` y=`21` edge=`DESCENT` kind=`RETURN_BELOW` y<n=`True`

## Lean

- `ResidualDescent`: `True`
- `ResidualReturn`: `True`
- `ResidualOvershoot`: `True`
- `two_pow_ne_three_pow`: `True`
- `cycle_envelope`: `True`
- `cycle_strict_envelope`: `True`
- `cycle_not_contracting`: `True`
- `orbit_repeat_cycle`: `True`
- `residual_return_cycle`: `True`
- `residual_return_envelope`: `True`
- `residual_return_a_ge_two`: `True`
- `minimal_residual_chain_ge`: `True`
- `bounded_prefix_not_nodup`: `True`
- certificate unchanged: `False`
- `PowerHeight` absent: `True`
- FloorPower not rewritten: `True`
- no cycle-impossibility theorem: `True`
- no cycle engine: `True`
- no infinite-path type: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- all_odd_orbit: `False`
- finite_progress_for_all: `False`
- cycles_impossible: `False`
- unbounded_branch_impossible: `False`
- overshoot_is_progress: `False`
- uniform_residual_horizon: `False`

## Decision

**BOUNDED_RESIDUAL_CYCLE_GREEN**

a repeated orbit state is a finite cycle; every nonempty cycle itinerary has 2^r < 3^o; residual returns need a ≥ 2; contracting and a = 1 residual returns are excluded; no cycle found in the scan n ≤ 400.

This is not a halt result. Cycles are not proved impossible.
The unbounded residual branch is not closed.

