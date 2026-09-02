# Juggler L-odd-run cap

Status: **L_ODD_RUN_CAP_PARK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Whether the L-envelope caps
odd runs from t = T_L(n). Not Z5, not a length-11 assembler,
and not a terminal-cluster reopen.

## Branch budget

```text
Mathematical target     L-envelope vs long odd runs from t
Novelty hypothesis      2187/2048 supplies a finite K
Existing machinery      compose_below_anchor; 33391 run 5
Maximum Phase-0 scope   compose test; 33391; no word census
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **L_ODD_RUN_CAP_PARK**
- sorry-free: `True`
- gaps: `{'l_num': 2187, 'l_den': 2048, 'never_drops': True, 'drop0': False, 'drop1': False, 'drop5': False, 'drop16': False, 'slack0': 139, 'slack5': 465905}`

The L-envelope never compose-drops O^k from t (2187 * 3^k > 2048 * 2^k for every k). A finite K cannot come from power_bound_contracts. 33391 realizes k=5. Boundedness of realization of L+O^k remains open.

## Attack 1 — the envelope never drops

`2187 > 2048` and `3^k >= 2^k`, so
`2187 * 3^k > 2048 * 2^k` for every `k >= 0`. If
`t^{2048} <= n^{2187}` and `t` follows `O^k`, the compose
test does not force `T_{O^k}(t) < n`. Slack at `k=0` is
`139` and increases.

## Attack 2 — cycle suffix is not a path cap

`odd_run_suffix_threshold` and `no_cycle_odd_run_append_even`
forbid `CycleItinerary` of the form `O^a E` for `a >= 3`. They do
not forbid a path `L+O^k` that does not return. `33391`
realizes `k=5` and does not follow `W_5`.

## Attack 3 — realization remains

Any finite `K` must come from non-existence of `n` following
`L+O^k`, not from `power_bound_contracts`. That realization
question is not an word census in this phase.

## Lean

- `CycleMin`: `True`
- `power_bound_word`: `True`
- `power_bound_contracts`: `True`
- `odd_run_suffix_threshold`: `True`
- `no_cycle_odd_run_append_even`: `True`
- `odd_preimage_unique`: `True`
- `no_cycleMin_ooeoooe`: `True`

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
- envelope_caps_k: `False`
- k_unbounded: `False`
- word_census: `False`
- new_power_cell: `False`

## Decision

**L_ODD_RUN_CAP_PARK**

The L-envelope never compose-drops O^k from t (2187 * 3^k > 2048 * 2^k for every k). A finite K cannot come from power_bound_contracts. 33391 realizes k=5. Boundedness of realization of L+O^k remains open.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler. Terminal clusters stay frozen.

