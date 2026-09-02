# Juggler parity persistence

Status: **PARITY_PERSIST_PARK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Parity persistence on inherited
post-L landings. Not Z5, not a length-11 assembler, and not a
terminal-cluster reopen.

## Branch budget

```text
Mathematical target     finite odd-run budget on inherited L
Novelty hypothesis      history forces even within finite K
Existing machinery      L-image split; odd_landing_sets CLOSE
Maximum Phase-0 scope   named L-window; 33391 run 5; no Lean
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **PARITY_PERSIST_PARK**
- sorry-free: `True`
- summary: `{'n_l': 23, 'n_odd_t': 17, 'runs': {'1': 9, '2': 4, '3': 2, '4': 1, '5': 1}, 'stay1': 8, 'stay1_den': 17, 'max_run': 5, 'w5_hits': 0, 'mod8': {'stay_classes': 4, 'exit_classes': 4, 'both_classes': 4, 'only_stay': [], 'only_exit': []}}`

Inherited L-landings do not force an even output. 33391 has a length-5 odd run from 67709. Stay is 8/17. Every odd class mod 8 both continues and exits. W_5 is absent. No finite K. No 2-adic shrink.

## Attack 1 — inherited odd-run lengths

Among the 23 starts that follow `OOEOOOEOOEE` below 50000,
17 landings are odd. Immediate next-odd stay is `8/17`.
Runs are `1^9 2^4 3^2 4^1 5^1`. The maximum is 5 at
`33391 -> 67709` (`OOOOOE`). `501` has run 2 and never
follows `W_5`.

## Attack 2 — no 2-adic shrink

Restricted to those odd L-images, every odd class modulo 8
both continues odd and exits even. The diagnostic is the
same as the closed odd-landing-set census. No 2-adic
system is opened.

## Attack 3 — no finite K

The OOE-only residual is not a bound: `29371` has `OOOE`,
`28367` has `OOOOE`, and `33391` has `OOOOOE`. History
does not force `T(t)` even. Integer-cell continuation is
not resumed.

## Lean

- `CycleMin`: `True`
- `power_bound_word`: `True`
- `power_bound_contracts`: `True`
- `ooo_residual_ge_cube`: `True`
- `odd_preimage_unique`: `True`
- `no_cycleMin_ooeoooe`: `True`
- `floorPower_oooee_five_step_lt`: `True`

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
- finite_odd_run_k: `False`
- inherited_forces_even: `False`
- twadic_shrink: `False`
- w5_realized: `False`
- episode_automaton: `False`
- new_power_cell: `False`

## Decision

**PARITY_PERSIST_PARK**

Inherited L-landings do not force an even output. 33391 has a length-5 odd run from 67709. Stay is 8/17. Every odd class mod 8 both continues and exits. W_5 is absent. No finite K. No 2-adic shrink.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler. Terminal clusters stay frozen.

