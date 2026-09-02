# Juggler hidden state of the coarse scale loop

Status: **SCALE_LOOP_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The C2-C4-C2-C1 return after
the second OO. Not Z5, not a length-11 assembler, and not a
terminal-cluster reopen.

## Branch budget

```text
Mathematical target     refine C2-C4-C2-C1 so it cannot recur
Novelty hypothesis      a hidden carry/defect/pre-post state drifts
Existing machinery      second-OO envelopes; 501 -> 763
Maximum Phase-0 scope   two inherited even-even loops;
                        C1 collision; p-adic control; no Lean
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **SCALE_LOOP_GREEN**
- sorry-free: `True`
- t may exceed n: `True`
- 501 hits / drop: `1` / `34`
- 6187 hits / drop: `1` / `1087`
- C1 collision split: `True`
- 2-adic special: `False`

C2->C4->C2->C1 is the one-shot word OOEOOOEOOEE; the return is C1-post, not C1-pre. 501 vs 763 is the same scale+parity with different futures. 6187 drops by OE. The exact signature does not repeat.

## Attack 1 — the loop is an word

Even-even `C2 -> C4 -> C2 -> C1` from inherited odd `q` is
`OEE` on `q`, equivalently `OOEOOOEOOEE` on `n`. The return
satisfies `t^{2048} <= n^{2187}`. Equality `t = n` would be
numerical closure. Both named images have `t > n`.

## Attack 2 — pre versus post

`C1` at the CycleMin start is pre-first-`OOO`. `C1` at the
return is post-`OOEOOOEOOEE`. Scale+parity identifies them;
the word-progress bit does not. 501 starts `OOE+OOO`; 763
starts `(OOE)^3 OE E` and never pays a second first-`OOO`.

## Attack 3 — one-shot orbits

Each inherited even-even orbit has exactly one coarse hit.
501 later drops to 34. 6187 returns to 11189 and drops by
`OE` to 1087. Outcome A (exact signature repeat) fails.

## Lean

- `CycleMin`: `True`
- `power_bound_word`: `True`
- `power_bound_contracts`: `True`
- `ooo_residual_ge_cube`: `True`
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
- signature_repeats: `False`
- scale_parity_determines_future: `False`
- two_adic_hidden_state: `False`
- defect_phi_monotone: `False`

## Decision

**SCALE_LOOP_GREEN**

C2->C4->C2->C1 is the one-shot word OOEOOOEOOEE; the return is C1-post, not C1-pre. 501 vs 763 is the same scale+parity with different futures. 6187 drops by OE. The exact signature does not repeat.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler. Terminal clusters stay frozen.

