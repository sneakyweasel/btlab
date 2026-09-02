# Juggler residual future-quotient

Status: **FUTURE_QUOTIENT_REPACK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. ResidualStep stays the successor.
The object is bounded future equivalence at horizon H, not
Myhill–Nerode equivalence.

## Branch budget

```text
Mathematical target     which listed projections determine Future_H, and does k*(H) grow?
Novelty hypothesis      a compact S, not exact y, or a genuine precision hierarchy
Falsifier               H=1 separators for every no-y projection; leftover fibers are HALT words
Existing machinery      residual_excursion, classify_step, residual_class, intrinsic_V, v2
Maximum Phase-0 scope   H<=6; n<=80 and n<=4000; optional atlas PE starts; no GPU/Lean/automaton
```

## Metadata

- algorithm: `future-quotient-v1`
- engine control layer modified: `False`
- classification: **FUTURE_QUOTIENT_REPACK**
- secondary: `['STATE_QUOTIENT_COUNTEREXAMPLE', 'STATE_COMPLEXITY_PARK']`
- sorry-free: `True`
- ResidualState.lean absent: `True`

every listed arithmetic projection of y is separated at H=1 (pairs {'y_mod_8': [1, 9], 'v2_3y1': [1, 9], 'y_mod_2_16': [33, 573141612728625270488952931933108109345]}); residual_V predicts Future_1 only as a rewrite of the next ResidualStep and splits by H=6 (pair [9, 49]); n<=80 label Q_H=[1, 6, 11, 12, 12, 12, 12] plateaus on HALT fibers; atlas-enriched Q_H=[1, 6, 18, 54, 158, 393, 769] on |Y|=6004, live_multi=312; k*(H) exceeds 16 on the atlas-enriched sample.

Closed branches were not reopened: `RESIDUAL_STATE_NEEDS_X`,
`RESIDUAL_MN_REPACK`, `LANDING_VALUATION_IS_Y_MOD_8`,
`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`.

## Window n ≤ 80

- distinct y: `30`
- most promising at H=1: `{'name': None, 'reason': 'no_arithmetic_quotient; residual_V is a Future_1 rewrite'}`

### Future_H labels

| H | Q_H | max_fiber | n_multi | halt_multi | live_multi |
|---|-----|-----------|---------|------------|------------|
| 0 | 1 | 30 | 1 | 1 | 0 |
| 1 | 6 | 9 | 5 | 5 | 0 |
| 2 | 11 | 8 | 8 | 8 | 0 |
| 3 | 12 | 8 | 7 | 7 | 0 |
| 4 | 12 | 8 | 7 | 7 | 0 |
| 5 | 12 | 8 | 7 | 7 | 0 |
| 6 | 12 | 8 | 7 | 7 | 0 |

### k*(H)

- H=1: k*=`9` exceeds_k_max=`False` separator=`[243, 1523]`
- H=2: k*=`9` exceeds_k_max=`False` separator=`[243, 1523]`
- H=3: k*=`9` exceeds_k_max=`False` separator=`[243, 1523]`
- H=4: k*=`9` exceeds_k_max=`False` separator=`[243, 1523]`
- H=5: k*=`9` exceeds_k_max=`False` separator=`[243, 1523]`
- H=6: k*=`9` exceeds_k_max=`False` separator=`[243, 1523]`

### Projections at H = 1

| S | |proj| | |Future| | compression | separators | first pair | sufficient |
|---|------|----------|-------------|------------|------------|------------|
| `exact_y` | 30 | 6 | 1.000 | 0 | — | `True` |
| `parity` | 1 | 6 | 0.033 | 1 | `1,3` | `False` |
| `y_mod_8` | 4 | 6 | 0.133 | 4 | `1,9` | `False` |
| `v2_3y1` | 6 | 6 | 0.200 | 4 | `1,9` | `False` |
| `residual_V` | 19 | 6 | 0.633 | 0 | — | `True` |
| `pe_flags` | 3 | 6 | 0.100 | 1 | `1,3` | `False` |
| `y_mod_2_1` | 1 | 6 | 0.033 | 1 | `1,3` | `False` |
| `mod2_1_v2` | 6 | 6 | 0.200 | 4 | `1,9` | `False` |
| `y_mod_2_2` | 2 | 6 | 0.067 | 2 | `1,5` | `False` |
| `mod2_2_v2` | 6 | 6 | 0.200 | 4 | `1,9` | `False` |
| `y_mod_2_3` | 4 | 6 | 0.133 | 4 | `1,9` | `False` |
| `mod2_3_v2` | 7 | 6 | 0.233 | 5 | `1,9` | `False` |
| `y_mod_2_4` | 8 | 6 | 0.267 | 8 | `1,33` | `False` |
| `mod2_4_v2` | 10 | 6 | 0.333 | 8 | `1,33` | `False` |
| `y_mod_2_8` | 29 | 6 | 0.967 | 1 | `243,1523` | `False` |
| `mod2_8_v2` | 29 | 6 | 0.967 | 1 | `243,1523` | `False` |
| `y_mod_2_16` | 30 | 6 | 1.000 | 0 | — | `True` |
| `mod2_16_v2` | 30 | 6 | 1.000 | 0 | — | `True` |

## Window n ≤ 4000 plus atlas PE starts

- distinct y: `6004`
- chain landings: `3386`
- atlas PE starts used: `4000`
- most promising at H=1: `{'name': None, 'reason': 'no_arithmetic_quotient; residual_V is a Future_1 rewrite'}`

### Future_H labels (all sampled)

| H | Q_H | max_fiber | n_multi | halt_multi | live_multi |
|---|-----|-----------|---------|------------|------------|
| 0 | 1 | 6004 | 1 | 0 | 1 |
| 1 | 6 | 4109 | 5 | 1 | 4 |
| 2 | 18 | 1197 | 17 | 5 | 12 |
| 3 | 54 | 587 | 53 | 18 | 35 |
| 4 | 158 | 265 | 150 | 51 | 99 |
| 5 | 393 | 223 | 326 | 122 | 204 |
| 6 | 769 | 223 | 520 | 208 | 312 |

### Persistent-odd slice

| H | Q_H | max_fiber | n_multi | halt_multi | live_multi |
|---|-----|-----------|---------|------------|------------|
| 0 | 1 | 4109 | 1 | 0 | 1 |
| 1 | 1 | 4109 | 1 | 0 | 1 |
| 2 | 5 | 1197 | 5 | 1 | 4 |
| 3 | 17 | 587 | 17 | 5 | 12 |
| 4 | 53 | 265 | 53 | 17 | 36 |
| 5 | 159 | 223 | 153 | 49 | 104 |
| 6 | 416 | 223 | 360 | 117 | 243 |

### PE slice

| H | Q_H | max_fiber | n_multi | halt_multi | live_multi |
|---|-----|-----------|---------|------------|------------|
| 0 | 1 | 4109 | 1 | 0 | 1 |
| 1 | 1 | 4109 | 1 | 0 | 1 |
| 2 | 5 | 1197 | 5 | 1 | 4 |
| 3 | 17 | 587 | 17 | 5 | 12 |
| 4 | 53 | 265 | 53 | 17 | 36 |
| 5 | 159 | 223 | 153 | 49 | 104 |
| 6 | 416 | 223 | 360 | 117 | 243 |

### k*(H) on all sampled

- H=1: k*=`None` exceeds_k_max=`True` separator=`[33, 573141612728625270488952931933108109345]` v2_diff=`16`
- H=2: k*=`None` exceeds_k_max=`True` separator=`[33, 573141612728625270488952931933108109345]` v2_diff=`16`
- H=3: k*=`None` exceeds_k_max=`True` separator=`[33, 573141612728625270488952931933108109345]` v2_diff=`16`
- H=4: k*=`None` exceeds_k_max=`True` separator=`[33, 573141612728625270488952931933108109345]` v2_diff=`16`
- H=5: k*=`None` exceeds_k_max=`True` separator=`[33, 573141612728625270488952931933108109345]` v2_diff=`16`
- H=6: k*=`None` exceeds_k_max=`True` separator=`[33, 573141612728625270488952931933108109345]` v2_diff=`16`

### Projections at H = 1

| S | |proj| | |Future| | compression | separators | first pair | sufficient |
|---|------|----------|-------------|------------|------------|------------|
| `exact_y` | 6004 | 6 | 1.000 | 0 | — | `True` |
| `parity` | 1 | 6 | 0.000 | 1 | `1,3` | `False` |
| `y_mod_8` | 4 | 6 | 0.001 | 4 | `1,9` | `False` |
| `v2_3y1` | 15 | 6 | 0.002 | 11 | `1,9` | `False` |
| `residual_V` | 121 | 6 | 0.020 | 0 | — | `True` |
| `pe_flags` | 3 | 6 | 0.000 | 1 | `1,3` | `False` |
| `y_mod_2_1` | 1 | 6 | 0.000 | 1 | `1,3` | `False` |
| `mod2_1_v2` | 15 | 6 | 0.002 | 11 | `1,9` | `False` |
| `y_mod_2_2` | 2 | 6 | 0.000 | 2 | `1,5` | `False` |
| `mod2_2_v2` | 15 | 6 | 0.002 | 11 | `1,9` | `False` |
| `y_mod_2_3` | 4 | 6 | 0.001 | 4 | `1,9` | `False` |
| `mod2_3_v2` | 16 | 6 | 0.003 | 12 | `1,9` | `False` |
| `y_mod_2_4` | 8 | 6 | 0.001 | 8 | `1,17` | `False` |
| `mod2_4_v2` | 19 | 6 | 0.003 | 15 | `1,17` | `False` |
| `y_mod_2_8` | 128 | 6 | 0.021 | 128 | `1,257` | `False` |
| `mod2_8_v2` | 135 | 6 | 0.022 | 131 | `1,257` | `False` |
| `y_mod_2_16` | 5880 | 6 | 0.979 | 108 | `33,573141612728625270488952931933108109345` | `False` |
| `mod2_16_v2` | 5880 | 6 | 0.979 | 108 | `33,573141612728625270488952931933108109345` | `False` |

### Multi-y fibers at H = 6

- size=`223` halted=`True` capped=`False` members=`[37, 69, 225, 269, 673, 739, 1141, 1253]`
- size=`166` halted=`True` capped=`False` members=`[3, 5, 7, 11, 13, 17, 41, 43]`
- size=`165` halted=`True` capped=`False` members=`[23, 29, 79, 85, 117, 121, 129, 153]`
- size=`165` halted=`True` capped=`False` members=`[247, 1125, 1135, 1245, 1399, 1993, 2375, 2467]`
- size=`156` halted=`True` capped=`False` members=`[15, 27, 31, 33, 35, 47, 73, 143]`
- size=`149` halted=`True` capped=`False` members=`[1081, 2345, 2349, 2947, 3373, 5489, 5561, 5625]`
- size=`131` halted=`True` capped=`False` members=`[99, 113, 183, 431, 951, 985, 1201, 1911]`
- size=`97` halted=`True` capped=`False` members=`[841, 1003, 2061, 3079, 4721, 5961, 6713, 7071]`

## Hard traces

- n=`9` terminal=`HALT` capped=`False` labels=`[[True, 'STAY_AUTO_FP', False, False, True], [True, 'CAPTURE', False, False, False], ['HALT']]`
- n=`11` terminal=`HALT` capped=`False` labels=`[[True, 'CAPTURE', False, False, False], ['HALT']]`
- n=`37` terminal=`HALT` capped=`False` labels=`[[True, 'PERSISTENT_ODD_ODD', True, True, True], [True, 'RETURN_BELOW', True, False, False], [True, 'CAPTURE', False, False, False], ['HALT']]`
- n=`49` terminal=`HALT` capped=`False` labels=`[[True, 'STAY_AUTO_FP', False, False, True], [True, 'RETURN_BELOW', True, False, False], [True, 'CAPTURE', False, False, False], ['HALT']]`
- n=`69` terminal=`HALT` capped=`False` labels=`[[True, 'PERSISTENT_ODD_ODD', True, True, True], [True, 'RETURN_BELOW', True, False, False], [True, 'CAPTURE', False, False, False], ['HALT']]`
- n=`77` terminal=`HALT` capped=`False` labels=`[[True, 'STAY_AUTO_FP', False, False, True], [True, 'RETURN_BELOW', True, False, False], [True, 'RETURN_BELOW', False, False, False], [True, 'RETURN_BELOW', True, False, False], [True, 'STAY_AUTO_FP', False, False, True], [True, 'CAPTURE', False, False, False]]`
- n=`365` terminal=`HALT` capped=`False` labels=`[[True, 'PERSISTENT_ODD_ODD', True, True, True], [True, 'PERSISTENT_ODD_ODD', True, True, True], [True, 'PERSISTENT_ODD_ODD', True, True, True], [True, 'STAY_AUTO_FP', False, False, True], [True, 'RETURN_BELOW', True, False, False], [True, 'CAPTURE', False, False, False]]`

## Lean

- `ResidualStep`: `True`
- `PersistentOddResidual`: `True`
- `PersistentExpandingResidual`: `True`
- `ResidualChain`: `True`
- ResidualStep unchanged: `True`
- ResidualState.lean absent: `True`
- no forbidden engines: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- residual_state_object: `False`
- residual_step_extended: `False`
- finite_residual_automaton: `False`
- itinerary_language_reopened: `False`
- pe_factor_reopened: `False`
- history_is_new_state: `False`
- new_scalar_energy: `False`

## Decision

**FUTURE_QUOTIENT_REPACK**

every listed arithmetic projection of y is separated at H=1 (pairs {'y_mod_8': [1, 9], 'v2_3y1': [1, 9], 'y_mod_2_16': [33, 573141612728625270488952931933108109345]}); residual_V predicts Future_1 only as a rewrite of the next ResidualStep and splits by H=6 (pair [9, 49]); n<=80 label Q_H=[1, 6, 11, 12, 12, 12, 12] plateaus on HALT fibers; atlas-enriched Q_H=[1, 6, 18, 54, 158, 393, 769] on |Y|=6004, live_multi=312; k*(H) exceeds 16 on the atlas-enriched sample.

This is not a halt result. ResidualStep is not a state object.
The PE-factor branch was not reopened. No automaton was built.

