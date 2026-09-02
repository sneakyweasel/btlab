# Juggler ResidualStep future-equivalence

Status: **RESIDUAL_MN_REPACK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. ResidualStep stays the successor.
The question is the growth of empirical trace classes `~_H`.

## Branch budget

```text
Mathematical target     does |Y / ~_H| saturate below |Y| or refine toward y?
Novelty hypothesis      a stable proper quotient of landings, not y
Falsifier               leftover fibers are the same complete word to HALT
Existing machinery      residual_excursion, intrinsic_V, residual_class
Maximum Phase-0 scope   n<=80 and n<=200; H=0..8; block/V/class; no Lean state
```

## Metadata

- algorithm: `residual-minimize-v1`
- engine control layer modified: `False`
- classification: **RESIDUAL_MN_REPACK**
- secondary: `['plateau']`
- sorry-free: `True`
- ResidualState.lean absent: `True`

Q_H plateaus below |Y| only because some landings share a complete block-word to HALT; the trace is a certificate of y, not a new state (Q_H=[1, 14, 22, 23, 23, 23, 23, 23, 23], |Y|=30, long_halt=4, short=2).

## Window n ≤ 80

- odd-odd starts: `18`
- landings: `43`
- distinct y: `30`
- distinct V: `19`
- H=1 V matches |{V(y)}|: `True`
- plateau from H: `3`
- capped traces: `0`

### block

| H | Q_H | max_fiber | n_multi | n_refine | n_live |
|---|-----|-----------|---------|----------|--------|
| 0 | 1 | 30 | 1 | 402 | 30 |
| 1 | 14 | 6 | 7 | 23 | 29 |
| 2 | 22 | 3 | 6 | 2 | 21 |
| 3 | 23 | 3 | 6 | 0 | 12 |
| 4 | 23 | 3 | 6 | 0 | 4 |
| 5 | 23 | 3 | 6 | 0 | 2 |
| 6 | 23 | 3 | 6 | 0 | 1 |
| 7 | 23 | 3 | 6 | 0 | 0 |
| 8 | 23 | 3 | 6 | — | 0 |

### V

| H | Q_H | max_fiber | n_multi | n_refine | n_live |
|---|-----|-----------|---------|----------|--------|
| 0 | 1 | 30 | 1 | 420 | 30 |
| 1 | 19 | 4 | 8 | 7 | 29 |
| 2 | 23 | 3 | 6 | 0 | 21 |
| 3 | 23 | 3 | 6 | 0 | 12 |
| 4 | 23 | 3 | 6 | 0 | 4 |
| 5 | 23 | 3 | 6 | 0 | 2 |
| 6 | 23 | 3 | 6 | 0 | 1 |
| 7 | 23 | 3 | 6 | 0 | 0 |
| 8 | 23 | 3 | 6 | — | 0 |

### class

| H | Q_H | max_fiber | n_multi | n_refine | n_live |
|---|-----|-----------|---------|----------|--------|
| 0 | 1 | 30 | 1 | 283 | 30 |
| 1 | 5 | 16 | 4 | 81 | 29 |
| 2 | 8 | 8 | 6 | 9 | 21 |
| 3 | 11 | 8 | 6 | 0 | 12 |
| 4 | 11 | 8 | 6 | 0 | 4 |
| 5 | 11 | 8 | 6 | 0 | 2 |
| 6 | 11 | 8 | 6 | 0 | 1 |
| 7 | 11 | 8 | 6 | 0 | 0 |
| 8 | 11 | 8 | 6 | — | 0 |

## Window n ≤ 200

- odd-odd starts: `56`
- landings: `162`
- distinct y: `111`
- distinct V: `38`
- H=1 V matches |{V(y)}|: `True`
- plateau from H: `5`
- capped traces: `13`

### block

| H | Q_H | max_fiber | n_multi | n_refine | n_live |
|---|-----|-----------|---------|----------|--------|
| 0 | 1 | 111 | 1 | 5615 | 111 |
| 1 | 26 | 18 | 16 | 399 | 110 |
| 2 | 64 | 7 | 23 | 31 | 88 |
| 3 | 74 | 5 | 21 | 2 | 61 |
| 4 | 75 | 5 | 21 | 1 | 38 |
| 5 | 76 | 5 | 20 | 0 | 27 |
| 6 | 76 | 5 | 20 | 0 | 22 |
| 7 | 76 | 5 | 20 | 0 | 20 |
| 8 | 76 | 5 | 20 | — | 17 |

## Multi-y fibers at H = 8 (block, n ≤ 80)

- size=`2` live=`3` long=`True` halted=`True` capped=`False` members=`[25, 59]` word=`[[3, 2], [1, 1], [1, 3], 'HALT']`
- size=`2` live=`3` long=`True` halted=`True` capped=`False` members=`[53, 55]` word=`[[2, 2], [2, 1], [1, 3], 'HALT']`
- size=`3` live=`2` long=`True` halted=`True` capped=`False` members=`[33, 35, 73]` word=`[[2, 2], [1, 3], 'HALT']`
- size=`2` live=`2` long=`True` halted=`True` capped=`False` members=`[15, 31]` word=`[[1, 1], [1, 3], 'HALT']`
- size=`2` live=`1` long=`False` halted=`True` capped=`False` members=`[7, 11]` word=`[[1, 3], 'HALT']`
- size=`2` live=`1` long=`False` halted=`True` capped=`False` members=`[43, 45]` word=`[[2, 4], 'HALT']`

## Hard traces

### n = 9

- terminal=`HALT` capped=`False` states=`[9, 11, 1]` blocks=`[(2, 1), (1, 3)]` classes=`['STAY_AUTO_FP', 'CAPTURE']`

### n = 37

- terminal=`HALT` capped=`False` states=`[37, 9317, 2233, 1]` blocks=`[(4, 1), (3, 2), (2, 5)]` classes=`['PERSISTENT_ODD_ODD', 'RETURN_BELOW', 'CAPTURE']`

### n = 49

- terminal=`HALT` capped=`False` states=`[49, 79, 5, 1]` blocks=`[(2, 1), (1, 2), (2, 3)]` classes=`['STAY_AUTO_FP', 'RETURN_BELOW', 'CAPTURE']`

### n = 69

- terminal=`HALT` capped=`False` states=`[69, 117, 3, 1]` blocks=`[(2, 1), (2, 3), (3, 3)]` classes=`['PERSISTENT_ODD_ODD', 'RETURN_BELOW', 'CAPTURE']`

### n = 77

- terminal=`HALT` capped=`False` states=`[77, 1523, 243, 21, 9, 11, 1]` blocks=`[(3, 1), (1, 1), (2, 2), (1, 1), (2, 1), (1, 3)]` classes=`['STAY_AUTO_FP', 'RETURN_BELOW', 'RETURN_BELOW', 'RETURN_BELOW', 'STAY_AUTO_FP', 'CAPTURE']`

### n = 11

- terminal=`HALT` capped=`False` states=`[11, 1]` blocks=`[(1, 3)]` classes=`['CAPTURE']`

## Lean

- `ResidualStep`: `True`
- `PersistentOddResidual`: `True`
- `ResidualChain`: `True`
- ResidualStep unchanged: `True`
- ResidualState.lean absent: `True`
- no ResidualState def: `True`
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
- history_is_new_state: `False`
- defect_financing_opened: `False`
- global_defect_growth_opened: `False`

## Decision

**RESIDUAL_MN_REPACK**

Q_H plateaus below |Y| only because some landings share a complete block-word to HALT; the trace is a certificate of y, not a new state (Q_H=[1, 14, 22, 23, 23, 23, 23, 23, 23], |Y|=30, long_halt=4, short=2).

This is not a halt result. ResidualStep is not a state object.
Object C was not opened. Word-language MN was not reopened.

