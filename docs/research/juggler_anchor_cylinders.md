# Juggler nested anchor cylinders

Status: **ANCHOR_CYLINDER_CLOSED**

R_w versus A_w start-sets on hard AboveAnchor prefix chains.
Not a halt theorem. Absence is NOT_OBSERVED_WITHIN_BOUND.

## Branch budget

```text
Mathematical target     scale-stable nested A_w decay or N_min growth
Novelty hypothesis      finite histories occur; one anchor cannot
Maximum Phase-0 scope   two-scale counts; hard chains; no Lean
```

## Metadata

- classification: **ANCHOR_CYLINDER_CLOSED**
- k_max: `20` windows: `[100000, 1000000]`
- scanned: `{'100000': 49999, '1000000': 499999}`
- OE A empty / R positive: `True` / `True`
- extra AA not formal: `0`
- hard thinner than max |A_w|: `False`

nested |A_w| follows the generic ~X/2^k occupancy of a length-k word; short leftovers keep a scale-stable positive fraction; late O(1) support is the window scale, not a new law.

## Hard laboratories

- `37`: S=`14` |A|=`54` N_min=`37` frac=`0.000054` word=`OOOOEOOOEEOOEE` no bottleneck
- `69`: S=`6` |A|=`15768` N_min=`69` frac=`0.015768` word=`OOEOOE` no bottleneck
- `89`: S=`7` |A|=`7881` N_min=`89` frac=`0.007881` word=`OOEOOEO` no bottleneck
- `365`: S=`14` |A|=`53` N_min=`365` frac=`0.000053` word=`OOEOOEOOEOOEOE` no bottleneck
- `501`: S=`20` |A|=`1` N_min=`501` frac=`0.000001` word=`OOEOOOEOOEEOOEOOEOOE` bottleneck k=`18` C=`0.2222`
- `1517`: S=`15` |A|=`45` N_min=`1517` frac=`0.000045` word=`OOEOOEOOEOEOOOE` no bottleneck
- `6187`: S=`12` |A|=`211` N_min=`501` frac=`0.000211` word=`OOEOOOEOOEEO` no bottleneck
- `329`: S=`20` |A|=`4` N_min=`329` frac=`0.000004` word=`OOOOOOOOEOOEOOEEOEEO` no bottleneck
- `33391`: S=`20` |A|=`1` N_min=`33391` frac=`0.000001` word=`OOEOOOEOOEEOOOOOEEOO` no bottleneck

## M_k versus M_k^hard

- M_k: `[499999, 249926, 124972, 62541, 31416, 15779, 7937, 3985, 2038, 1031, 534, 284, 156, 84, 49, 29, 23, 12, 9, 7]`
- M_k^hard: `[499999, 249926, 124972, 62541, 31416, 15779, 7937, 3952, 1990, 978, 499, 261, 125, 64, 45, 21, 12, 7, 5, 4]`

## Isolation and N_min

- isolation: `[{'n': 37, 'k': 14, 'S': 54, 'N_min': 37, 'frac': 5.4e-05, 'isolated': False}, {'n': 69, 'k': 6, 'S': 15768, 'N_min': 69, 'frac': 0.015768, 'isolated': False}, {'n': 89, 'k': 7, 'S': 7881, 'N_min': 89, 'frac': 0.007881, 'isolated': False}, {'n': 365, 'k': 14, 'S': 53, 'N_min': 365, 'frac': 5.3e-05, 'isolated': False}, {'n': 501, 'k': 20, 'S': 1, 'N_min': 501, 'frac': 1e-06, 'isolated': True}, {'n': 1517, 'k': 15, 'S': 45, 'N_min': 1517, 'frac': 4.5e-05, 'isolated': False}, {'n': 6187, 'k': 12, 'S': 211, 'N_min': 501, 'frac': 0.000211, 'isolated': False}, {'n': 329, 'k': 20, 'S': 4, 'N_min': 329, 'frac': 4e-06, 'isolated': True}, {'n': 33391, 'k': 20, 'S': 1, 'N_min': 33391, 'frac': 1e-06, 'isolated': True}]`
- N_min growth: `[{'n': 37, 'first': 3, 'last': 37, 'grows': True, 'equals_lab': True}, {'n': 69, 'first': 3, 'last': 69, 'grows': True, 'equals_lab': True}, {'n': 89, 'first': 3, 'last': 89, 'grows': True, 'equals_lab': True}, {'n': 365, 'first': 3, 'last': 365, 'grows': True, 'equals_lab': True}, {'n': 501, 'first': 3, 'last': 501, 'grows': True, 'equals_lab': True}, {'n': 1517, 'first': 3, 'last': 1517, 'grows': True, 'equals_lab': True}, {'n': 6187, 'first': 3, 'last': 501, 'grows': True, 'equals_lab': False}, {'n': 329, 'first': 3, 'last': 329, 'grows': True, 'equals_lab': True}, {'n': 33391, 'first': 3, 'last': 33391, 'grows': True, 'equals_lab': True}]`

## R versus A on OE / OOE

- OE: A=`0` R=`250073`
- OOE: A=`124954` R=`124954` N_min_A=`5`

## Existing Lean (unchanged)

- `AboveAnchor`: `True`
- `aboveAnchor_of_prefix`: `True`
- `prefixNoncontracting`: `True`
- `aboveAnchor_not_envelope_drop`: `True`
- `follows`: `True`
- new Lean file: `False`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- global_non_realizability: `False`
- A_w_empty_from_window: `False`
- search_horizon_is_L: `False`
- density_theorem: `False`
- anchor_cylinder_lean: `False`
- itinerary_language_reopen: `False`

## Decision

**ANCHOR_CYLINDER_CLOSED**

nested |A_w| follows the generic ~X/2^k occupancy of a length-k word; short leftovers keep a scale-stable positive fraction; late O(1) support is the window scale, not a new law.

