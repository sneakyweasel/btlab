# Juggler formal vs realized AboveAnchor language

Status: **FORMAL_REALIZED_GAP_CLOSED**

Shared prefix-noncontracting language versus integer AboveAnchor prefixes.
Not a halt theorem. Absence is NOT_OBSERVED_WITHIN_BOUND.

## Branch budget

```text
Mathematical target     simple exact P for D_N, or equally rich
Novelty hypothesis      Lean forgets one AA-realizability feature
Maximum Phase-0 scope   enumerate L_formal; AA scan; F_j; hold-out
```

## Metadata

- classification: **FORMAL_REALIZED_GAP_CLOSED**
- k_max: `20` n_max: `1000000` hold_split: `500000`
- scanned starts: `499999`
- last N formal/AA/dead: `27328` / `16822` / `10506`
- R_N: `0.6155591334894613`
- |F_j|: `8498`
- property: `None` found=`False`
- hold-out later fraction: `0.5042680711950599`
- leftover AA prefixes formal: `True`
- extra AA not formal: `0`

F_j from the low-n half realizes later; remaining unobserved prefixes are window or scale artefacts, not a new exact P.

## Counts by length

- N=`1` formal=`1` AA=`1` dead=`0` R_N=`1.000000`
- N=`2` formal=`1` AA=`1` dead=`0` R_N=`1.000000`
- N=`3` formal=`2` AA=`2` dead=`0` R_N=`1.000000`
- N=`4` formal=`3` AA=`3` dead=`0` R_N=`1.000000`
- N=`5` formal=`4` AA=`4` dead=`0` R_N=`1.000000`
- N=`6` formal=`8` AA=`8` dead=`0` R_N=`1.000000`
- N=`7` formal=`13` AA=`13` dead=`0` R_N=`1.000000`
- N=`8` formal=`19` AA=`19` dead=`0` R_N=`1.000000`
- N=`9` formal=`38` AA=`38` dead=`0` R_N=`1.000000`
- N=`10` formal=`64` AA=`64` dead=`0` R_N=`1.000000`
- N=`11` formal=`128` AA=`128` dead=`0` R_N=`1.000000`
- N=`12` formal=`226` AA=`226` dead=`0` R_N=`1.000000`
- N=`13` formal=`367` AA=`367` dead=`0` R_N=`1.000000`
- N=`14` formal=`734` AA=`734` dead=`0` R_N=`1.000000`
- N=`15` formal=`1295` AA=`1295` dead=`0` R_N=`1.000000`
- N=`16` formal=`2114` AA=`2114` dead=`0` R_N=`1.000000`
- N=`17` formal=`4228` AA=`4225` dead=`3` R_N=`0.999290`
- N=`18` formal=`7495` AA=`7338` dead=`157` R_N=`0.979053`
- N=`19` formal=`14990` AA=`12763` dead=`2227` R_N=`0.851434`
- N=`20` formal=`27328` AA=`16822` dead=`10506` R_N=`0.615559`

## Minimal unobserved prefixes

Count `8498` by length `{17: 3, 18: 151, 19: 1913, 20: 6431}`.
Claim language: `NOT OBSERVED WITHIN SEARCH BOUND`.

- `OOOEOOEOEOOOEEOOO` slack=`400369` sig=`O3,E1,O2,E1,O1,E1,O3,E2,O3` first_OO=`0`
- `OOOOEOOOOEOEOOEOO` slack=`1463251` sig=`O4,E1,O4,E1,O1,E1,O2,E1,O2` first_OO=`0`
- `OOOOOOOOOOEEOOOEO` slack=`4651897` sig=`O10,E2,O3,E1,O1` first_OO=`0`
- `OOEOOEOOEOEOOOOEOE` slack=`269297` sig=`O2,E1,O2,E1,O2,E1,O1,E1,O4,E1,O1,E1` first_OO=`0`
- `OOEOOEOOEOOOOOOEEO` slack=`1332179` sig=`O2,E1,O2,E1,O2,E1,O6,E2,O1` first_OO=`0`
- `OOEOOEOOOEOOOOEOOE` slack=`1332179` sig=`O2,E1,O2,E1,O3,E1,O4,E1,O2,E1` first_OO=`0`
- `OOEOOEOOOEOOOOOOOE` slack=`4520825` sig=`O2,E1,O2,E1,O3,E1,O7,E1` first_OO=`0`
- `OOEOOEOOOOEOOOEOOE` slack=`1332179` sig=`O2,E1,O2,E1,O4,E1,O3,E1,O2,E1` first_OO=`0`
- `OOEOOEOOOOEOOOOEOE` slack=`1332179` sig=`O2,E1,O2,E1,O4,E1,O4,E1,O1,E1` first_OO=`0`
- `OOEOOEOOOOOEEOOEOO` slack=`1332179` sig=`O2,E1,O2,E1,O5,E2,O2,E1,O2` first_OO=`0`
- `OOEOOEOOOOOEEOOOEE` slack=`269297` sig=`O2,E1,O2,E1,O5,E2,O3,E2` first_OO=`0`
- `OOEOOEOOOOOEOEEOEO` slack=`269297` sig=`O2,E1,O2,E1,O5,E1,O1,E2,O1,E1,O1` first_OO=`0`
- `OOEOOEOOOOOOEEEOOE` slack=`269297` sig=`O2,E1,O2,E1,O6,E3,O2,E1` first_OO=`0`
- `OOEOOEOOOOOOEOOOOE` slack=`4520825` sig=`O2,E1,O2,E1,O6,E1,O4,E1` first_OO=`0`
- `OOEOOOEOOEOOOEOOEO` slack=`1332179` sig=`O2,E1,O3,E1,O2,E1,O3,E1,O2,E1,O1` first_OO=`0`
- `OOEOOOEOOOEOOEEOOE` slack=`269297` sig=`O2,E1,O3,E1,O3,E1,O2,E2,O2,E1` first_OO=`0`

## Property search

- found: `False` name: `None`
- reason: no exact predicate holds on all F_j and fails on some formal itinerary
- distinctive: `[]`

## Hold-out

- hold F_j: `11012` later: `5553` fraction: `0.5042680711950599`

## Hard starts

- ordinary R: `0.6155591334894613` hard R: `0.00117096018735363`
- thinner: `True`

- n=`163` S=`20` leftover=`False` word=`OOOOOOEOEEOOOEOEOEOE`
- n=`173` S=`20` leftover=`False` word=`OOEOOOOOOOOEOOEOOEEO`
- n=`193` S=`20` leftover=`False` word=`OOOEOOOOOOOEOOOEEOEE`
- n=`229` S=`20` leftover=`False` word=`OOEOOOOOOOOOEOEEEEOE`
- n=`241` S=`20` leftover=`False` word=`OOOOOEOOOOOEOEOOEOEE`
- n=`265` S=`20` leftover=`False` word=`OOOOOEOOOEEEOOOEEOEO`
- n=`293` S=`20` leftover=`False` word=`OOOOOOOOEEEOOOOOEOEO`
- n=`321` S=`20` leftover=`False` word=`OOOEOOEOOEOOOOEEOOOE`
- n=`329` S=`20` leftover=`False` word=`OOOOOOOOEOOEOOEEOEEO`
- n=`357` S=`20` leftover=`False` word=`OOOOOOOOOOEEEEEOOEOO`
- n=`425` S=`20` leftover=`False` word=`OOOOOOOEOOEEOOOEOEEO`
- n=`427` S=`20` leftover=`False` word=`OOOOOEEOOOEEOEOOEOOE`

## Leftover witnesses

- `5`: S=`3` formal=`True` AA=`True` word=`OOE`
- `37`: S=`14` formal=`True` AA=`True` word=`OOOOEOOOEEOOEE`
- `365`: S=`14` formal=`True` AA=`True` word=`OOEOOEOOEOOEOE`

## Atlas follows control

- experiment `wa-20260827T200310Z-cuda-k20-n100000000` missing-by-N `{'1': 0, '2': 0, '3': 0, '4': 0, '5': 0, '6': 0, '7': 0, '8': 0, '9': 0, '10': 0, '11': 0, '12': 0, '13': 0, '14': 0, '15': 0, '16': 0, '17': 0, '18': 0, '19': 0, '20': 0}`

## Existing Lean (unchanged)

- `prefixNoncontracting`: `True`
- `aboveAnchor_not_envelope_drop`: `True`
- `aboveAnchor_not_odd_even`: `True`
- `isolatedOddSurvival_bound`: `True`
- `AboveAnchor`: `True`
- `power_bound_word`: `True`
- new Lean file: `False`
- no LANG_FORMAL / LANG_ABOVE_ANCHOR: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- global_non_realizability: `False`
- forbidden_factor_theorem: `False`
- search_horizon_is_L: `False`
- cyclemin_in_language: `False`
- formal_realized_lean: `False`
- new_atlas_language: `False`
- letter_chain: `False`

## Decision

**FORMAL_REALIZED_GAP_CLOSED**

F_j from the low-n half realizes later; remaining unobserved prefixes are window or scale artefacts, not a new exact P.

