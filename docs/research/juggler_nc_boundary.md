# Juggler noncontracting realization boundary

Status: **NC_BOUNDARY_COMPLEX**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Studies `N_w = {n in R_w : T_w(n) >= n}`.
The identity is the definition, not a discovery. Does not reopen
PE-factor, residual-future, sum-rho, realization-set branching,
or landing-image geometry.

## Branch budget

```text
Mathematical target     structural description of N_w / a_w
Novelty hypothesis      threshold, cell, (k,o,run), or inheritance
Falsifier               inversions; same (k,o) split; T>=n restatement
Existing machinery      follows, image, power_bound_contracts
Maximum Phase-0 scope   n<=4000 k<=20; selected n<=1e5
```

## Metadata

- diagnostic window: `n<= 4000`, `k<= 20`
- confirm window: `n<= 100000` selected families
- engine control layer modified: `False`
- classification: **NC_BOUNDARY_COMPLEX**
- sorry-free: `True`

N_w is not an upper tail: inversions n1 in N_w < n2 in C_w exist. The same (k,o) and even the same run signature split a_w. Noncontraction can appear after a contracting prefix and can vanish after a noncontracting prefix. First-defect position is unrestricted on N_w. No description simpler than T_w(n)>=n survived.

## Calibration

- `N_E` empty: `True`
- `N_O` equals all odds: `True` size=`2000`
- formally contracting exceptions: `[]`

## Diagnostic partition

- words: `7519` expanding `3166`
- expanding with nonempty N: `2584`
- expanding with empty N in window: `582`
- upper tails: `2583`
- inversions (n1 in N, n2 in C, n1<n2): `1`
- fragmented N (components>4): `230`
- smallest inversion: `{'word': 'EOO', 'k': 3, 'o': 2, 'gap': -1, 'expanding': True, 'runs': 2, 'max_O_run': 2, 'max_E_run': 1, 'first_mixed': 0, 'm': 2, 'a': 10, 'a_minus_m': 8, 'r_size': 491, 'n_size': 488, 'n_components': 488, 'n_max_gap': 528, 'n_max': 3598, 'r_max': 3598, 'upper_tail': False, 'inversion': {'n1': 10, 'n2': 12}, 'image_a': 11}`

## Same (k,o) and run signature

- (k,o) groups that split a_w: `58` / `82`
- strongest (k,o) split: `{'k': 13, 'o': 9, 'low_word': 'OOOOEOOOEEOOE', 'low_a': 37, 'high_word': 'OOEOOEOOEOOOE', 'high_a': 3989, 'ratio': 107.8108108108108, 'n_words': 121}`
- run-signature groups that split a_w: `457`
- strongest run split: `{'key': (11, 8, 5, 4, 2, 4), 'low_word': 'OOOOEOOOEEO', 'low_a': 37, 'high_word': 'OOOEEOOOOEO', 'high_a': 3753, 'ratio': 101.43243243243244}`

## Prefix extension

- `N_wb ⊆ N_w`: `False`
- late expand (contracting prefix, NC word): `1774` smallest=`{'parent': 'EO', 'child': 'EOO', 'n': 10}`
- late contract (NC prefix, contracting itinerary): `3554` smallest=`{'parent': 'OOOE', 'child': 'OOOEE', 'n': 3}`

## First defect

- samples: `698`
- NC positions: `{'0': 690, '2': 1}`
- C positions: `{'0': 7}`

## Adjacency / first-step cells

- even-start left-cell count: `2` / `2`
- first non-endpoint: `None`

## Families

- `E` gap=`1` m=`2` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EE` gap=`3` m=`4` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEE` gap=`7` m=`16` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEE` gap=`15` m=`256` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `O` gap=`-1` m=`1` a=`1` |N|=`2000` comps=`2000` tail=`True` inv=`None`
- `OO` gap=`-5` m=`1` a=`1` |N|=`1010` comps=`1010` tail=`True` inv=`None`
- `OOO` gap=`-19` m=`1` a=`1` |N|=`510` comps=`510` tail=`True` inv=`None`
- `OOOO` gap=`-65` m=`1` a=`1` |N|=`282` comps=`282` tail=`True` inv=`None`
- `OOOOO` gap=`-211` m=`1` a=`1` |N|=`136` comps=`136` tail=`True` inv=`None`
- `OOOOOO` gap=`-665` m=`1` a=`1` |N|=`67` comps=`67` tail=`True` inv=`None`
- `OE` gap=`1` m=`7` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEE` gap=`5` m=`7` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEEE` gap=`13` m=`7` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEEEE` gap=`29` m=`41` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOE` gap=`-1` m=`5` a=`5` |N|=`500` comps=`500` tail=`True` inv=`None`
- `OOEE` gap=`7` m=`5` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOEEE` gap=`23` m=`5` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOEEEE` gap=`55` m=`43` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOOE` gap=`-11` m=`3` a=`3` |N|=`228` comps=`228` tail=`True` inv=`None`
- `OOOEE` gap=`5` m=`3` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOOEEE` gap=`37` m=`3` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOOEEEE` gap=`101` m=`75` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOOOE` gap=`-49` m=`37` a=`37` |N|=`146` comps=`146` tail=`True` inv=`None`
- `OOOOEE` gap=`-17` m=`271` a=`271` |N|=`68` comps=`68` tail=`True` inv=`None`
- `OOOOEEE` gap=`47` m=`271` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOOOEEEE` gap=`175` m=`271` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EO` gap=`1` m=`2` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EOO` gap=`-1` m=`2` a=`10` |N|=`488` comps=`488` tail=`False` inv=`{'n1': 10, 'n2': 12}`
- `EOOO` gap=`-11` m=`2` a=`10` |N|=`163` comps=`163` tail=`True` inv=`None`
- `EOOOO` gap=`-49` m=`2` a=`1370` |N|=`37` comps=`37` tail=`True` inv=`None`
- `EEO` gap=`5` m=`4` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEOO` gap=`7` m=`4` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEOOO` gap=`5` m=`4` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEOOOO` gap=`-17` m=`4` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEO` gap=`13` m=`16` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEOO` gap=`23` m=`16` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEOOO` gap=`37` m=`16` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEOOOO` gap=`47` m=`16` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEEO` gap=`29` m=`256` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEEOO` gap=`55` m=`256` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEEOOO` gap=`101` m=`256` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `EEEEOOOO` gap=`175` m=`256` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEO` gap=`-1` m=`15` a=`15` |N|=`482` comps=`482` tail=`True` inv=`None`
- `OEOO` gap=`-11` m=`19` a=`19` |N|=`236` comps=`236` tail=`True` inv=`None`
- `OEEO` gap=`7` m=`23` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEEOO` gap=`5` m=`23` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEEEO` gap=`23` m=`7` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEEEOO` gap=`37` m=`7` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOEO` gap=`-11` m=`9` a=`9` |N|=`245` comps=`245` tail=`True` inv=`None`
- `OOEOO` gap=`-49` m=`69` a=`69` |N|=`123` comps=`123` tail=`True` inv=`None`
- `OOEEO` gap=`5` m=`33` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOEEOO` gap=`-17` m=`53` a=`53` |N|=`86` comps=`86` tail=`True` inv=`None`
- `OOEEEO` gap=`37` m=`5` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOEEEOO` gap=`47` m=`5` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOOEO` gap=`-49` m=`77` a=`77` |N|=`108` comps=`108` tail=`True` inv=`None`
- `OOOEOO` gap=`-179` m=`99` a=`99` |N|=`63` comps=`63` tail=`True` inv=`None`
- `OOOEEO` gap=`-17` m=`25` a=`25` |N|=`59` comps=`59` tail=`True` inv=`None`
- `OOOEEOO` gap=`-115` m=`221` a=`221` |N|=`36` comps=`36` tail=`True` inv=`None`
- `OOOEEEO` gap=`47` m=`3` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OOOEEEOO` gap=`13` m=`3` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`
- `OEOE` gap=`7` m=`15` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`

## Selected confirm

- words: `62` inversions `1`
- expanding families still upper tail: `False`

- `O` gap=`-1` m=`1` a=`1` |N|=`50000` comps=`50000` tail=`True` inv=`None`
- `OO` gap=`-5` m=`1` a=`1` |N|=`24985` comps=`24985` tail=`True` inv=`None`
- `OOE` gap=`-1` m=`5` a=`5` |N|=`12467` comps=`12467` tail=`True` inv=`None`
- `OOOE` gap=`-11` m=`3` a=`3` |N|=`6332` comps=`6332` tail=`True` inv=`None`
- `OEO` gap=`-1` m=`15` a=`15` |N|=`12509` comps=`12509` tail=`True` inv=`None`
- `OOEO` gap=`-11` m=`9` a=`9` |N|=`6291` comps=`6291` tail=`True` inv=`None`
- `OEOE` gap=`7` m=`15` a=`None` |N|=`0` comps=`0` tail=`True` inv=`None`

## Lean

- `power_bound_contracts`: `True`
- `image_monotone_of_follows`: `True`
- `even_preimage_iff`: `True`
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
- forbidden_factor_law: `False`
- reopen_pe_factors: `False`
- reopen_residual_quotient: `False`
- reopen_sum_rho: `False`
- reopen_realization_geometry: `False`
- reopen_landing_image: `False`
- automaton: `False`

## Decision

**NC_BOUNDARY_COMPLEX**

N_w is not an upper tail: inversions n1 in N_w < n2 in C_w exist. The same (k,o) and even the same run signature split a_w. Noncontraction can appear after a contracting prefix and can vanish after a noncontracting prefix. First-defect position is unrestricted on N_w. No description simpler than T_w(n)>=n survived.

This is not a halt result. N_w is not a new invariant.

