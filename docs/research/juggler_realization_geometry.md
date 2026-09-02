# Juggler realization-set geometry

Status: **REALIZATION_GEOMETRY_COMPLEX**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Studies the realizing sets
`R_w(N) = {n <= N : follows(n,w)}` of the prefix trie. Does not
reopen PE-factor grammar or residual-future quotients.

## Branch budget

```text
Mathematical target     What geometry of R_w makes a prefix unary?
Novelty hypothesis      inverse-floor cells / scale of R_w force d(w)=1
Falsifier               unary without monochrome landings, or a square
                        amplification law that survives mixed itineraries, or
                        a hole that is CELL_EMPTY rather than scale
Existing machinery      follows_itinerary, image_after, even_preimage, atlas trie
Maximum Phase-0 scope   R_w on n<=4000 then 1e5; selected roots n<=1e7
```

## Metadata

- diagnostic window: `n<= 4000`, `k<= 12`
- confirm window: `n<= 100000`, `k<= 12`
- engine control layer modified: `False`
- classification: **REALIZATION_GEOMETRY_COMPLEX**
- sorry-free: `True`

Appending a letter is the landing-parity filter of T_w(R_w), which is the definition of follows. Prepending E is the even-cell union already in even_preimage_iff; it is exact on every finite window. Prepending O leaks the window because odd landings escape [1,N]. Naive m(wE)>=m(w)^2 fails after an odd letter (OOOE at 3; OEEE 7->41). The first holes are SCALE_LIMITED, not CELL_EMPTY. No new set geometry beyond follows plus inverse-floor cells survived.

## Atlas reproduction

Even tower `m(E^r)` versus `2^{2^{r-1}}`:

- r=`1` word=`E` min=`2` tower=`2` status=`FOUND`
- r=`2` word=`EE` min=`4` tower=`4` status=`FOUND`
- r=`3` word=`EEE` min=`16` tower=`16` status=`FOUND`
- r=`4` word=`EEEE` min=`256` tower=`256` status=`FOUND`
- r=`5` word=`EEEEE` min=`65536` tower=`65536` status=`FOUND`
- r=`6` word=`EEEEEE` min=`None` tower=`4294967296` status=`NOT_FOUND_WITHIN_BOUND`
- r=`7` word=`EEEEEEE` min=`None` tower=`None` status=`NOT_FOUND_WITHIN_BOUND`

First unary parents:

- `EEEEE` min=`65536` class=`UNARY_O`
- `EEEEO` min=`256` class=`UNARY_O`
- `EEEOE` min=`6250000` class=`UNARY_E`

First rooted holes:

- `EEEEEE` status=`NOT_FOUND_WITHIN_BOUND`
- `EEEEOE` status=`NOT_FOUND_WITHIN_BOUND`
- `EEEOEO` status=`NOT_FOUND_WITHIN_BOUND`

- `EE…` words at length 12: `37` unary `37`

Leading-`E` unary fraction at length 19:

- leadE=`0` nodes=`76332` unary=`21785` frac=`0.28539799821830947`
- leadE=`1` nodes=`1476` unary=`1470` frac=`0.9959349593495935`
- leadE=`2` nodes=`29` unary=`29` frac=`1.0`
- leadE=`3` nodes=`5` unary=`5` frac=`1.0`
- leadE=`4` nodes=`2` unary=`2` frac=`1.0`
- leadE=`5` nodes=`1` unary=`1` frac=`1.0`

## Missing-child status

- `EEEEEE` status=`SCALE_LIMITED` — m(E^6)=even_tower(6)=4294967296 > atlas n_max=100000000
- `EEEEOE` status=`SCALE_LIMITED` — smallest interior realizing state 39062504258660 > atlas n_max=100000000; no rooted realizer in the scan
- `EEEOEO` status=`SCALE_LIMITED` — smallest interior realizing state 2608762880 > atlas n_max=100000000; no rooted realizer in the scan

## Root versus interior

- `EEEEEE` hosts=`2906` min_pos=`1` min_state=`4294972782` in_atlas=`0` follows=`True` host_n=`40853379` host=`OOOOEEEEEEEEOOOOOOOO`
- `EEEEOE` hosts=`6164` min_pos=`2` min_state=`39062504258660` in_atlas=`0` follows=`True` host_n=`14435959` host=`OOOOEEOEEEEOEEEOOOOO`
- `EEEOEO` hosts=`11310` min_pos=`1` min_state=`2608762880` in_atlas=`0` follows=`True` host_n=`27551539` host=`OOEOOEEEEOEOEEEOOOOO`

## Selected exact roots n<=`10000000`

- `EEEEEE` |R|=`0` min=`None` max=`None`
- `EEEEOE` |R|=`0` min=`None` max=`None`
- `EEEOEO` |R|=`0` min=`None` max=`None`
- `EEEEE` |R|=`604928` min=`65536` max=`5764800`
- `EEEEO` |R|=`1063` min=`256` max=`6560`
- `EEEOE` |R|=`481443` min=`6250000` max=`10000000`

## Window artefact

- `EEEE` diagnostic=`UNARY_O` atlas=`BINARY` — n<=4000 cannot see m(EEEEE)=65536, so EEEE looks UNARY_O in the small window

## Set recurrence

- prepend E on the empty itinerary: exact=`True`
- prepend O on the empty itinerary: exact=`False` predicted=`126` actual=`2000` leak=`1874`
- even-tower prepend E: `True`
- prepend E mismatches among prefixes: `0`
- prepend O mismatches among prefixes: `946` first=`{'word': 'O', 'predicted': 67, 'actual': 1010, 'missing': 943}`
- append rule: R_{wb} = {n in R_w : T_w(n) has parity b}
- prepend E rule: R_{Ew}(N) = union_{q in R_w(N)} (even_preimage(q) ∩ 2Z ∩ [1,N])
- prepend O rule: R_{Ow} = union_{q in R_w} (odd_cell(q) ∩ (2Z+1)); not closed on [1,N]

## Diagnostic realizing sets

- words: `1836`
- uncovered realizers: `0`
- unary nodes: `1186` monochrome landings `1186`
- unary with a singleton landing: `1025`
- binary nodes: `650` scale-separated children `307`
- unary prefixes that regain two children: `62`
- interval classes by degree: `{'BINARY': {'FRAGMENTED': 390, 'FEW_INTERVALS': 260}, 'UNARY_O': {'SINGLE_INTERVAL': 191, 'FEW_INTERVALS': 198, 'FRAGMENTED': 259}, 'UNARY_E': {'FRAGMENTED': 148, 'FEW_INTERVALS': 188, 'SINGLE_INTERVAL': 202}}`

Branching profile (diagnostic):

- k=`1` {'BINARY': 2}
- k=`2` {'BINARY': 4}
- k=`3` {'BINARY': 8}
- k=`4` {'BINARY': 13, 'UNARY_O': 2, 'UNARY_E': 1}
- k=`5` {'BINARY': 20, 'UNARY_O': 4, 'UNARY_E': 5}
- k=`6` {'BINARY': 29, 'UNARY_O': 14, 'UNARY_E': 6}
- k=`7` {'BINARY': 43, 'UNARY_O': 20, 'UNARY_E': 15}
- k=`8` {'BINARY': 73, 'UNARY_O': 34, 'UNARY_E': 14}
- k=`9` {'BINARY': 126, 'UNARY_O': 50, 'UNARY_E': 18}
- k=`10` {'BINARY': 127, 'UNARY_O': 93, 'UNARY_E': 100}
- k=`11` {'BINARY': 121, 'UNARY_O': 186, 'UNARY_E': 140}
- k=`12` {'UNARY_O': 245, 'UNARY_E': 239, 'BINARY': 84}

Adversarial prefixes in the diagnostic window:

- `E` class=`BINARY` |R|=`2000` min=`2` max=`4000` rho_O=`0.4885` rho_E=`0.5115` landings=`63` mono=`False` sep=`False`
- `EE` class=`BINARY` |R|=`1023` min=`4` max=`3968` rho_O=`0.5826001955034213` rho_E=`0.4173998044965787` landings=`7` mono=`False` sep=`False`
- `EEE` class=`BINARY` |R|=`427` min=`16` max=`2400` rho_O=`0.04918032786885246` rho_E=`0.9508196721311475` landings=`2` mono=`False` sep=`True`
- `EEEE` class=`UNARY_O` |R|=`406` min=`256` max=`2400` rho_O=`1.0` rho_E=`0.0` landings=`1` mono=`True` sep=`None`
- `EO` class=`BINARY` |R|=`977` min=`2` max=`4000` rho_O=`0.5025588536335721` rho_E=`0.49744114636642783` landings=`32` mono=`False` sep=`False`
- `EOE` class=`BINARY` |R|=`486` min=`50` max=`4000` rho_O=`0.5596707818930041` rho_E=`0.4403292181069959` landings=`15` mono=`False` sep=`False`
- `EOO` class=`BINARY` |R|=`491` min=`2` max=`3598` rho_O=`0.3340122199592668` rho_E=`0.6659877800407332` landings=`15` mono=`False` sep=`False`
- `O` class=`BINARY` |R|=`2000` min=`1` max=`3999` rho_O=`0.505` rho_E=`0.495` landings=`2000` mono=`False` sep=`False`
- `OO` class=`BINARY` |R|=`1010` min=`1` max=`3999` rho_O=`0.504950495049505` rho_E=`0.49504950495049505` landings=`1010` mono=`False` sep=`False`
- `OOO` class=`BINARY` |R|=`510` min=`1` max=`3999` rho_O=`0.5529411764705883` rho_E=`0.4470588235294118` landings=`510` mono=`False` sep=`False`
- `OE` class=`BINARY` |R|=`990` min=`7` max=`3995` rho_O=`0.4868686868686869` rho_E=`0.5131313131313131` landings=`433` mono=`False` sep=`False`
- `OEO` class=`BINARY` |R|=`482` min=`15` max=`3985` rho_O=`0.4896265560165975` rho_E=`0.5103734439834025` landings=`216` mono=`False` sep=`False`
- `OOE` class=`BINARY` |R|=`500` min=`5` max=`3989` rho_O=`0.49` rho_E=`0.51` landings=`500` mono=`False` sep=`False`
- `EEO` class=`BINARY` |R|=`596` min=`4` max=`3968` rho_O=`0.33053691275167785` rho_E=`0.6694630872483222` landings=`4` mono=`False` sep=`True`
- `OEEEE` class=`BINARY` |R|=`195` min=`41` max=`3995` rho_O=`0.15384615384615385` rho_E=`0.8461538461538461` landings=`2` mono=`False` sep=`True`
- `OOOOE` class=`BINARY` |R|=`146` min=`37` max=`3939` rho_O=`0.5342465753424658` rho_E=`0.4657534246575342` landings=`146` mono=`False` sep=`False`

## Confirm window

- words: `2982` uncovered `0`
- unary `1073` monochrome `1073`
- singleton landings `916`
- binary scale-separated `327` / `1909`
- unary-to-binary `52`

Smallest unary-to-binary returns in the confirm window:

- `EOOOEEEO` → `EOOOEEEOO` min=`10`
- `OEOEEEOO` → `OEOEEEOOO` min=`15`
- `EEEOO` → `EEEOOO` min=`16`
- `OEOOEOEEEO` → `OEOOEOEEEOO` min=`19`
- `OEEOOOE` → `OEEOOOEE` min=`23`
- `EOOEEEOO` → `EOOEEEOOO` min=`26`
- `OOEEOEEEOO` → `OOEEOEEEOOO` min=`33`
- `OOEEEEOO` → `OOEEEEOOO` min=`43`

Atlas unary-to-binary (capped scan of continuations):

- examples found: `2543`
- among `EE…` parents: `5`

- `OEEEEO` → `OEEEEOO`
- `EOEEEO` → `EOEEEOO`
- `EEOEEO` → `EEOEEOO`
- `EEEEOO` → `EEEEOOO`
- `EEOOEOO` → `EEOOEOOE`
- `OEEEOOOE` → `OEEEOOOEE`
- `EOEEOOOE` → `EOEEOOOEE`
- `EEOOOEEOE` → `EEOOOEEOEO`

## Minimum-realizer extension

- tower identity in the diagnostic window: `True`
- square-law counterexample: `{'word': 'OOOE', 'm_w': 3, 'm_wE': 3, 'landing': 6}`
- odd-landing square counterexample: `{'word': 'OEEE', 'm_w': 7, 'm_wE': 41, 'landing': 1}`
- even-landing identity fail: `None`

The identity `m(E^{r+1})=m(E^r)^2` is special to the pure even
tower. After an odd letter, `m(wE)=m(w)` whenever `T_w(m(w))` is
even. The square lower bound does not survive mixed itineraries.

## Lean

- `even_tower_to_one`: `True`
- `even_preimage_iff`: `True`
- `odd_preimage_iff`: `True`
- `odd_preimage_unique`: `True`
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
- automaton: `False`

## Decision

**REALIZATION_GEOMETRY_COMPLEX**

Appending a letter is the landing-parity filter of T_w(R_w), which is the definition of follows. Prepending E is the even-cell union already in even_preimage_iff; it is exact on every finite window. Prepending O leaks the window because odd landings escape [1,N]. Naive m(wE)>=m(w)^2 fails after an odd letter (OOOE at 3; OEEE 7->41). The first holes are SCALE_LIMITED, not CELL_EMPTY. No new set geometry beyond follows plus inverse-floor cells survived.

This is not a halt result and not a forbidden-factor law.

