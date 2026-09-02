# Juggler drift-first-passage tree

Status: **DRIFT_FIRST_PASSAGE_COMPLEX**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Studies nested realizing sets
A_w of actual prefix-NC words. Does not claim tau_+ < infinity.
Does not reopen prefix-NC word admissibility, endpoint
filtration, the corridor, escape-state, ResidualStep, or
odd-fourth-power.

## Branch budget

```text
Mathematical target     Along actual prefix-NC chains, does A_w^{NC}
                        acquire a named arithmetic constraint that
                        forbids indefinite NC continuation?
Novelty hypothesis      the nested start-set thins or prunes
Falsifier               only tautological |A_w ∩ window| decrease
Existing machinery      slim crossing, exponent_gap, Ival pullback
Maximum Phase-0 scope   one probe; nested signatures; hunt; no Lean
```

## Metadata

- search_id: `juggler-drift-first-passage-phase0-n2-2000-hunt100000`
- algorithm_version: `drift-first-passage-v1`
- classification_version: `drift-first-passage-class-v1`
- nested window: `n=2..2000`
- hunt window: `n=2..100000`
- horizon: `10000` (not L)
- nested bit_cap: `4096`
- hunt bit_cap: `2000000`
- crossing_policy: `stop at first G_k>0; absorb if T^k=1 still NC`
- engine control layer modified: `False`
- classification: **DRIFT_FIRST_PASSAGE_COMPLEX**
- sorry-free: `True`

nested A_w signatures do not compress below the itineraries themselves; 10 extensions are tautological window subsets and 259 named-thinner hits are residue/modulus artefacts of longer prefixes, not a pruning rule; hunt max tau_+=253 is a larger record, not a structured unbounded family; 1 hunt bit-cap leftovers are not a bound L.

## Nested census

- starts: `1999`
- crossed: `1999`
- absorbed at 1 still NC: `0`
- unfinished: `0`
- identity failures: `0`
- even tau_+ failures: `0`
- unique prefix-NC words: `1318`
- mixed prefix-NC words: `1307`
- max tau_+ in nested window: `70`
- max peak bits: `900`

## Extension tags

- `empty`: `1072`
- `same`: `1048`
- `strict_subset`: `10`
- `named_thinner`: `259`

## Named-thinner examples

- `OOOE` + `O` → `OOOEO` counts `117`→`57` mod `2`→`2`
- `OOOO` + `O` → `OOOOO` counts `134`→`60` mod `2`→`2`
- `OOOO` + `E` → `OOOOE` counts `134`→`74` mod `2`→`2`
- `OOOOE` + `O` → `OOOOEO` counts `74`→`38` mod `2`→`2`
- `OOOOE` + `E` → `OOOOEE` counts `74`→`36` mod `2`→`2`
- `OOOOEO` + `O` → `OOOOEOO` counts `38`→`13` mod `2`→`2`
- `OOOOEO` + `E` → `OOOOEOE` counts `38`→`25` mod `2`→`2`
- `OOOOEOO` + `O` → `OOOOEOOO` counts `13`→`7` mod `2`→`2`
- `OOOOEOO` + `E` → `OOOOEOOE` counts `13`→`6` mod `2`→`2`
- `OOOOEOOO` + `O` → `OOOOEOOOO` counts `7`→`3` mod `2`→`12`
- `OOOOEOOO` + `E` → `OOOOEOOOE` counts `7`→`4` mod `2`→`2`
- `OOOOEOOOE` + `O` → `OOOOEOOOEO` counts `4`→`3` mod `2`→`2`

## Depth census (words vs signatures)

- k=`1` words=`1` mixed=`0` signatures=`1` compression=`1.0` max_|A|=`999`
- k=`2` words=`1` mixed=`0` signatures=`1` compression=`1.0` max_|A|=`505`
- k=`3` words=`2` mixed=`1` signatures=`1` compression=`0.5` max_|A|=`254`
- k=`4` words=`3` mixed=`2` signatures=`1` compression=`0.333333` max_|A|=`134`
- k=`5` words=`4` mixed=`3` signatures=`4` compression=`1.0` max_|A|=`74`
- k=`6` words=`8` mixed=`7` signatures=`8` compression=`1.0` max_|A|=`38`
- k=`7` words=`13` mixed=`12` signatures=`13` compression=`1.0` max_|A|=`25`
- k=`8` words=`19` mixed=`18` signatures=`19` compression=`1.0` max_|A|=`16`
- k=`9` words=`38` mixed=`37` signatures=`38` compression=`1.0` max_|A|=`10`
- k=`10` words=`55` mixed=`54` signatures=`55` compression=`1.0` max_|A|=`6`
- k=`11` words=`87` mixed=`86` signatures=`79` compression=`0.908046` max_|A|=`4`
- k=`12` words=`98` mixed=`98` signatures=`82` compression=`0.836735` max_|A|=`3`
- k=`13` words=`85` mixed=`85` signatures=`73` compression=`0.858824` max_|A|=`2`
- k=`14` words=`90` mixed=`90` signatures=`76` compression=`0.844444` max_|A|=`2`
- k=`15` words=`79` mixed=`79` signatures=`66` compression=`0.835443` max_|A|=`2`
- k=`16` words=`65` mixed=`65` signatures=`57` compression=`0.876923` max_|A|=`2`
- k=`17` words=`65` mixed=`65` signatures=`57` compression=`0.876923` max_|A|=`2`
- k=`18` words=`54` mixed=`54` signatures=`47` compression=`0.87037` max_|A|=`2`
- k=`19` words=`55` mixed=`55` signatures=`48` compression=`0.872727` max_|A|=`1`
- k=`20` words=`52` mixed=`52` signatures=`46` compression=`0.884615` max_|A|=`1`
- k=`21` words=`45` mixed=`45` signatures=`40` compression=`0.888889` max_|A|=`1`
- k=`22` words=`45` mixed=`45` signatures=`40` compression=`0.888889` max_|A|=`1`
- k=`23` words=`38` mixed=`38` signatures=`36` compression=`0.947368` max_|A|=`1`
- k=`24` words=`27` mixed=`27` signatures=`25` compression=`0.925926` max_|A|=`1`
- k=`25` words=`27` mixed=`27` signatures=`25` compression=`0.925926` max_|A|=`1`
- k=`26` words=`22` mixed=`22` signatures=`21` compression=`0.954545` max_|A|=`1`
- k=`27` words=`16` mixed=`16` signatures=`15` compression=`0.9375` max_|A|=`1`
- k=`28` words=`16` mixed=`16` signatures=`15` compression=`0.9375` max_|A|=`1`
- k=`29` words=`14` mixed=`14` signatures=`13` compression=`0.928571` max_|A|=`1`
- k=`30` words=`14` mixed=`14` signatures=`13` compression=`0.928571` max_|A|=`1`
- k=`31` words=`13` mixed=`13` signatures=`12` compression=`0.923077` max_|A|=`1`
- k=`32` words=`11` mixed=`11` signatures=`10` compression=`0.909091` max_|A|=`1`
- k=`33` words=`11` mixed=`11` signatures=`10` compression=`0.909091` max_|A|=`1`
- k=`34` words=`11` mixed=`11` signatures=`10` compression=`0.909091` max_|A|=`1`
- k=`35` words=`9` mixed=`9` signatures=`8` compression=`0.888889` max_|A|=`1`
- k=`36` words=`9` mixed=`9` signatures=`8` compression=`0.888889` max_|A|=`1`
- k=`37` words=`8` mixed=`8` signatures=`7` compression=`0.875` max_|A|=`1`
- k=`38` words=`8` mixed=`8` signatures=`7` compression=`0.875` max_|A|=`1`
- k=`39` words=`8` mixed=`8` signatures=`7` compression=`0.875` max_|A|=`1`
- k=`40` words=`7` mixed=`7` signatures=`6` compression=`0.857143` max_|A|=`1`
- k=`41` words=`7` mixed=`7` signatures=`6` compression=`0.857143` max_|A|=`1`
- k=`42` words=`7` mixed=`7` signatures=`6` compression=`0.857143` max_|A|=`1`
- k=`43` words=`6` mixed=`6` signatures=`5` compression=`0.833333` max_|A|=`1`
- k=`44` words=`6` mixed=`6` signatures=`5` compression=`0.833333` max_|A|=`1`
- k=`45` words=`6` mixed=`6` signatures=`5` compression=`0.833333` max_|A|=`1`
- k=`46` words=`5` mixed=`5` signatures=`5` compression=`1.0` max_|A|=`1`
- k=`47` words=`5` mixed=`5` signatures=`5` compression=`1.0` max_|A|=`1`
- k=`48` words=`5` mixed=`5` signatures=`5` compression=`1.0` max_|A|=`1`
- k=`49` words=`5` mixed=`5` signatures=`5` compression=`1.0` max_|A|=`1`
- k=`50` words=`3` mixed=`3` signatures=`3` compression=`1.0` max_|A|=`1`
- k=`51` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`52` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`53` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`54` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`55` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`56` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`57` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`58` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`59` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`60` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`61` words=`2` mixed=`2` signatures=`2` compression=`1.0` max_|A|=`1`
- k=`62` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`
- k=`63` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`
- k=`64` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`
- k=`65` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`
- k=`66` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`
- k=`67` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`
- k=`68` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`
- k=`69` words=`1` mixed=`1` signatures=`1` compression=`1.0` max_|A|=`1`

## Least-constrained mixed prefixes

- `OOE` k=`3` |A|=`254` G=`-1` modulus=`2`
- `OOEO` k=`4` |A|=`130` G=`-11` modulus=`2`
- `OOOE` k=`4` |A|=`117` G=`-11` modulus=`2`
- `OOOOE` k=`5` |A|=`74` G=`-49` modulus=`2`
- `OOEOO` k=`5` |A|=`64` G=`-49` modulus=`2`
- `OOOEO` k=`5` |A|=`57` G=`-49` modulus=`2`
- `OOOOEO` k=`6` |A|=`38` G=`-179` modulus=`2`
- `OOEOOO` k=`6` |A|=`36` G=`-179` modulus=`2`

## tau_+ hunt

- starts: `99999`
- crossed: `99998`
- unfinished: `1`
- max tau_+: `253` at n=`78901`
- known record: n=`193` tau_+=`70`
- beats known record: `12`
- finite max is not a bound: `True`

## Longest crossings in the hunt

- n=`78901` tau_+=`253` o=`159` peak_bits=`1234916` word=`OOOOEOEOOOOEOEEOOOOEOOOOOEOEOOOOOEOOOOOEOOOOEOOOOOOOOOEEOOOOEEOOOEOEOOEOOEOOOOOEOEOOEOEOEEOEEOOOEEOOOEOOOOOOOEOEEEOOEOEEOOOOEOEEOEOEOOEOEEOEOEOEOOOEEEOOOEOOEOOEOEOEOEOEEEOOEOEEOEOOEOOOOOEOEEOOOEOOEOEOOOOOOEOEEOOEOEEEOOOOOOOOOEEOOEOOEEOOOEEEOEEEEOOEOOEEE`
- n=`34175` tau_+=`183` o=`115` peak_bits=`19297` word=`OOOOOEOOOEOOEOOOOEOEEEOOOOEOEOEOOOOEEOEOOOEOOOOOOOOEOOOOOEOOOEEEEOEOEOOOOOOOEEOOEOEOEOOEOOEOOOEOOOEEOEOEOOEEOOEEOOOEOOOOOEEOEEOOOEEOOEOOEOOOOEOEOEOOOOOEEEEOEEOOOOEEEOOOEOEEOEEOOEOOEEE`
- n=`28719` tau_+=`156` o=`98` peak_bits=`12480` word=`OOEOOOOOOOOOEEOOOOEEOOOEOOOOOOOEEOOOOEOOOEOEOEEEOEEOOOEOOOOOOEEEOEOOOEOEOEEEOOEOEEOOEOOEOOEOOEOEOOEOOOOOOOOEOEOOOOEEOOOEOOEOOOEOOOEEOOOEEEEOOOEEEOEEEEOOOEEE`
- n=`13325` tau_+=`154` o=`97` peak_bits=`4223` word=`OOOOOOOOOOOOOOEOEEEOOOEOOOEEOOEEEOOEOOOOOOEOEOOOOEOOEEEOEOOEEOOEEOOOOEOOOEOEEEOOOOOOOOEOOOEOEOEOEOOOEOEEOOOOEOOEOOEOOEOEOEEOOEOOEOOOOEEEEEEOOEOOOOEOEEOEEE`
- n=`56509` tau_+=`138` o=`87` peak_bits=`2923` word=`OOEOOEOOOEOOEOEOOEOEOOOOOOOOOEEEEOOEOOOOEOOEOOEOOOOOOEOEEEOOOOOEOEEEEOOOOOEOOOOEOEOEEEOOOOEOOEOEOEOOOOOOOEOEOEOEOEOOEEOOOOEOOEOEEOOEEEOEEE`
- n=`83787` tau_+=`138` o=`87` peak_bits=`2210` word=`OOEOOOOEOEOEOEOOOOEEOOOOEOOOOOOEEOOOOOOEEOEOOOEOEOEOOEEOEOOOOOEEOOOOOEOEEEOEOEEOOEOOEEOEOOEOEOEOOOOEOOOEEOOOOOOOOOEEOEOOEEOOOOOEEEEOOOEEEE`
- n=`15845` tau_+=`132` o=`83` peak_bits=`79357` word=`OOOOOOOOOOOOOOOOOOOEEOEOEEOEEOOOEOOOOOOOOOOEEEEEOOOOOEOOEOEEOOOOEOOEEOOEEOOOEOOEEOOEEEOEOOOOOEEOEOEOEOEOOOEEEOEOOOEEOOOEEOOEOOEEOEEE`
- n=`39947` tau_+=`124` o=`78` peak_bits=`6529` word=`OOEOOOOEOOOOOEEEOOOOEOOEEEOEOOOOOOOEOOOEEOOEEOEOOOOOOEOOOOOOOEEOEEOEOOEOEEOEOOEEOEOOOEOEOOOOEEEOOOOEOOOOEEOOOOOEEEEEOEOOOEEE`
- n=`52505` tau_+=`123` o=`77` peak_bits=`15273` word=`OOOOEOOOOOEOEEEOOEOOOEEOEOOOOOOOOOOOEOEEOOOEOEOOOOEOEOEOEOEOOOEOOOOEEOEOOOEOOOOOOOEEEEOEEOOOOEOOEEOEEOEOOOEOOEOOOEOEOEEEEEE`
- n=`30717` tau_+=`121` o=`76` peak_bits=`15684` word=`OOOEOOEOEOOOOOOOOOOEOOOOOOOOEEEOOOEEOOEOEOEEOOOEOOEEEOOOOOEOOOOEEOEOOEOOOOEOOOEEOOEEEEOEEOOEOOOOOOOOOEOEEEOEOEOEEOOEOEEEE`
- n=`76249` tau_+=`119` o=`75` peak_bits=`19197` word=`OOOEOOOOOEOOOOEOEOOOOOOOOEOOOOOEEEOEEOEOEOEEOOOOOOEEOEOOEEOEOOOOOOOOOEOEEOEEOEEEOEEOEOOOOOOOEOOEOOEEOEEOEOEOOEOEOOEOEOE`
- n=`7847` tau_+=`115` o=`72` peak_bits=`12433` word=`OOOOOOOEEOOOEOOOOOOOOOEEEOOOOEOOEEOEEOOOOOEOEEOOOOOEOOEOOOEOOOOEEEEEEOOOEEOEEOOOOOEOOOOOOEEOOEEEOOOOEOEOOEOEEEEOEEE`

## Record trajectories

- n=`9` tau_+=`5` last_nc=`36` unique_after=`None` peak_bits=`8`
- n=`37` tau_+=`15` last_nc=`76` unique_after=`10` peak_bits=`45`
- n=`49` tau_+=`5` last_nc=`702` unique_after=`None` peak_bits=`13`
- n=`69` tau_+=`7` last_nc=`212` unique_after=`None` peak_bits=`16`
- n=`77` tau_+=`10` last_nc=`482` unique_after=`9` peak_bits=`22`
- n=`173` tau_+=`26` last_nc=`742` unique_after=`12` peak_bits=`272`
- n=`193` tau_+=`70` last_nc=`6498` unique_after=`12` peak_bits=`900`
- n=`557` tau_+=`27` last_nc=`192276` unique_after=`13` peak_bits=`888`
- n=`761` tau_+=`62` last_nc=`115892` unique_after=`11` peak_bits=`851`
- n=`1181` tau_+=`50` last_nc=`2348` unique_after=`13` peak_bits=`150`
- n=`1721` tau_+=`50` last_nc=`3550` unique_after=`12` peak_bits=`419`
- n=`1773` tau_+=`51` last_nc=`222080` unique_after=`11` peak_bits=`312`
- n=`78901` tau_+=`253` last_nc=`84694` unique_after=`None` peak_bits=`1234916`
- n=`34175` tau_+=`183` last_nc=`294704` unique_after=`10` peak_bits=`19297`
- n=`28719` tau_+=`156` last_nc=`388794` unique_after=`14` peak_bits=`12480`
- n=`13325` tau_+=`154` last_nc=`7860112` unique_after=`11` peak_bits=`4223`
- n=`56509` tau_+=`138` last_nc=`656330956` unique_after=`9` peak_bits=`2923`
- n=`83787` tau_+=`138` last_nc=`1363020656` unique_after=`9` peak_bits=`2210`
- n=`15845` tau_+=`132` last_nc=`1435662` unique_after=`11` peak_bits=`79357`
- n=`39947` tau_+=`124` last_nc=`12784074` unique_after=`9` peak_bits=`6529`
- n=`52505` tau_+=`123` last_nc=`72446` unique_after=`None` peak_bits=`15273`
- n=`30717` tau_+=`121` last_nc=`1446756` unique_after=`10` peak_bits=`15684`
- n=`76249` tau_+=`119` last_nc=`864208370` unique_after=`11` peak_bits=`19197`
- n=`7847` tau_+=`115` last_nc=`16772` unique_after=`10` peak_bits=`12433`

## First-passage classes (largest)

- C_`1`,`0` count=`1000` modulus=`2` residues8=`[0, 2, 4, 6]` window=`True`
- C_`2`,`1` count=`494` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`5`,`3` count=`126` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`4`,`2` count=`124` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`8`,`5` count=`54` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`7`,`4` count=`46` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`13`,`8` count=`26` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`10`,`6` count=`19` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`12`,`7` count=`18` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`16`,`10` count=`15` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`
- C_`15`,`9` count=`11` modulus=`2` residues8=`[3, 5, 7]` window=`True`
- C_`18`,`11` count=`11` modulus=`2` residues8=`[1, 3, 5, 7]` window=`True`

## Lean

- `power_bound_word`: `True`
- `power_bound_contracts`: `True`
- `power_bound_eq_iff_extremal`: `True`
- `power_bound_compensated_contracts`: `True`
- new DriftFirstPassage file absent: `True`
- ResidualStep not extended: `True`
- CycleDiophantine not rewritten: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- search_horizon_is_L: `False`
- tau_plus_finite: `False`
- tau_plus_bounded: `False`
- window_empty_is_A_w_empty: `False`
- cardinality_drop_is_named: `False`
- finite_max_is_unbounded_family: `False`
- endpoint_filtration_reopened: `False`

## Decision

**DRIFT_FIRST_PASSAGE_COMPLEX**

nested A_w signatures do not compress below the itineraries themselves; 10 extensions are tautological window subsets and 259 named-thinner hits are residue/modulus artefacts of longer prefixes, not a pruning rule; hunt max tau_+=253 is a larger record, not a structured unbounded family; 1 hunt bit-cap leftovers are not a bound L.

A finite tau_+ on this window is not tau_+ < infinity.
A search-horizon miss is not a bound L.
A window-empty child is not A_w empty.
Do not claim termination.

