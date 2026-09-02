# Juggler cycle second-valley bound

Status: **SECOND_VALLEY_CLOSED**

Does CycleMin force the other valleys to sit at ≥ 281?
Not a halt theorem. Not a leftover-itinerary census. No new Lean.

## Metadata

- classification: **SECOND_VALLEY_CLOSED**
- floor: `261`
- leftover L: `84` o=`53` even=`31`
- theta: `0.00208595`
- height-split killing n2: `281`
- worst first-circuit odd landing: k=`12` p=`281`
- from 281: k=`12` p=`303`
- k=24 raw landing: p=`304` even=`True` odd p=`92495`
- k=1 OE witness: v=`1687` T=`69290` p=`263`
- 6/5 killing n2: `369`
- adversarial valleys: `[261, 281, 303]`
- adversarial const 1: `0.00202432` kills=`True`
- adversarial 6/5: `0.00242918` kills=`False`
- adversarial inv-sum: `0.0118679` kills=`False`
- OE triple: `[261, 263, 1687]` 6/5 kills=`True` inv kills=`True`
- all-281 const 1: `0.00207787` kills=`True`
- all-281 inv-sum: `0.0121263` kills=`False`
- slogan false: `True`

height-split const 1 first kills at n2=281, but that form is not proved. Lean inv-sum still misses when both others sit at 281 (S=0.012126 > 0.011568). The adversarial Lean-allowed triple is [261, 281, 303] (first circuit k=12 lands at 281; from 281, k=12 lands at 303). Height 6/5 RHS=0.002429 and inv-sum S=0.011868 both miss θ=0.002086 / need=0.011568; 6/5 first kills at 369. A later OE landing at 263 requires a start valley ≥ 1687 and that triple dies. The 281 landing is even_iter_lt_succ_pow. Not a leftover-itinerary census and not a floor raise

## First-circuit odd landings at n=261

- k=`2` r=`1` p_raw=`523` even=`False` r_odd=`1` p_odd=`523` feasible=`True`
- k=`3` r=`1` p_raw=`11970` even=`True` r_odd=`0` p_odd=`261` feasible=`False`
- k=`4` r=`2` p_raw=`1144` even=`True` r_odd=`1` p_odd=`1309763` feasible=`True`
- k=`5` r=`2` p_raw=`38716` even=`True` r_odd=`0` p_odd=`261` feasible=`False`
- k=`6` r=`3` p_raw=`2760` even=`True` r_odd=`1` p_odd=`58034208680743` feasible=`True`
- k=`7` r=`4` p_raw=`380` even=`True` r_odd=`0` p_odd=`261` feasible=`False`
- k=`8` r=`4` p_raw=`7430` even=`True` r_odd=`3` p_odd=`55216933` feasible=`True`
- k=`9` r=`5` p_raw=`800` even=`True` r_odd=`4` p_odd=`640551` feasible=`True`
- k=`10` r=`5` p_raw=`22642` even=`True` r_odd=`4` p_odd=`512662231` feasible=`True`
- k=`11` r=`6` p_raw=`1845` even=`False` r_odd=`6` p_odd=`1845` feasible=`True`
- k=`12` r=`7` p_raw=`281` even=`False` r_odd=`7` p_odd=`281` feasible=`True`
- k=`13` r=`7` p_raw=`4725` even=`False` r_odd=`7` p_odd=`4725` feasible=`True`
- k=`14` r=`8` p_raw=`569` even=`False` r_odd=`8` p_odd=`569` feasible=`True`
- k=`15` r=`8` p_raw=`13607` even=`False` r_odd=`8` p_odd=`13607` feasible=`True`
- k=`16` r=`9` p_raw=`1259` even=`False` r_odd=`9` p_odd=`1259` feasible=`True`
- k=`17` r=`9` p_raw=`44718` even=`True` r_odd=`7` p_odd=`3999025781181682619` feasible=`True`
- k=`18` r=`10` p_raw=`3075` even=`False` r_odd=`10` p_odd=`3075` feasible=`True`
- k=`19` r=`11` p_raw=`412` even=`True` r_odd=`10` p_odd=`170529` feasible=`True`
- k=`20` r=`11` p_raw=`8391` even=`False` r_odd=`11` p_odd=`8391` feasible=`True`
- k=`21` r=`12` p_raw=`876` even=`True` r_odd=`11` p_odd=`768731` feasible=`True`
- k=`22` r=`12` p_raw=`25961` even=`False` r_odd=`12` p_odd=`25961` feasible=`True`
- k=`23` r=`13` p_raw=`2045` even=`False` r_odd=`13` p_odd=`2045` feasible=`True`
- k=`24` r=`14` p_raw=`304` even=`True` r_odd=`13` p_odd=`92495` feasible=`True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- halt_theorem: `False`
- no_cycle_all_lengths: `False`
- new_lean: `False`
- floor_raise: `False`
- leftover_word_census: `False`

## Decision

**SECOND_VALLEY_CLOSED**

height-split const 1 first kills at n2=281, but that form is not proved. Lean inv-sum still misses when both others sit at 281 (S=0.012126 > 0.011568). The adversarial Lean-allowed triple is [261, 281, 303] (first circuit k=12 lands at 281; from 281, k=12 lands at 303). Height 6/5 RHS=0.002429 and inv-sum S=0.011868 both miss θ=0.002086 / need=0.011568; 6/5 first kills at 369. A later OE landing at 263 requires a start valley ≥ 1687 and that triple dies. The 281 landing is even_iter_lt_succ_pow. Not a leftover-itinerary census and not a floor raise

