# Juggler cycle ceiling finance

Status: **CEILING_FINANCE_CLOSED**

The upper cell (p+1)^{2^r} as leftover finance.
Not a halt theorem. Not a leftover-itinerary census. No new Lean.

## Metadata

- classification: **CEILING_FINANCE_CLOSED**
- floor: `261`
- leftover L: `84` o=`53` even=`31`
- theta: `0.00208595`
- T(n) even: `True`
- plain height m=3: `0.00219263`
- k=18 landing: p=`3075` r=`10` 6/5 kills=`True`
- k=24 landing: p=`304` r=`14` 6/5=`0.00249536` inv-sum=`0.0121298`
- 6/5 killing p: `659`
- inv-sum killing p: `367`
- slogan false: `True`

the upper cell forces a landing p >= iterated_isqrt(M_min, r), which is a corollary of even_iter_lt_succ_pow, but the adversarial peak run k=24 lands at p=304. Proved 6/5 RHS=0.002495 and Lean inv-sum S=0.012130 both miss θ=0.002086 / need=0.011568. 6/5 needs p>=659; inv-sum needs p>=367. Pigeonhole k=18 lands at 3075 and would kill; the leftover can choose k=24. Large m is worse. Not a leftover-itinerary census and not a floor raise.

## Exact peak-run landings at n=261, m=3

- k=`18` r=`10` p=`3075` bits=`11865` const1=`0.00154458` 6/5=`0.00185349` inv=`0.00916549` 6/5 kills=`True` inv kills=`True`
- k=`19` r=`11` p=`412` bits=`17797` const1=`0.0019072` 6/5=`0.00228864` inv=`0.0112675` 6/5 kills=`False` inv kills=`True`
- k=`20` r=`11` p=`8391` bits=`26696` const1=`0.00151728` 6/5=`0.00182073` inv=`0.00895947` 6/5 kills=`True` inv kills=`True`
- k=`21` r=`12` p=`876` bits=`40043` const1=`0.00167257` 6/5=`0.00200708` inv=`0.00998184` 6/5 kills=`True` inv kills=`True`
- k=`22` r=`12` p=`25961` bits=`60065` const1=`0.00150787` 6/5=`0.00180945` inv=`0.00887881` 6/5 kills=`True` inv kills=`True`
- k=`23` r=`13` p=`2045` bits=`90097` const1=`0.00156823` 6/5=`0.00188188` inv=`0.00932929` 6/5 kills=`True` inv kills=`True`
- k=`24` r=`14` p=`304` bits=`135145` const1=`0.00207947` 6/5=`0.00249536` inv=`0.0121298` 6/5 kills=`False` inv kills=`False`

## Pigeonhole m-table (k = ceil(53/m) only)

- m=`3` kmin=`18` r=`10` p=`3075` 6/5 kills=`True` inv kills=`True`
- m=`4` kmin=`14` r=`8` p=`569` 6/5 kills=`False` inv kills=`False`
- m=`5` kmin=`11` r=`6` p=`1845` 6/5 kills=`False` inv kills=`False`
- m=`6` kmin=`9` r=`5` p=`800` 6/5 kills=`False` inv kills=`False`
- m=`7` kmin=`8` r=`4` p=`7430` 6/5 kills=`False` inv kills=`False`
- m=`8` kmin=`7` r=`4` p=`380` 6/5 kills=`False` inv kills=`False`
- m=`9` kmin=`6` r=`3` p=`2760` 6/5 kills=`False` inv kills=`False`
- m=`10` kmin=`6` r=`3` p=`2760` 6/5 kills=`False` inv kills=`False`
- m=`11` kmin=`5` r=`2` p=`38716` 6/5 kills=`False` inv kills=`False`
- m=`12` kmin=`5` r=`2` p=`38716` 6/5 kills=`False` inv kills=`False`
- m=`13` kmin=`5` r=`2` p=`38716` 6/5 kills=`False` inv kills=`False`
- m=`14` kmin=`4` r=`2` p=`1144` 6/5 kills=`False` inv kills=`False`
- m=`15` kmin=`4` r=`2` p=`1144` 6/5 kills=`False` inv kills=`False`
- m=`16` kmin=`4` r=`2` p=`1144` 6/5 kills=`False` inv kills=`False`
- m=`17` kmin=`4` r=`2` p=`1144` 6/5 kills=`False` inv kills=`False`
- m=`18` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`19` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`20` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`21` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`22` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`23` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`24` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`25` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`26` kmin=`3` r=`1` p=`11970` 6/5 kills=`False` inv kills=`False`
- m=`27` kmin=`2` r=`1` p=`523` 6/5 kills=`False` inv kills=`False`
- m=`28` kmin=`2` r=`1` p=`523` 6/5 kills=`False` inv kills=`False`
- m=`29` kmin=`2` r=`1` p=`523` 6/5 kills=`False` inv kills=`False`
- m=`30` kmin=`2` r=`1` p=`523` 6/5 kills=`False` inv kills=`False`
- m=`31` kmin=`2` r=`1` p=`523` 6/5 kills=`False` inv kills=`False`

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
- peak_finance_reopened: `False`

## Decision

**CEILING_FINANCE_CLOSED**

the upper cell forces a landing p >= iterated_isqrt(M_min, r), which is a corollary of even_iter_lt_succ_pow, but the adversarial peak run k=24 lands at p=304. Proved 6/5 RHS=0.002495 and Lean inv-sum S=0.012130 both miss θ=0.002086 / need=0.011568. 6/5 needs p>=659; inv-sum needs p>=367. Pigeonhole k=18 lands at 3075 and would kill; the leftover can choose k=24. Large m is worse. Not a leftover-itinerary census and not a floor raise.

