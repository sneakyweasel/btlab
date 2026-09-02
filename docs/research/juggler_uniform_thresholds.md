# Juggler uniform superquadratic thresholds

Status: **CHANGING_SUFFIX_COUNTEREXAMPLE**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. A threshold depending only on the
exponent margin `α_v-2` does not exist.

## Branch budget

```text
Mathematical target     Does Q(ε) exist for all α_v ≥ 2+ε?
Novelty hypothesis      Margin above 2 might give a family bound
Falsifier               Superquadratic v_q with unbounded contracting q
Existing machinery      LowerPowerBound; first_even_freeze
Maximum Phase-0 scope   q_max vs ε; D_v audit; even-tower family
```

## Metadata

- short-word length: `k <= 6`
- short-word q domain: `q <= 80`
- engine control layer modified: `False`
- classification: **CHANGING_SUFFIX_COUNTEREXAMPLE**
- sorry-free: `True`

the family E^k O^{3k} at q=2^{2^{k-1}} is superquadratic, maps onto 1, and contracts for arbitrarily large q; no Q(ε) exists.

## Collapse family `E^k O^{3k}`

- k=`2` v=`EEOOOOOO` α=`729/256` q=`4` T=`1` contracts=`True`
- k=`3` v=`EEEOOOOOOOOO` α=`19683/4096` q=`16` T=`1` contracts=`True`
- k=`4` v=`EEEEOOOOOOOOOOOO` α=`531441/65536` q=`256` T=`1` contracts=`True`
- k=`5` v=`EEEEEOOOOOOOOOOOOOOO` α=`14348907/1048576` q=`65536` T=`1` contracts=`True`

## Short-word `q_max` by margin

- `OO` ε=`1/4` q_max=`3`
- `EOOOO` ε=`17/32` q_max=`2`
- `OEOOO` ε=`17/32` q_max=`None`
- `OOEOO` ε=`17/32` q_max=`None`
- `OOOEO` ε=`17/32` q_max=`None`
- `OOOOE` ε=`17/32` q_max=`None`
- `OOO` ε=`11/8` q_max=`1`
- `EOOOOO` ε=`115/64` q_max=`2`
- `OEOOOO` ε=`115/64` q_max=`None`
- `OOEOOO` ε=`115/64` q_max=`None`
- `OOOEOO` ε=`115/64` q_max=`None`
- `OOOOEO` ε=`115/64` q_max=`None`
- `OOOOOE` ε=`115/64` q_max=`None`
- `OOOO` ε=`49/16` q_max=`1`
- `OOOOO` ε=`179/32` q_max=`1`
- `OOOOOO` ε=`601/64` q_max=`1`

## `D_v` order audit for `(r,o)=(5,4)`

- `EOOOO` D bit-length=`423`
- `OEOOO` D bit-length=`315`
- `OOEOO` D bit-length=`243`
- `OOOEO` D bit-length=`195`
- `OOOOE` D bit-length=`163`

## Minimal positive margin by length

- r=`1` none
- r=`2` o=`2` ε_r=`1/4`
- r=`3` o=`3` ε_r=`11/8`
- r=`4` o=`4` ε_r=`49/16`
- r=`5` o=`4` ε_r=`17/32`
- r=`6` o=`5` ε_r=`115/64`
- r=`7` o=`6` ε_r=`473/128`
- r=`8` o=`6` ε_r=`217/256`
- r=`9` o=`7` ε_r=`1163/512`
- r=`10` o=`7` ε_r=`139/1024`
- r=`11` o=`8` ε_r=`2465/2048`
- r=`12` o=`9` ε_r=`11491/4096`

## Lean

- `alphaMargin`: `True`
- `minimal_superquadratic_margin`: `True`
- `even_tower_to_one`: `True`
- `even_tower_odd_tail_contracts`: `True`
- `three_k_superquadratic`: `True`
- `changing_suffix_unbounded_contraction`: `True`
- `LowerPowerBound`: `True`
- `lower_growth_word`: `True`
- `eventually_no_first_even_contraction`: `True`
- `alpha_ne_two`: `True`
- `first_even_contracts_iff`: `True`
- `first_even_freeze`: `True`
- certificate unchanged: `True`
- `PowerHeight` absent: `True`
- no `uniform_first_even_threshold`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**CHANGING_SUFFIX_COUNTEREXAMPLE**

the family E^k O^{3k} at q=2^{2^{k-1}} is superquadratic, maps onto 1, and contracts for arbitrarily large q; no Q(ε) exists.

The fixed-itinerary theorem remains. This is not a halt result.

