# Juggler superquadratic suffixes

Status: **FIRST_E_EVENTUAL_NONCONTRACTION_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Every fixed suffix with
`3^#O(v) > 2^(|v|+1)` has only finitely many first-even contraction
cells. The threshold depends on `v`.

## Branch budget

```text
Mathematical target     For each fixed v with α_v>2, is Q_v finite?
Novelty hypothesis      Coarse 4T^2 bounds compose to a gap 3^o>2^{r+1}
Falsifier               A large contracting q for a fixed superquadratic v
Existing machinery      first_even_freeze, PowerBound (upper only)
Maximum Phase-0 scope   LowerPowerBound; eventual non-contraction
```

## Metadata

- word length: `k <= 5`
- q domain: `q <= 200` (heavy `<= 80`)
- engine control layer modified: `False`
- classification: **FIRST_E_EVENTUAL_NONCONTRACTION_GREEN**
- sorry-free: `True`

each fixed v with 3^#O(v) > 2^(|v|+1) has LowerPowerBound q^{3^o} ≤ D_v T_v(q)^{2^r} and therefore only finitely many first-even contraction cells; no finite itinerary has α_v = 2.

## Superquadratic scans

- `OO` α=`9/4` Q=`[1, 3]` first_expand=`5`
- `OOO` α=`27/8` Q=`[1]` first_expand=`3`
- `OOOO` α=`81/16` Q=`[1]` first_expand=`37`
- `EOOOO` α=`81/32` Q=`[2]` first_expand=`None`
- `OEOOO` α=`81/32` Q=`[]` first_expand=`None`
- `OOEOO` α=`81/32` Q=`[]` first_expand=`69`
- `OOOEO` α=`81/32` Q=`[]` first_expand=`77`
- `OOOOE` α=`81/32` Q=`[]` first_expand=`37`
- `OOOOO` α=`243/32` Q=`[1]` first_expand=`None`

## Lean

- `LowerPowerBound`: `True`
- `lower_growth_word`: `True`
- `eventually_no_first_even_contraction`: `True`
- `alpha_ne_two`: `True`
- `four_mul_floorPower_even_sq`: `True`
- `four_mul_floorPower_odd_sq`: `True`
- `oo_lower_growth_eventual`: `True`
- `oo_suffix_threshold`: `True`
- `ooo_suffix_threshold`: `True`
- `first_even_freeze`: `True`
- `power_bound_compensated_contracts`: `True`
- certificate unchanged: `True`
- `PowerHeight` absent: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**FIRST_E_EVENTUAL_NONCONTRACTION_GREEN**

each fixed v with 3^#O(v) > 2^(|v|+1) has LowerPowerBound q^{3^o} ≤ D_v T_v(q)^{2^r} and therefore only finitely many first-even contraction cells; no finite itinerary has α_v = 2.

This is a fixed-itinerary threshold statement, not a global halt result.

