# Juggler first-even thresholds

Status: **FIRST_E_FINITE_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Q_v is the set of realized q with
`T_v(q) + 1 < (q+1)^2`.

## Branch budget

```text
Mathematical target     For α_v > 2, is Q_v finite?
Novelty hypothesis      OO and OOO have eventual thresholds
Falsifier               Large Q_v for OO/OOO, or a mono break
Existing machinery      first_even_freeze, eoo_cell_output_ge_succ_sq
Maximum Phase-0 scope   Cell-interval API; Q_v for short suffixes
```

## Metadata

- q domain: `q <= 120`
- engine control layer modified: `False`
- classification: **FIRST_E_FINITE_GREEN**
- sorry-free: `True`

Q_OO = {1,3} and Q_OOO = {1} with Lean eventual thresholds; Q_O is all realized odd q because α=3/2<2, which is formal contraction of EO, not compensated positive drift.

Exact any-contraction: `any contraction on [q^2,(q+1)^2) is c+1 < (q+1)^2, not merely c < (q+1)^2`.

## Suffix scans

- `O` α=`3/2` drift>2=`False` Q=`[1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 119]` Q_all=`[3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97, 99, 101, 103, 105, 107, 109, 111, 113, 115, 117, 119]` first_expand=`None` mono_breaks=`0`
- `OO` α=`9/4` drift>2=`True` Q=`[1, 3]` Q_all=`[]` first_expand=`5` mono_breaks=`0`
- `OOO` α=`27/8` drift>2=`True` Q=`[1]` Q_all=`[]` first_expand=`3` mono_breaks=`0`
- `EO` α=`3/4` drift>2=`False` Q=`[2, 10, 12, 14, 26, 28, 30, 32, 34, 50, 52, 54, 56, 58, 60, 62, 82, 84, 86, 88, 90, 92, 94, 96, 98]` Q_all=`[2, 10, 12, 14, 26, 28, 30, 32, 34, 50, 52, 54, 56, 58, 60, 62, 82, 84, 86, 88, 90, 92, 94, 96, 98]` first_expand=`None` mono_breaks=`0`
- `EOO` α=`9/8` drift>2=`False` Q=`[2, 10, 12, 14, 26, 28, 30, 32, 34, 82, 84, 86, 88, 90, 92, 94, 96, 98]` Q_all=`[2, 10, 12, 14, 26, 28, 30, 32, 34, 82, 84, 86, 88, 90, 92, 94, 96, 98]` first_expand=`None` mono_breaks=`0`
- `EOOO` α=`27/16` drift>2=`False` Q=`[2, 10, 12, 14]` Q_all=`[2, 10, 12, 14]` first_expand=`None` mono_breaks=`0`
- `EOOOO` α=`81/32` drift>2=`True` Q=`[2]` Q_all=`[2]` first_expand=`None` mono_breaks=`0`
- `OOOO` α=`81/16` drift>2=`True` Q=`[1]` Q_all=`[]` first_expand=`37` mono_breaks=`0`

## Lean

- `cell_any_contracts_iff`: `True`
- `cell_all_contracts_iff`: `True`
- `first_even_any_contracts_iff`: `True`
- `first_even_all_contracts_iff`: `True`
- `first_even_contracts_iff`: `True`
- `oo_suffix_threshold`: `True`
- `ooo_suffix_threshold`: `True`
- `floorPower_odd_ge`: `True`
- `eoo_cell_output_ge_succ_sq`: `True`
- `floorPower_eoo_contracts_iff`: `True`
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

**FIRST_E_FINITE_GREEN**

Q_OO = {1,3} and Q_OOO = {1} with Lean eventual thresholds; Q_O is all realized odd q because α=3/2<2, which is formal contraction of EO, not compensated positive drift.

This is a finite-itinerary threshold statement, not a global halt result.

