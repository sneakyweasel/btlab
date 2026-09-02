# Juggler floor-cell geometry

Status: **FIRST_E_FREEZE_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. The first even letter freezes every
suffix on the square-root cell. Odd cells are singletons.

## Branch budget

```text
Mathematical target     Is T_Ev(n)=T_v(⌊√n⌋) reusable, and do
                        positive-drift Ev words have infinitely
                        many contraction cells?
Novelty hypothesis      First-even freeze plus a threshold
                        trichotomy; odd cells are too thin
Falsifier               Freeze fails, or odd cells are wide
Existing machinery      inverse-floor iff, EOO cell threshold
Maximum Phase-0 scope   Generic freeze; recover EOO; Ev scan
```

## Metadata

- q domain: `q <= 80`
- word length: `k <= 6`
- odd-cell m domain: `m <= 500`
- engine control layer modified: `False`
- classification: **FIRST_E_FREEZE_GREEN**
- sorry-free: `True`

T_Ev(n)=T_v(⌊√n⌋) on every square-root cell; odd cells are unique so an initial O does not freeze a range; EOO is the mixed-cell case and EEOOOO is an entire-cell case.

## Primitive cells

- even widths q=1,3,10,100: `{'1': 3, '3': 7, '10': 21, '100': 201}`
- odd cells: empty `437`, singleton `64`, multi `0`

## Freeze checks

- first-even failures: `0`
- first-odd failures: `0`

## Positive-drift first-even cells

- `EOO` starts `[2, 12, 14]` non-expanding cells `[{'q': 1, 'regime': 'mixed', 'output': 1, 'cell': [1, 4], 'starts': [2]}, {'q': 3, 'regime': 'mixed', 'output': 11, 'cell': [9, 16], 'starts': [12, 14]}]`
- `EOOO` starts `[2]` non-expanding cells `[{'q': 1, 'regime': 'mixed', 'output': 1, 'cell': [1, 4], 'starts': [2]}]`
- `EOOOO` starts `[2]` non-expanding cells `[{'q': 1, 'regime': 'mixed', 'output': 1, 'cell': [1, 4], 'starts': [2]}]`
- `EEOOOO` starts `[4, 6, 8]` non-expanding cells `[{'q': 2, 'regime': 'all_contract', 'output': 1, 'cell': [4, 9], 'starts': [4, 6, 8]}]`
- `EOOOOO` starts `[2]` non-expanding cells `[{'q': 1, 'regime': 'mixed', 'output': 1, 'cell': [1, 4], 'starts': [2]}]`

## EEOOOO entire-cell witnesses

- n=`4` q=`2` T^6=`1` regime=`all_contract`
- n=`6` q=`2` T^6=`1` regime=`all_contract`
- n=`8` q=`2` T^6=`1` regime=`all_contract`

## Lean

- `even_preimage_iff`: `True`
- `odd_preimage_iff`: `True`
- `preimage_same_next_state`: `True`
- `iterate_cons_even`: `True`
- `iterate_cons_odd`: `True`
- `first_even_freeze`: `True`
- `first_odd_freeze`: `True`
- `suffix_same_output_on_cell`: `True`
- `first_even_contracts_iff`: `True`
- `eoo_from_first_even`: `True`
- `constant_cell_trichotomy`: `True`
- `odd_preimage_unique`: `True`
- `floorPower_eoo_contracts_iff`: `True`
- `eoo_contracts_on_cell`: `True`
- `power_bound_compensated_contracts`: `True`
- certificate unchanged: `True`
- `PowerHeight` absent: `True`
- no cell tree: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**FIRST_E_FREEZE_GREEN**

T_Ev(n)=T_v(⌊√n⌋) on every square-root cell; odd cells are unique so an initial O does not freeze a range; EOO is the mixed-cell case and EEOOOO is an entire-cell case.

This is a finite-itinerary cell identity, not a global halt result.

