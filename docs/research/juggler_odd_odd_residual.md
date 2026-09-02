# Juggler odd-odd residual admissibility

Status: **ODD_ODD_RESIDUAL_COMPLEX**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. A residual step is one realized
`O^a E^b` excursion. The question is whether another
non-extremal odd-odd step stays finitely admissible.

## Branch budget

```text
Mathematical target     Can a non-extremal ResidualStep chain remain
                        arithmetically admissible indefinitely?
Novelty hypothesis      successor constraints tighten until no next step exists
Falsifier               every proposed I(S) dies; ResidualStep rewritten
Existing machinery      ResidualStep, residual_excursion, localDefect, is_odd_odd
Maximum Phase-0 scope   HARD_PROBES + odd-odd n<=80; admissibility first
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **ODD_ODD_RESIDUAL_COMPLEX**
- secondary: `['ODD_ODD_COUNTEREXAMPLE']`
- sorry-free: `True`
- algorithm: `odd-odd-residual-v1`

no jointly necessary recursively preserved obstruction; killed ['y>x', 'interval tightening', 'valuation monotonicity', 'exact O^k towers as the branch']; max non-extremal odd-odd depth 2 is a search-horizon count, not L.

## Window

- odd-odd starts: `18`
- first exact odd prefixes: `0`
- first non-extremal: `18`
- first lands odd-odd: `4`
- max odd-odd depth: `2` (horizon, not L)
- max non-extremal odd-odd depth: `2`
- interval tightens always: `False`
- v2 monotone: `False`
- v3 monotone: `False`
- smallest y<x odd-odd step: `{'x': 53, 'y': 9}`
- smallest persist-then-descent: `{'x': 69, 'mid': 117, 'y': 3}`

## Hard residual traces

### n = 9

- x=`9` O^2E^1 z=`140` y=`11` exact=`False` nonextremal=`True` y_odd_odd=`False` y_gt_x=`True` another=`False`
- full residual chain:
  - x=`9` O^2E^1 y=`11` kind=`STAY_AUTO_FP` y_odd_odd=`False`
  - x=`11` O^1E^3 y=`1` kind=`CAPTURE` y_odd_odd=`False`

### n = 37

- x=`37` O^4E^1 z=`86818724` y=`9317` exact=`False` nonextremal=`True` y_odd_odd=`True` y_gt_x=`True` another=`True`
- x=`9317` O^3E^2 z=`24906114455136` y=`2233` exact=`False` nonextremal=`True` y_odd_odd=`True` y_gt_x=`False` another=`False`
- x=`2233` O^2E^5 z=`34276462` y=`1` exact=`False` nonextremal=`True` y_odd_odd=`False` y_gt_x=`False` another=`False`
- full residual chain:
  - x=`37` O^4E^1 y=`9317` kind=`PERSISTENT_ODD_ODD` y_odd_odd=`True`
  - x=`9317` O^3E^2 y=`2233` kind=`PERSISTENT_ODD_ODD` y_odd_odd=`True`
  - x=`2233` O^2E^5 y=`1` kind=`CAPTURE` y_odd_odd=`False`

### n = 49

- x=`49` O^2E^1 z=`6352` y=`79` exact=`False` nonextremal=`True` y_odd_odd=`False` y_gt_x=`True` another=`True`
- full residual chain:
  - x=`49` O^2E^1 y=`79` kind=`STAY_AUTO_FP` y_odd_odd=`False`
  - x=`79` O^1E^2 y=`5` kind=`RETURN_BELOW` y_odd_odd=`True`

### n = 69

- x=`69` O^2E^1 z=`13716` y=`117` exact=`False` nonextremal=`True` y_odd_odd=`True` y_gt_x=`True` another=`True`
- x=`117` O^2E^3 z=`44992` y=`3` exact=`False` nonextremal=`True` y_odd_odd=`True` y_gt_x=`False` another=`False`
- x=`3` O^3E^3 z=`36` y=`1` exact=`False` nonextremal=`True` y_odd_odd=`False` y_gt_x=`False` another=`False`
- full residual chain:
  - x=`69` O^2E^1 y=`117` kind=`PERSISTENT_ODD_ODD` y_odd_odd=`True`
  - x=`117` O^2E^3 y=`3` kind=`RETURN_BELOW` y_odd_odd=`True`

### n = 77

- x=`77` O^3E^1 z=`2322378` y=`1523` exact=`False` nonextremal=`True` y_odd_odd=`False` y_gt_x=`True` another=`True`
- full residual chain:
  - x=`77` O^3E^1 y=`1523` kind=`STAY_AUTO_FP` y_odd_odd=`False`
  - x=`1523` O^1E^1 y=`243` kind=`PERSISTENT_ODD_ODD` y_odd_odd=`True`
  - x=`243` O^2E^2 y=`21` kind=`RETURN_BELOW` y_odd_odd=`False`

## Lean

- `ResidualStep`: `True`
- `PersistentOddResidual`: `True`
- new OddOddResidual file absent: `True`
- CycleItinerary not rewritten: `True`
- CycleDiophantine not rewritten: `True`
- FloorPower not rewritten: `True`
- no forbidden engine: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- finite_progress_for_all: `False`
- uniform_residual_horizon: `False`
- odd_odd_chains_bounded: `False`
- scalar_must_grow: `False`
- search_horizon_is_L: `False`

## Decision

**ODD_ODD_RESIDUAL_COMPLEX**

no jointly necessary recursively preserved obstruction; killed ['y>x', 'interval tightening', 'valuation monotonicity', 'exact O^k towers as the branch']; max non-extremal odd-odd depth 2 is a search-horizon count, not L.

This is not a halt result. A search-horizon depth is not a
bound L. ResidualStep is not replaced.

