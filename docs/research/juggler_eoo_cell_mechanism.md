# Juggler EOO square-root cell mechanism

Status: **EOO_CELL_MECHANISM_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. The first even step freezes the remaining
`OO` computation on the square-root cell `[q^2, (q+1)^2)`.

## Branch budget

```text
Mathematical target     Why does EOO contract exactly at 2, 12, 14?
Novelty hypothesis      Cell constancy plus the threshold n > c(q)
Falsifier               Output varies on a cell, or n>c fails
Existing machinery      PowerBound, floorPower_eoo_contracts_iff
Maximum Phase-0 scope   EOO cells; OOE/OEO contrast; length-4 scan
```

## Metadata

- odd-q cell domain: `q <= 80`
- length-4 domain: `n <= 20000`
- engine control layer modified: `False`
- classification: **EOO_CELL_MECHANISM_GREEN**
- sorry-free: `True`

EOO contracts exactly on the cells q=1,3 by the threshold n > c(q); q≥5 has c(q) ≥ (q+1)^2. The same first-even freeze appears for EOOO, but only n=2 meets the threshold.

## EOO cells

- constancy failures: `0`
- threshold failures: `0`
- contracting starts: `[2, 12, 14]`

- q=`1` cell=`[1, 4]` c=`1` realized=`[2]` contracts=`[2]` c < (q+1)^2: `True`
- q=`3` cell=`[9, 16]` c=`11` realized=`[10, 12, 14]` contracts=`[12, 14]` c < (q+1)^2: `True`
- q=`5` cell=`[25, 36]` c=`36` realized=`[26, 28, 30, 32, 34]` contracts=`[]` c < (q+1)^2: `False`
- q=`7` cell=`[49, 64]` c=`76` realized=`[]` contracts=`[]` c < (q+1)^2: `False`
- q=`9` cell=`[81, 100]` c=`140` realized=`[82, 84, 86, 88, 90, 92, 94, 96, 98]` contracts=`[]` c < (q+1)^2: `False`

## Witness table

- n=`2` q=`1` r=`1` T(q)=`1` T^3=`1` Δ=`511` G=`256` contracts=`True`
- n=`10` q=`3` r=`1` T(q)=`5` T^3=`11` Δ=`785641119` G=`900000000` contracts=`False`
- n=`12` q=`3` r=`3` T(q)=`5` T^3=`11` Δ=`4945421471` G=`4729798656` contracts=`True`
- n=`14` q=`3` r=`5` T(q)=`5` T^3=`11` Δ=`20446687903` G=`19185257728` contracts=`True`

## OOE / OEO on n-sqrt cells

- `OOE`: varying `76`, constant `0`
- `OEO`: varying `72`, constant `1`

The first letter is odd, so T(n) = ⌊n^{3/2}⌋ varies inside the
n-sqrt cell. EOO is special because the first even step freezes
the remaining word.

## Length-4 mixed o=3

- `EOOO` first-even constancy failures: `0`
- `EOOO` contracting starts: `[2]`

- `OOOE`: realized `1237`, contractions `0`
- `OOEO`: realized `1251`, contractions `0`
- `OEOO`: realized `1276`, contractions `0`
- `EOOO`: realized `1043`, contractions `1`

## Lean

- `sqrt_preimage_iff`: `True`
- `follows_eoo_sqrt_iff`: `True`
- `eoo_output_eq_preimage`: `True`
- `eoo_output_constant_on_sqrt_preimage`: `True`
- `eoo_contracts_on_preimage`: `True`
- `eoo_preimage_output_one`: `True`
- `eoo_preimage_output_three`: `True`
- `eoo_preimage_output_ge_succ_sq`: `True`
- `floorPower_eoo_contracts_iff`: `True`
- `power_bound_compensated_contracts`: `True`
- `eooCellOutput` present: `True`
- certificate unchanged: `True`
- `PowerHeight` absent: `True`
- `mixed_word_power_lt` absent: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**EOO_CELL_MECHANISM_GREEN**

EOO contracts exactly on the cells q=1,3 by the threshold n > c(q); q≥5 has c(q) ≥ (q+1)^2. The same first-even freeze appears for EOOO, but only n=2 meets the threshold.

This is a finite-itinerary cell classification, not a global halt result.

