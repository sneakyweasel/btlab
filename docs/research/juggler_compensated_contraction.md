# Juggler defect-compensated contraction

Status: **COMPENSATED_CONTRACTION_FOUND**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Formal drift `3^o > 2^k` is not a
complete predictor of block direction.

## Branch budget

```text
Mathematical target     Can a mixed itinerary with 3^o > 2^k still
                        contract because floor defect overcomes
                        the formal gap?
Novelty hypothesis      A shortest mixed positive-drift family
                        contracts, or the family is obstructed
Falsifier               No contraction and no obstruction, or a
                        first-defect certificate that never fires
Existing machinery      PowerBound, powerDeficit, localDefect,
                        first-defect sharpness
Maximum Phase-0 scope   Search OOE/OEO/EOO; first-defect vs G;
                        Lean certificate or EOO obstruction
```

## Metadata

- OOE/OEO domain: `n <= 20000` odd
- EOO domain: even `n <= 200000`
- length-4 mixed domain: `n <= 10000`
- engine control layer modified: `False`
- classification: **COMPENSATED_CONTRACTION_FOUND**
- sorry-free: `True`

EOO contracts exactly at n ∈ {2, 12, 14}; the first-defect bound is never enough for (k,o)=(3,2), so compensation uses the full envelope deficit.

## Length-3 mixed positive-drift words

These words have two odd letters, so `3^2 = 9 > 8 = 2^3`.

- `OOE`: realized `2476`, contractions `0`, first-defect certificates `0`
- `OEO`: realized `2495`, contractions `0`, first-defect certificates `0`
- `EOO`: realized `22888`, contractions `3`, first-defect certificates `0`

## EOO witnesses

- n=`2` → T^3=`1`; δ=`1`; G=`256`; Δ=`511`
- n=`12` → T^3=`11`; δ=`3`; G=`4729798656`; Δ=`4945421471`
- n=`14` → T^3=`11`; δ=`5`; G=`19185257728`; Δ=`20446687903`

n=10 also realizes `EOO` but expands: T^3=`11`.

## Lean

- `power_bound_compensated_contracts`: `True`
- `power_bound_compensated_contracts_follows`: `True`
- `floorPower_eoo_contracts_iff`: `True`
- `floorPower_eoo_two_contracts`: `True`
- `floorPower_eoo_twelve_contracts`: `True`
- `floorPower_eoo_fourteen_contracts`: `True`
- `eoo_first_defect_lt_formal_gap`: `True`
- `floorPower_eoo_two_deficit_gt_gap`: `True`
- `follows_eoo_two`: `True`
- `follows_eoo_twelve`: `True`
- `follows_eoo_fourteen`: `True`
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

**COMPENSATED_CONTRACTION_FOUND**

EOO contracts exactly at n ∈ {2, 12, 14}; the first-defect bound is never enough for (k,o)=(3,2), so compensation uses the full envelope deficit.

This is a finite-itinerary direction statement, not a global halt result.

