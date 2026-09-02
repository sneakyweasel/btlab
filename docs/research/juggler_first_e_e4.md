# Juggler first-E transport at four evens

Status: **FIRST_E_E4_REPARAMETERIZATION**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Four-even leftovers only; not a
length-8/9 census and not a four-even bunched-tail programme.

## Branch budget

```text
Mathematical target     Do leftover CycleMins with e=4 even
                        letters die by first-E transport of
                        an excluded three-even family?
Novelty hypothesis      A new infinite e=4 layer, not e=3 again
Falsifier               Gapped last-cluster is Theorem 3.13;
                        long-a1 bunched remainder is 3.14-3.20
                        at y; a large class has short gaps
Existing machinery      two-even tail; first-E; bunched Z;
                        CycleMin y>=n
Maximum Phase-0 scope   Classify expanding e=4 leftovers;
                        no Lean, no census, no Paper A
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **FIRST_E_E4_REPARAMETERIZATION**
- sorry-free: `True`
- leftover count: `1185`
- class counts: `{'gapped_last_cluster': 570, 'short_bunched_remainder': 160, 'leading_OE': 70, 'leading_even': 70, 'bunched_remainder': 315}`
- remainder count: `300`
- remainder shapes: `30`
- first bunched remainder odd-count: `8`
- Z monotone: `True`

gapped last-cluster is Theorem 3.13 on the last two-even suffix; long-a1 bunched remainder is the existing bunched tail at y after y>=n tightens Z(n)<=Z(y); 30 short-first-gap shapes remain; not a new e=4 theorem.

## Examples

- gapped last-cluster: `OOEEOOOOEE`
- bunched remainder: `OOEOOOOOOEEE`
- leading even: `OOOOOOOEEEE`
- leading OE: `OOOOOOEOEEE`
- short bunched remainder: `OOEOOOOOEEE`

## Lean

- `CycleMin`: `True`
- `no_cycleMin_gapped_three_even_ee`: `True`
- `no_cycleMin_gapped_three_even_eoe`: `True`
- `no_cycle_itinerary_gapped_three_even_ee`: `True`
- `no_cycle_itinerary_three_even_eee`: `True`
- `no_cycle_itinerary_three_even_eoee`: `True`
- `no_cycle_itinerary_three_even_eooee`: `True`
- `no_cycle_itinerary_three_even_eoooee`: `True`
- `no_cycle_itinerary_three_even_eeoe`: `True`
- `no_cycle_itinerary_three_even_eoeoe`: `True`
- `no_cycle_itinerary_three_even_eooeoe`: `True`
- no four-even theorem: `True`
- no first-E e=4 theorem: `True`
- length eight open in census: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- three_even_cycles_impossible: `False`
- four_even_cycles_impossible: `False`
- length_eight_census: `False`
- length_nine_census: `False`
- first_e_e4_lean: `False`
- four_even_bunched_attack: `False`
- induction_on_period: `False`
- induction_on_n: `False`

## Decision

**FIRST_E_E4_REPARAMETERIZATION**

gapped last-cluster is Theorem 3.13 on the last two-even suffix; long-a1 bunched remainder is the existing bunched tail at y after y>=n tightens Z(n)<=Z(y); 30 short-first-gap shapes remain; not a new e=4 theorem.

This is not a halt result and not a length-8/9 census.

