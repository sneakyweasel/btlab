# Juggler first-E transport of the two-even tail

Status: **FIRST_E_TRANSPORT_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Gapped three-even CycleMins
only; not a length-8/9 census and not a bunched-tail attack.

## Branch budget

```text
Mathematical target     Do gapped three-even CycleMins die
                        by first-E transport of the two-even
                        tail?
Novelty hypothesis      y>=n tightens the leftover cell
Falsifier               A CycleMin hit, or a k>=17 leak
Existing machinery      uniform two-even Lean; CycleMin
Maximum Phase-1 scope   Lean CycleMin exclusion; tables;
                        seven-odd; no census, no bunched
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **FIRST_E_TRANSPORT_GREEN**
- sorry-free: `True`
- finite gapped words k=9..16: `72`
- tables empty: `True`
- k>=17 small-n sealed: `True`

Lean excludes gapped three-even CycleMins by first-E transport of the two-even tail at y>=n; the finite window k=9..16 has empty CycleItinerary tables below 256; for k>=17 small n is seven-odd on the prefix or the remainder; bunched a1-short leftovers remain.

## Length-9 transport words

- `OOEOOOOEE`
- `OOEOOOEOE`

## Bunched remainder at each k

- k=`9` gapped=`2` bunched=`7` ee=`['OOOEOOOEE', 'OOOOEOOEE', 'OOOOOEOEE', 'OOOOOOEEE']` eoe=`['OOOEOOEOE', 'OOOOEOEOE', 'OOOOOEEOE']`
- k=`10` gapped=`4` bunched=`7` ee=`['OOOOEOOOEE', 'OOOOOEOOEE', 'OOOOOOEOEE', 'OOOOOOOEEE']` eoe=`['OOOOEOOEOE', 'OOOOOEOEOE', 'OOOOOOEEOE']`
- k=`11` gapped=`6` bunched=`7` ee=`['OOOOOEOOOEE', 'OOOOOOEOOEE', 'OOOOOOOEOEE', 'OOOOOOOOEEE']` eoe=`['OOOOOEOOEOE', 'OOOOOOEOEOE', 'OOOOOOOEEOE']`
- k=`12` gapped=`8` bunched=`7` ee=`['OOOOOOEOOOEE', 'OOOOOOOEOOEE', 'OOOOOOOOEOEE', 'OOOOOOOOOEEE']` eoe=`['OOOOOOEOOEOE', 'OOOOOOOEOEOE', 'OOOOOOOOEEOE']`
- k=`13` gapped=`10` bunched=`7` ee=`['OOOOOOOEOOOEE', 'OOOOOOOOEOOEE', 'OOOOOOOOOEOEE', 'OOOOOOOOOOEEE']` eoe=`['OOOOOOOEOOEOE', 'OOOOOOOOEOEOE', 'OOOOOOOOOEEOE']`
- k=`14` gapped=`12` bunched=`7` ee=`['OOOOOOOOEOOOEE', 'OOOOOOOOOEOOEE', 'OOOOOOOOOOEOEE', 'OOOOOOOOOOOEEE']` eoe=`['OOOOOOOOEOOEOE', 'OOOOOOOOOEOEOE', 'OOOOOOOOOOEEOE']`
- k=`15` gapped=`14` bunched=`7` ee=`['OOOOOOOOOEOOOEE', 'OOOOOOOOOOEOOEE', 'OOOOOOOOOOOEOEE', 'OOOOOOOOOOOOEEE']` eoe=`['OOOOOOOOOEOOEOE', 'OOOOOOOOOOEOEOE', 'OOOOOOOOOOOEEOE']`
- k=`16` gapped=`16` bunched=`7` ee=`['OOOOOOOOOOEOOOEE', 'OOOOOOOOOOOEOOEE', 'OOOOOOOOOOOOEOEE', 'OOOOOOOOOOOOOEEE']` eoe=`['OOOOOOOOOOEOOEOE', 'OOOOOOOOOOOEOEOE', 'OOOOOOOOOOOOEEOE']`

## Lean

- `CycleMin`: `True`
- `cycleMin_ge`: `True`
- `cycle_trailing_evens_lt`: `True`
- `shared_two_even_tail`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycle_itinerary_two_even_eoe`: `True`
- `no_cycleMin_internal_even_threshold`: `True`
- `no_cycle_itinerary_length_le_seven`: `True`
- `no_cycleMin_gapped_three_even_ee`: `True`
- `no_cycleMin_gapped_three_even_eoe`: `True`
- no first-E transport theorem: `False`
- length eight open in census: `True`
- no length-nine theorem: `True`

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
- length_eight_census: `False`
- length_nine_census: `False`
- first_e_transport_lean: `True`
- induction_on_period: `False`
- induction_on_n: `False`

## Decision

**FIRST_E_TRANSPORT_GREEN**

Lean excludes gapped three-even CycleMins by first-E transport of the two-even tail at y>=n; the finite window k=9..16 has empty CycleItinerary tables below 256; for k>=17 small n is seven-odd on the prefix or the remainder; bunched a1-short leftovers remain.

This is not a halt result, not a length-8/9 census, and
not an exclusion of bunched three-even leftovers.

