# Juggler CycleMin necklace slack

Status: **CYCLEMIN_NECKLACE_REFUTED**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The thirty first-expanding
leftovers are 30 of the 56 CycleMin-shaped length-11 four-even
words. Extra rotations land in the other 26.

## Branch budget

```text
Mathematical target     Does slack 139 plus a bounded pin
                        exclude every length-11 CycleMin-shaped
                        four-even word (the 56)?
Novelty hypothesis      extra rotations are a3>=2 spellings of
                        the same identity; e>=5 is contracting
Falsifier               some of the 26 have N0 above the first
                        prefix start, or a pin hit below that N0
Existing machinery      no_cycleMin_slack139; slack_of_four_even;
                        prefix_cell_exponents; chain_n0
Maximum Phase-0 scope   one scan of the 56 words; no Lean census,
                        no 26 named theorems, no tails pin, no e=5
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **CYCLEMIN_NECKLACE_REFUTED**
- family slack: `139`

slack stays 139 on all 56, but ['OOEEEOOOOOE', 'OOOEEEOOOOE'] have chain N0 above the first prefix start; pin hits [('OOEEEOOOOOE', [5], 55), ('OOOEEEOOOOE', [3], 42)]; A max 30705 exceeds the fudge bound 13905 on 21 words.

## Summary

- words: `56` (fudge `30`, extra `26`)
- slack identity: `True`
- slack min/max: `139` / `139`
- A min/max: `6177` / `30705`
- A over fudge 13905: `21` `['OOEEEOOOOOE', 'OOEEOEOOOOE', 'OOEEOOEOOOE', 'OOEEOOOEOOE', 'OOEEOOOOEOE', 'OOEEOOOOOEE', 'OOEOEEOOOOE', 'OOEOEOEOOOE', 'OOEOEOOEOOE', 'OOEOEOOOEOE', 'OOEOEOOOOEE', 'OOEOOEEOOOE', 'OOEOOEOEOOE', 'OOEOOOEEOOE', 'OOOEEEOOOOE', 'OOOEEOEOOOE', 'OOOEEOOEOOE', 'OOOEEOOOEOE', 'OOOEOEEOOOE', 'OOOEOEOEOOE', 'OOOOEEEOOOE']`
- chain N0 min/max: `16` / `55`
- first start min/max: `3` / `77625`
- all fire at first: `False`
- pin hits: `[('OOEEEOOOOOE', [5], 55), ('OOOEEEOOOOE', [3], 42)]`
- extra 26 fire / pin empty: `False` / `False`
- extra A min/max: `11553` / `30705`
- extra max N0: `55`

## Extra 26

- `OOEEEOOOOOE` A=`30705` slack=`139` chain_n0=`55` first=`5` fire=`False` pin=`[5]` a3=`5`
- `OOEEOEOOOOE` A=`25521` slack=`139` chain_n0=`47` first=`77625` fire=`True` pin=`[]` a3=`4`
- `OOEEOOEOOOE` A=`22065` slack=`139` chain_n0=`42` first=`3983` fire=`True` pin=`[]` a3=`3`
- `OOEEOOOEOOE` A=`19761` slack=`139` chain_n0=`39` first=`3539` fire=`True` pin=`[]` a3=`2`
- `OOEEOOOOEOE` A=`18225` slack=`139` chain_n0=`36` first=`3811` fire=`True` pin=`[]` a3=`1`
- `OOEEOOOOOEE` A=`16689` slack=`139` chain_n0=`34` first=`4639` fire=`True` pin=`[]` a3=`0`
- `OOEOEEOOOOE` A=`22929` slack=`139` chain_n0=`44` first=`5249` fire=`True` pin=`[]` a3=`4`
- `OOEOEOEOOOE` A=`19473` slack=`139` chain_n0=`38` first=`979` fire=`True` pin=`[]` a3=`3`
- `OOEOEOOEOOE` A=`17169` slack=`139` chain_n0=`35` first=`263` fire=`True` pin=`[]` a3=`2`
- `OOEOEOOOEOE` A=`15633` slack=`139` chain_n0=`32` first=`175` fire=`True` pin=`[]` a3=`1`
- `OOEOEOOOOEE` A=`14097` slack=`139` chain_n0=`30` first=`1111` fire=`True` pin=`[]` a3=`0`
- `OOEOOEEOOOE` A=`17745` slack=`139` chain_n0=`36` first=`1439` fire=`True` pin=`[]` a3=`3`
- `OOEOOEOEOOE` A=`15441` slack=`139` chain_n0=`32` first=`1969` fire=`True` pin=`[]` a3=`2`
- `OOEOOOEEOOE` A=`14289` slack=`139` chain_n0=`30` first=`1419` fire=`True` pin=`[]` a3=`2`
- `OOOEEEOOOOE` A=`21633` slack=`139` chain_n0=`42` first=`3` fire=`False` pin=`[3]` a3=`4`
- `OOOEEOEOOOE` A=`18177` slack=`139` chain_n0=`36` first=`1055` fire=`True` pin=`[]` a3=`3`
- `OOOEEOOEOOE` A=`15873` slack=`139` chain_n0=`33` first=`3237` fire=`True` pin=`[]` a3=`2`
- `OOOEEOOOEOE` A=`14337` slack=`139` chain_n0=`30` first=`1415` fire=`True` pin=`[]` a3=`1`
- `OOOEEOOOOEE` A=`12801` slack=`139` chain_n0=`28` first=`895` fire=`True` pin=`[]` a3=`0`
- `OOOEOEEOOOE` A=`16449` slack=`139` chain_n0=`34` first=`965` fire=`True` pin=`[]` a3=`3`
- `OOOEOEOEOOE` A=`14145` slack=`139` chain_n0=`30` first=`629` fire=`True` pin=`[]` a3=`2`
- `OOOEOOEEOOE` A=`12993` slack=`139` chain_n0=`28` first=`647` fire=`True` pin=`[]` a3=`2`
- `OOOOEEEOOOE` A=`15585` slack=`139` chain_n0=`32` first=`309` fire=`True` pin=`[]` a3=`3`
- `OOOOEEOEOOE` A=`13281` slack=`139` chain_n0=`28` first=`1147` fire=`True` pin=`[]` a3=`2`
- `OOOOEOEEOOE` A=`12129` slack=`139` chain_n0=`26` first=`533` fire=`True` pin=`[]` a3=`2`
- `OOOOOEEEOOE` A=`11553` slack=`139` chain_n0=`26` first=`767` fire=`True` pin=`[]` a3=`2`

## Proof schema

Any start-O four-even word with 7 odds has length 11.
CycleMin starts OO, so a0>=2. There are 56 such words.
Slack is identically 3^7-2^{11}=139. A cycle is impossible
when n^{139} > (1+1/n)^{A-139} and no prefix start exists
below that N0. Five or more evens at length 11 are
formally contracting (3^6 < 2^{11}).

Two extra itineraries miss: OOEEEOOOOOE follows its prefix at
n=5 with N0=55, and OOOEEEOOOOE follows at n=3 with N0=42.
Slack 139 is not enough for a uniform pin. This is not a
length-11 census and not a two-word rescue.

## Lean

- `CycleMin`: `True`
- `absorb_even_step`: `True`
- `family_slack139`: `True`
- `slack_of_four_even`: `True`
- `slack_of_four_even_word`: `True`
- `slack139_of_seven_odd_length_eleven`: `True`
- `no_cycleMin_slack139`: `True`
- `no_cycleMin_cyclemin_fudge`: `True`
- `no_cycle_itinerary_even_count_le_three`: `True`
- `cycle_itinerary_formally_expanding`: `True`
- no `no_cycle_itinerary_length_eleven`: `True`
- no `no_cycleMin_length_eleven`: `True`
- no `no_cycle_itinerary_four_even`: `True`
- no `no_cycleMin_four_even`: `True`
- no `no_cycleMin_necklace`: `True`
- no `no_cycle_itinerary_cyclemin_necklace`: `True`
- no `juggler_reaches_one`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycle_impossible: `False`
- length_eleven_census: `False`
- four_even_impossible: `False`
- twenty_six_word_rescue: `False`
- z5_cell: `False`

## Decision

**CYCLEMIN_NECKLACE_REFUTED**

slack stays 139 on all 56, but ['OOEEEOOOOOE', 'OOOEEEOOOOE'] have chain N0 above the first prefix start; pin hits [('OOEEEOOOOOE', [5], 55), ('OOOEEEOOOOE', [3], 42)]; A max 30705 exceeds the fudge bound 13905 on 21 words.

This is not a halt result. A length-11 census is a later
corollary only if the scan is clean.

