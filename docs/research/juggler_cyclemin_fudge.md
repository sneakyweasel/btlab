# Juggler CycleMin fudge versus leftover 2-bound

Status: **CYCLEMIN_FUDGE_LAYER_PROVED**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Leftover cells pay (x+1)/x <= 2.
CycleMin pays (x+1)/x <= (n+1)/n. The exponent machine is that
crossing on every letter of the thirty first-expanding leftovers.

## Branch budget

```text
Mathematical target     For the 30 length-11 leftovers, does
                        absorb_odd + absorb_even with x>=n give
                        n^A > (n+1)^{B+γ} at the first prefix
                        start?
Novelty hypothesis      leftover N0 is the 2-bound; CycleMin
                        replaces it by (n+1)/n and slack survives
Falsifier               some word has slack <= 0, or chain N0
                        still sits at leftover scale
Existing machinery      absorb_odd_step; trailing-evens cell;
                        30-word list; O^7 / (1,3) chains
Maximum Phase-0 scope   exponent machine on 30 words; Lean
                        CycleMin exclusion; no Z5, no census
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **CYCLEMIN_FUDGE_LAYER_PROVED**
- family slack: `3^7 - 2^11 = 139`

all 30 words have slack identically 139; chain N0 <= 29 (min 16); every first prefix start is at least 37; pin n<30 empty; leftover 2-fudge unused.

## Summary

- words: `30`
- slack min/max: `139` / `139`
- all slack positive: `True`
- all slack family 139: `True`
- all fire at first start: `True`
- pin n<30: `[]`
- ate / late / leftover-scale: `0` / `0` / `0`
- chain N0 min/max: `16` / `29`
- first start min/max: `37` / `2935`

## Rows

- `OOOOOOOEEEE` family=`EEE` A=`6177` right=`6038` slack=`139` chain_n0=`16` first=`289` fire=`True` r=`4`
- `OOOOOOEOEEE` family=`EEE` A=`6561` right=`6422` slack=`139` chain_n0=`17` first=`163` fire=`True` r=`3`
- `OOOOOEOOEEE` family=`EEE` A=`6945` right=`6806` slack=`139` chain_n0=`17` first=`241` fire=`True` r=`3`
- `OOOOEOOOEEE` family=`EEE` A=`7521` right=`7382` slack=`139` chain_n0=`18` first=`37` fire=`True` r=`3`
- `OOOEOOOOEEE` family=`EEE` A=`8385` right=`8246` slack=`139` chain_n0=`20` first=`113` fire=`True` r=`3`
- `OOEOOOOOEEE` family=`EEE` A=`9681` right=`9542` slack=`139` chain_n0=`22` first=`173` fire=`True` r=`3`
- `OOOOOOEEEOE` family=`EEOE` A=`8865` right=`8726` slack=`139` chain_n0=`21` first=`913` fire=`True` r=`1`
- `OOOOOEOEEOE` family=`EEOE` A=`9249` right=`9110` slack=`139` chain_n0=`22` first=`615` fire=`True` r=`1`
- `OOOOEOOEEOE` family=`EEOE` A=`9825` right=`9686` slack=`139` chain_n0=`23` first=`1113` fire=`True` r=`1`
- `OOOEOOOEEOE` family=`EEOE` A=`10689` right=`10550` slack=`139` chain_n0=`24` first=`225` fire=`True` r=`1`
- `OOEOOOOEEOE` family=`EEOE` A=`11985` right=`11846` slack=`139` chain_n0=`26` first=`693` fire=`True` r=`1`
- `OOOOOOEEOEE` family=`EOEE` A=`7329` right=`7190` slack=`139` chain_n0=`18` first=`673` fire=`True` r=`2`
- `OOOOOEOEOEE` family=`EOEE` A=`7713` right=`7574` slack=`139` chain_n0=`19` first=`899` fire=`True` r=`2`
- `OOOOEOOEOEE` family=`EOEE` A=`8289` right=`8150` slack=`139` chain_n0=`20` first=`1319` fire=`True` r=`2`
- `OOOEOOOEOEE` family=`EOEE` A=`9153` right=`9014` slack=`139` chain_n0=`21` first=`595` fire=`True` r=`2`
- `OOEOOOOEOEE` family=`EOEE` A=`10449` right=`10310` slack=`139` chain_n0=`24` first=`681` fire=`True` r=`2`
- `OOOOOEEOEOE` family=`EOEOE` A=`10017` right=`9878` slack=`139` chain_n0=`23` first=`1795` fire=`True` r=`1`
- `OOOOEOEOEOE` family=`EOEOE` A=`10593` right=`10454` slack=`139` chain_n0=`24` first=`2001` fire=`True` r=`1`
- `OOOEOOEOEOE` family=`EOEOE` A=`11457` right=`11318` slack=`139` chain_n0=`25` first=`1359` fire=`True` r=`1`
- `OOEOOOEOEOE` family=`EOEOE` A=`12753` right=`12614` slack=`139` chain_n0=`28` first=`483` fire=`True` r=`1`
- `OOOOOEEOOEE` family=`EOOEE` A=`8481` right=`8342` slack=`139` chain_n0=`20` first=`427` fire=`True` r=`2`
- `OOOOEOEOOEE` family=`EOOEE` A=`9057` right=`8918` slack=`139` chain_n0=`21` first=`103` fire=`True` r=`2`
- `OOOEOOEOOEE` family=`EOOEE` A=`9921` right=`9782` slack=`139` chain_n0=`23` first=`321` fire=`True` r=`2`
- `OOEOOOEOOEE` family=`EOOEE` A=`11217` right=`11078` slack=`139` chain_n0=`25` first=`491` fire=`True` r=`2`
- `OOOOEEOOEOE` family=`EOOEOE` A=`11745` right=`11606` slack=`139` chain_n0=`26` first=`513` fire=`True` r=`1`
- `OOOEOEOOEOE` family=`EOOEOE` A=`12609` right=`12470` slack=`139` chain_n0=`27` first=`2935` fire=`True` r=`1`
- `OOEOOEOOEOE` family=`EOOEOE` A=`13905` right=`13766` slack=`139` chain_n0=`29` first=`365` fire=`True` r=`1`
- `OOOOEEOOOEE` family=`EOOOEE` A=`10209` right=`10070` slack=`139` chain_n0=`23` first=`539` fire=`True` r=`2`
- `OOOEOEOOOEE` family=`EOOOEE` A=`11073` right=`10934` slack=`139` chain_n0=`25` first=`1045` fire=`True` r=`2`
- `OOEOOEOOOEE` family=`EOOOEE` A=`12369` right=`12230` slack=`139` chain_n0=`27` first=`565` fire=`True` r=`2`

## Proof schema

On a CycleMin every later state is >= n, so each +1-cell
crosses by n(x+1) <= (n+1)x. Odd letters are absorb_odd_step.
Even letters use x < (T(x)+1)^2 and the same crossing.
After the prefix, cycle_trailing_evens puts the image below
(n+1)^{2^r}. The composed comparison is n^A < (n+1)^{B+γ 2^r}.
Any 7-odd word that starts O keeps γ a power of 2, raises
on each later odd, and ends with slack 3^7-2^{11}=139
independent of even placement. A cycle is impossible when
n^{139} > (1+1/n)^{A-139}. That fires by n=29 on every
length-11 leftover; no prefix start exists below 30.

This is not a length-11 census. It does not exclude e=5.

## Lean

- `CycleMin`: `True`
- `cycle_trailing_evens_lt`: `True`
- `o7_image_ge_succ_pow16`: `True`
- `no_cycle_itinerary_even_count_le_three`: `True`
- `absorb_even_step`: `True`
- `family_slack139`: `True`
- `no_cycleMin_cyclemin_fudge`: `True`
- `no_cycleMin_slack139`: `True`
- `no_cycleMin_oooooooeeee`: `True`
- `no_cycle_itinerary_oooooooeeee`: `True`
- `no_cycle_itinerary_ooooooeoeee`: `True`
- `no_cycle_itinerary_ooooooeeeoe`: `True`
- `no_cycle_itinerary_oooooeoeeoe`: `True`
- `no_cycle_itinerary_ooooooeeoee`: `True`
- `no_cycle_itinerary_oooooeoeoee`: `True`
- `no_cycle_itinerary_oooooeeoeoe`: `True`
- `no_cycle_itinerary_ooooeoeoeoe`: `True`
- `no_cycleMin_ooooooeoeee`: `True`
- `no_cycleMin_oooooeooeee`: `True`
- `no_cycleMin_ooooeoooeee`: `True`
- `no_cycleMin_oooeooooeee`: `True`
- `no_cycleMin_ooeoooooeee`: `True`
- `no_cycleMin_ooooooeeeoe`: `True`
- `no_cycleMin_oooooeoeeoe`: `True`
- `no_cycleMin_ooooeooeeoe`: `True`
- `no_cycleMin_oooeoooeeoe`: `True`
- `no_cycleMin_ooeooooeeoe`: `True`
- `no_cycleMin_ooooooeeoee`: `True`
- `no_cycleMin_oooooeoeoee`: `True`
- `no_cycleMin_ooooeooeoee`: `True`
- `no_cycleMin_oooeoooeoee`: `True`
- `no_cycleMin_ooeooooeoee`: `True`
- `no_cycleMin_oooooeeoeoe`: `True`
- `no_cycleMin_ooooeoeoeoe`: `True`
- `no_cycleMin_oooeooeoeoe`: `True`
- `no_cycleMin_ooeoooeoeoe`: `True`
- `no_cycleMin_oooooeeooee`: `True`
- `no_cycleMin_ooooeoeooee`: `True`
- `no_cycleMin_oooeooeooee`: `True`
- `no_cycleMin_ooeoooeooee`: `True`
- `no_cycleMin_ooooeeooeoe`: `True`
- `no_cycleMin_oooeoeooeoe`: `True`
- `no_cycleMin_ooeooeooeoe`: `True`
- `no_cycleMin_ooooeeoooee`: `True`
- `no_cycleMin_oooeoeoooee`: `True`
- `no_cycleMin_ooeooeoooee`: `True`
- no `no_cycle_itinerary_length_eleven`: `True`
- no `no_cycle_itinerary_four_even`: `True`
- no `no_cycle_itinerary_cyclemin_fudge`: `True`
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
- twenty_three_word_scan: `False`

## Decision

**CYCLEMIN_FUDGE_LAYER_PROVED**

all 30 words have slack identically 139; chain N0 <= 29 (min 16); every first prefix start is at least 37; pin n<30 empty; leftover 2-fudge unused.

This is not a halt result and not a length-11 census.

