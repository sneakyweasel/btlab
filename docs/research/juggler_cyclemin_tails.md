# Juggler CycleMin tails

Status: **CYCLEMIN_TAILS_PROVED**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The first-expanding leftovers
have seven odds. The tails are a0 > a0* on the same thirty
remainder shapes.

## Branch budget

```text
Mathematical target     For each of the 30 remainder shapes,
                        does CycleMin (n+1)/n fire for every
                        a0 > a0* through 16, with chain N0
                        at or below the first prefix start?
Novelty hypothesis      slack 3^o-2^{o+4} grows; CycleMin
                        beats leftover Z4 (N0<=180 at a0*+1)
Falsifier               slack <= 0, chain N0 above the first
                        start, or leftover-scale N0
Existing machinery      cyclemin_fudge exponent machine;
                        30 shapes; four_even_short_gap N0
Maximum Phase-0 scope   Lean slack 3^o-2^{o+4}; no pin,
                        no Z5, no census
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **CYCLEMIN_TAILS_PROVED**
- a0 hi: `16`

367 tails a0*+1..16 have slack identically 3^o-2^{o+4} >= 2465; chain N0 <= 7; pin n<8 empty; first tail layer (30 words, eight odds) fires at starts 37..4481; leftover Z4 unused (plus1 max 180).

## Summary

- rows: `367`
- slack identity: `True`
- slack min/max: `2465` / `10426798771`
- chain N0 min/max: `3` / `7`
- pin n<8: `[]`
- first tail layer fire: `True`
- first tail starts: `37` / `4481`
- leftover unused: `True`

## First tail layer

- `OOOOOOOOEEEE` slack=`2465` A=`18915` chain_n0=`5` first=`293` Z4=`37`
- `OOOOOOOEOEEE` slack=`2465` A=`19683` chain_n0=`5` first=`425` Z4=`39`
- `OOOOOOEOOEEE` slack=`2465` A=`20451` chain_n0=`5` first=`671` Z4=`44`
- `OOOOOEOOOEEE` slack=`2465` A=`21603` chain_n0=`5` first=`241` Z4=`51`
- `OOOOEOOOOEEE` slack=`2465` A=`23331` chain_n0=`5` first=`1721` Z4=`64`
- `OOOEOOOOOEEE` slack=`2465` A=`25923` chain_n0=`6` first=`113` Z4=`92`
- `OOOOOOOEEEOE` slack=`2465` A=`24291` chain_n0=`6` first=`1307` Z4=`35`
- `OOOOOOEOEEOE` slack=`2465` A=`25059` chain_n0=`6` first=`163` Z4=`38`
- `OOOOOEOOEEOE` slack=`2465` A=`26211` chain_n0=`6` first=`669` Z4=`45`
- `OOOOEOOOEEOE` slack=`2465` A=`27939` chain_n0=`6` first=`37` Z4=`56`
- `OOOEOOOOEEOE` slack=`2465` A=`30531` chain_n0=`6` first=`4385` Z4=`80`
- `OOOOOOOEEOEE` slack=`2465` A=`21219` chain_n0=`5` first=`477` Z4=`45`
- `OOOOOOEOEOEE` slack=`2465` A=`21987` chain_n0=`5` first=`2097` Z4=`50`
- `OOOOOEOOEOEE` slack=`2465` A=`23139` chain_n0=`5` first=`3653` Z4=`58`
- `OOOOEOOOEOEE` slack=`2465` A=`24867` chain_n0=`6` first=`387` Z4=`74`
- `OOOEOOOOEOEE` slack=`2465` A=`27459` chain_n0=`6` first=`335` Z4=`106`
- `OOOOOOEEOEOE` slack=`2465` A=`26595` chain_n0=`6` first=`1383` Z4=`47`
- `OOOOOEOEOEOE` slack=`2465` A=`27747` chain_n0=`6` first=`2155` Z4=`55`
- `OOOOEOOEOEOE` slack=`2465` A=`29475` chain_n0=`6` first=`4481` Z4=`69`
- `OOOEOOOEOEOE` slack=`2465` A=`32067` chain_n0=`7` first=`1423` Z4=`98`
- `OOOOOOEEOOEE` slack=`2465` A=`23523` chain_n0=`5` first=`673` Z4=`62`
- `OOOOOEOEOOEE` slack=`2465` A=`24675` chain_n0=`6` first=`899` Z4=`72`
- `OOOOEOOEOOEE` slack=`2465` A=`26403` chain_n0=`6` first=`1319` Z4=`91`
- `OOOEOOOEOOEE` slack=`2465` A=`28995` chain_n0=`6` first=`1123` Z4=`131`
- `OOOOOEEOOEOE` slack=`2465` A=`30051` chain_n0=`6` first=`1163` Z4=`75`
- `OOOOEOEOOEOE` slack=`2465` A=`31779` chain_n0=`7` first=`205` Z4=`95`
- `OOOEOOEOOEOE` slack=`2465` A=`34371` chain_n0=`7` first=`321` Z4=`135`
- `OOOOOEEOOOEE` slack=`2465` A=`26979` chain_n0=`6` first=`427` Z4=`99`
- `OOOOEOEOOOEE` slack=`2465` A=`28707` chain_n0=`6` first=`103` Z4=`125`
- `OOOEOOEOOOEE` slack=`2465` A=`31299` chain_n0=`7` first=`807` Z4=`180`

## Proof schema

Any start-O four-even word with o odds has length o+4.
The CycleMin exponent machine keeps gamma a power of two
and raises on each later odd, so slack is 3^o-2^{o+4}.
At eight odds that is 2465. The integer comparison
n^A > (n+1)^{A-slack} first holds by n=7 on every scanned
tail. No n<8 follows any of those prefixes. Leftover Z4
is unused.

This is not a four-even assembler and not Z5.

## Lean

- `CycleMin`: `True`
- `absorb_even_step`: `True`
- `family_slack139`: `True`
- `familySlack`: `True`
- `familySlack_eight`: `True`
- `two_pow_add_four_le_three_pow`: `True`
- `exponents_slack_add`: `True`
- `slack_of_four_even`: `True`
- `slack_of_four_even_word`: `True`
- `no_cycleMin_cyclemin_fudge`: `True`
- no `no_cycle_itinerary_length_eleven`: `True`
- no `no_cycle_itinerary_four_even`: `True`
- no `no_cycleMin_four_even`: `True`
- no `no_cycle_itinerary_cyclemin_tails`: `True`
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
- z5_cell: `False`

## Decision

**CYCLEMIN_TAILS_PROVED**

367 tails a0*+1..16 have slack identically 3^o-2^{o+4} >= 2465; chain N0 <= 7; pin n<8 empty; first tail layer (30 words, eight odds) fires at starts 37..4481; leftover Z4 unused (plus1 max 180).

This is not a halt result and not a length-11 census.

