# Juggler four-even short-first-gap prefix-cell

Status: **FOUR_EVEN_SHORT_GAP_PARK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The 30 short-first-gap four-even
shapes only; not a length-8/9/11 census and not a thirty-family
Lean list.

## Branch budget

```text
Mathematical target     Do the 30 four-even short-first-gap
                        leftovers fire as one prefix-cell?
Novelty hypothesis      Z4 = three-even Z pulled back through
                        E O^{a1} is one family, not 30 tails
Falsifier               The cell misses the first expanding
                        a0, or N0 is unbounded after it
Existing machinery      three-even Z; denom bits; 30-shape list
Maximum Phase-0 scope   Log-cell N0 for 30 shapes; no Lean,
                        no tables, no Paper A
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **FOUR_EVEN_SHORT_GAP_PARK**
- sorry-free: `True`
- shapes: `30`
- first expanding all length 11: `True`
- miss first expanding in window 800: `True`
- max N0 at a0+1: `180`
- max N0 at a0+2: `22`
- min large N0 at first expanding: `437599552`
- max large N0 at first expanding: `1612237392847051`

Z4 is the three-even cell pulled back through E O^{a1}; it fires on all 30 shapes at a0_exp+1 with N0<=180 and at a0_exp+2 with N0<=22; at the first expanding length (30 itineraries of length 11) N0 is 10^8 to 10^15; not a thirty-family Lean list and not a length-11 census.

## First-expanding itineraries (length 11)

- `OOOOOOOEEEE` (EEE, a1=0, N0~828484409, a0+1 N0=37)
- `OOOOOOEOEEE` (EEE, a1=1, N0~1568526333, a0+1 N0=39)
- `OOOOOEOOEEE` (EEE, a1=2, N0~4086043903, a0+1 N0=44)
- `OOOOEOOOEEE` (EEE, a1=3, N0~17179869199, a0+1 N0=51)
- `OOOEOOOOEEE` (EEE, a1=4, N0~148113652199, a0+1 N0=64)
- `OOEOOOOOEEE` (EEE, a1=5, N0~3749366963330, a0+1 N0=92)
- `OOOOOOEEEOE` (EEOE, a1=0, N0~437599552, a0+1 N0=35)
- `OOOOOEOEEOE` (EEOE, a1=1, N0~1139955969, a0+1 N0=38)
- `OOOOEOOEEOE` (EEOE, a1=2, N0~4792972066, a0+1 N0=45)
- `OOOEOOOEEOE` (EEOE, a1=3, N0~41321885980, a0+1 N0=56)
- `OOEOOOOEEOE` (EEOE, a1=4, N0~1046027235270, a0+1 N0=80)
- `OOOOOOEEOEE` (EOEE, a1=0, N0~5622206167, a0+1 N0=45)
- `OOOOOEOEOEE` (EOEE, a1=1, N0~14645964716, a0+1 N0=50)
- `OOOOEOOEOEE` (EOEE, a1=2, N0~61579308643, a0+1 N0=58)
- `OOOEOOOEOEE` (EOEE, a1=3, N0~530896725835, a0+1 N0=74)
- `OOEOOOOEOEE` (EOEE, a1=4, N0~13439184135766, a0+1 N0=106)
- `OOOOOEEOEOE` (EOEOE, a1=0, N0~7735893922, a0+1 N0=47)
- `OOOOEOEOEOE` (EOEOE, a1=1, N0~32525750839, a0+1 N0=55)
- `OOOEOOEOEOE` (EOEOE, a1=2, N0~280415857259, a0+1 N0=69)
- `OOEOOOEOEOE` (EOEOE, a1=3, N0~7098481035595, a0+1 N0=98)
- `OOOOOEEOOEE` (EOOEE, a1=0, N0~99389479725, a0+1 N0=62)
- `OOOOEOEOOEE` (EOOEE, a1=1, N0~417885442903, a0+1 N0=72)
- `OOOEOOEOOEE` (EOOEE, a1=2, N0~3602736346711, a0+1 N0=91)
- `OOEOOOEOOEE` (EOOEE, a1=3, N0~91200105031766, a0+1 N0=131)
- `OOOOEEOOEOE` (EOOEOE, a1=0, N0~574990913574, a0+1 N0=75)
- `OOOEOEOOEOE` (EOOEOE, a1=1, N0~4957197477348, a0+1 N0=95)
- `OOEOOEOOEOE` (EOOEOE, a1=2, N0~125487098441322, a0+1 N0=135)
- `OOOOEEOOOEE` (EOOOEE, a1=0, N0~7387387730711, a0+1 N0=99)
- `OOOEOEOOOEE` (EOOOEE, a1=1, N0~63689249619738, a0+1 N0=125)
- `OOEOOEOOOEE` (EOOOEE, a1=2, N0~1612237392847051, a0+1 N0=180)

## Lean

- `CycleMin`: `True`
- `no_cycle_itinerary_two_even_ee`: `True`
- `no_cycleMin_gapped_three_even_ee`: `True`
- `no_cycle_itinerary_three_even_eee`: `True`
- `no_cycle_itinerary_three_even_eoooee`: `True`
- no four-even theorem: `True`
- no length-11 theorem: `True`
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
- length_eleven_census: `False`
- four_even_lean: `False`
- induction_on_period: `False`
- induction_on_n: `False`

## Decision

**FOUR_EVEN_SHORT_GAP_PARK**

Z4 is the three-even cell pulled back through E O^{a1}; it fires on all 30 shapes at a0_exp+1 with N0<=180 and at a0_exp+2 with N0<=22; at the first expanding length (30 itineraries of length 11) N0 is 10^8 to 10^15; not a thirty-family Lean list and not a length-11 census.

This is not a halt result and not a length-8/9/11 census.

