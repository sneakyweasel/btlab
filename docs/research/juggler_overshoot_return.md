# Juggler later ReturnBelow after even-y overshoot

Status: **EVEN_Y_RETURN_SUFFIX_SCATTER**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. After e<=3 the first even
always overshoots on a minimal non-terminator. Halt on that
leftover is ReturnBelow from y>n. Novelty is only a>=4
even-y; a=2,3 replay Paper B.

## Branch budget

```text
Mathematical target     Does every first-E overshoot with even y
                        admit a uniform later word from y that
                        lands below the original n?
Novelty hypothesis      After e<=3 the first even always overshoots;
                        the even-y class then has one later
                        contractor, giving FiniteProgress on that class
Falsifier               a>=4 return words scatter, or only Paper B engines,
                        or an even-y stay like 37 / 77
Existing machinery      Progress spine; ReturnBelow; e<=3; Paper B; K3 parked
Maximum Phase-0 scope   Lean overshoot corollary; even-y census, novelty at a>=4
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **EVEN_Y_RETURN_SUFFIX_SCATTER**
- sorry-free: `True`

a>=4 even-y first-excursion descent dies (N0=9883); second excursion is not uniform; 96 ReturnBelow suffixes scatter with lengths 7..115.

## Window

- n_max: `10000`
- overshoots: `2504`
- easy even-y a=2,3: `947`
- hard even-y a>=4: `317`
- odd y: `1240`
- easy first-excursion all descend: `True`
- odd-y two-excursion stays (count only): `[37, 77, 89, 103, 111, 163, 173, 193, 205, 225, 229, 241, 265, 319, 321, 329, 335, 349, 365, 387]`

Pin n<=`80`: easy `13`, hard `0`, odd `5`.

## Hard class a>=4 even y

- count: `317`
- first excursion < n: `147`
- first excursion stay: `170`
- first-excursion N0: `9883`
- first stay min n: `115`
- first stay samples: `[115, 293, 357, 427, 477, 513, 539, 663, 673, 677, 761, 849]`
- second excursion all < n on stays: `False`
- second excursion failures: `[293, 357, 427, 477, 513, 539, 663, 673, 677, 761, 849, 877]`
- missing ReturnBelow: `[]`
- suffix counts: `{'E': 131, 'OE': 39, 'OOEE': 10, 'EE': 10, 'OEEE': 8, 'OEE': 7, 'EEE': 6, 'EOEE': 4, 'OEOEE': 4, 'OOOEEOE': 4, 'OOOEEE': 3, 'EOOOOOEOEOOOOOEEEEOOEOOEOEOEOEOEE': 2, 'EEEOOEOOEOEE': 2, 'OOEEOEE': 2, 'OEOEOOOEE': 2, 'OOEEOE': 2, 'OOEEOOEE': 2, 'OOOEEOEOOEOOEE': 1, 'OOEOOOOEOEOEEEOEE': 1, 'OOEOOEE': 1, 'OOOEOOOEOEEOEOOEE': 1, 'OEOEEEOEEE': 1, 'OOOOEEEOOOOEEEE': 1, 'OOOOEEOOEOEEOOOOEOOEEE': 1, 'OEOEEOOEEOOOEOOOOEOOOEOEOOOEEOOOOEOOOOEEEOOOEEEEOEE': 1, 'OOOOEOOEOEEE': 1, 'OEOEEOOEEOOOEE': 1, 'OOEOOOOOOOEOOEEEOEOEOOEOEE': 1, 'OOEOOEOEE': 1, 'OOOEOEEOE': 1, 'OOOEEOOEEE': 1, 'EOOEEOOEE': 1, 'OOEOEE': 1, 'OOOOEOEOOEEOEE': 1, 'OOOEOEOOOEEEOOEE': 1, 'OEEOE': 1, 'EOOEE': 1, 'EOOEEOEOOEE': 1, 'OOEEE': 1, 'OOOOEOEOEE': 1, 'OOOEOEOOOEEOOOEOEE': 1, 'OOOOEEEEOOEE': 1, 'OOOEEOOEOOOEOOOEEEOEOEE': 1, 'OOEOOEEE': 1, 'OEOOEEE': 1, 'OOEOOEOOOOEEOOEOEOOOEEOOOEEOEEE': 1, 'EOEEOEE': 1, 'OOOEOEOEE': 1, 'OOEOOEOEOOEEOOEE': 1, 'OOOEOEEE': 1, 'EOOEOOOOOOOEOEEOOOOEEOOOEOOOEEEEEOOOOEOEOOOEOEEE': 1, 'OOEOOEOEOEOEOE': 1, 'EOEEE': 1, 'OEOOEOEEOOEOEE': 1, 'EOOOEOOEEE': 1, 'OOEOEOOOEE': 1, 'OOOOEOEEOE': 1, 'EOOOEOOEOEOOEOOEEOOOEOOOEOEOOOOOEEOOEOOOOEOEOOEOOOEEOEOOEOEOEOOEEEOEOEEE': 1, 'OOEOOEOOEE': 1, 'OOOOOOEOOOOEOOOOOEEOOEOOEEEOOOOOEEEOEEEEOOOEOOOOOOOEOEOEOOOEOEEEEOOEEE': 1, 'EOOOEOEE': 1, 'OOEOEOOOEOEOOEOOOOOOEEEOEEE': 1, 'OOEOOEEOOEOEE': 1, 'OEEOOOOEEOOEE': 1, 'OEEEE': 1, 'OEOEEEEE': 1, 'EEOOEEOOEEE': 1, 'OOEOEOOEEEOOOOOEEE': 1, 'OOEEOOOOOEEEOOOEE': 1, 'OOOOEOOEOOEEOEOOOOOEEOOOEOEOEOEOOOEEE': 1, 'OOEEOEOE': 1, 'OOOEOEE': 1, 'OOOEOOOOOEOEEEOOOEOEEOEE': 1, 'OOOOEEOOEOOOOEOOEOEOEOEOOEOEOEOEOE': 1, 'OOOOOEOOEOEOOOEOEOEOOEEEOEE': 1, 'EOEOOOEEEOE': 1, 'OOOEOOOOOOOOOEEEOOOOEOOEEOEEOOOOOEOEEOOOOOEOOEOOOEOOOOEEEEEEOOOEEOEEOOOOOEOOOOOOEEOOEEEOOOOEOEOOEOEEEEOEEE': 1, 'OOOOOOEOOEOOEEEEE': 1, 'OOEEEOE': 1, 'OEOOOOEOEEEE': 1, 'OOOOEEOEOE': 1, 'OOOOOEEEOOOOEOOEEOOEOOOOOEEEOEEOE': 1, 'EEOOOEEEOOOEEE': 1, 'EEEOOOOOEEEE': 1, 'OOEOOOOEOOOEOEEEE': 1, 'OOOEOOEEE': 1, 'OEOEEE': 1, 'EOOOOOEEEEOOEOOOEEOEOE': 1, 'OEOOOEOOOOOOOOEOOOEOOOOOOOEOOOEEEOOOEEEEEEOEEOEEOOEE': 1, 'OOOEEOOOOOEEEOEOOEOE': 1, 'EEOOEOOOEEE': 1, 'OOOOOEOEOEEEE': 1, 'OEOEOOOOEEEE': 1, 'EOEOEOOEEOOOEEE': 1, 'OOOEEOEEE': 1, 'EOEOE': 1}`
- family by a: `False`
- suffixes even-only: `False`
- suffixes Paper B: `False`
- return length: `7`..`115`
- a values: `[4, 5, 6, 7, 8, 9, 10, 11]`

## Hard samples

- n=`115` a=`5` e=`66678934` b=`2` y*=`8165` first=`STAY` second_lt=`True` return=`{'step': 10, 'value': 29, 'word': 'OOOOOEEOEE'}` suffix=`OEE`
- n=`129` a=`5` e=`103162534` b=`5` y*=`3` first=`DESCENT` second_lt=`None` return=`{'step': 8, 'value': 100, 'word': 'OOOOOEEE'}` suffix=`E`
- n=`209` a=`5` e=`644363658` b=`3` y*=`159` first=`DESCENT` second_lt=`None` return=`{'step': 8, 'value': 159, 'word': 'OOOOOEEE'}` suffix=`E`
- n=`271` a=`4` e=`1440178` b=`4` y*=`5` first=`DESCENT` second_lt=`None` return=`{'step': 7, 'value': 34, 'word': 'OOOOEEE'}` suffix=`E`
- n=`289` a=`7` e=`1055283216607770715102` b=`8` y*=`1` first=`CAPTURE` second_lt=`None` return=`{'step': 12, 'value': 20, 'word': 'OOOOOOOEEEEE'}` suffix=`EEE`
- n=`293` a=`8` e=`40859682615271796005654168626860` b=`3` y*=`79950971` first=`STAY` second_lt=`False` return=`{'step': 43, 'value': 137, 'word': 'OOOOOOOOEEEOOOOOEOEOOOOOEEEEOOEOOEOEOEOEOEE'}` suffix=`EOOOOOEOEOOOOOEEEEOOEOOEOEOEOEOEE`
- n=`309` a=`4` e=`2007286` b=`3` y*=`37` first=`DESCENT` second_lt=`None` return=`{'step': 7, 'value': 37, 'word': 'OOOOEEE'}` suffix=`E`
- n=`357` a=`10` e=`39761658000430569938378859679953880455933576093805262002730372145468242628` b=`5` y*=`39807` first=`STAY` second_lt=`False` return=`{'step': 24, 'value': 152, 'word': 'OOOOOOOOOOEEEEEOOEOOEOEE'}` suffix=`EEEOOEOOEOEE`

## Lean

- `minimal_first_even_overshoots`: `True`
- `cycleMin_first_even_overshoots`: `True`
- `no_cycle_itinerary_even_count_le_three`: `True`
- `ReturnBelow`: `True`
- `finiteProgress_of_returnBelow`: `True`
- `minimal_first_even_dichotomy`: `True`
- certificate unchanged: `True`
- Paper A has no overshoot-return: `True`
- `PowerHeight` absent: `True`
- FloorPower not rewritten: `True`
- Progress unchanged: `True`
- no universal return-below: `True`
- no two-excursion progress: `True`
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
- return_below_universal: `False`
- cycle_impossible: `False`
- density_one_claimed: `False`
- two_excursion_always_returns: `False`

## Decision

**EVEN_Y_RETURN_SUFFIX_SCATTER**

a>=4 even-y first-excursion descent dies (N0=9883); second excursion is not uniform; 96 ReturnBelow suffixes scatter with lengths 7..115.

This is not a halt result. A cycle of length >=11 is one
FiniteProgress failure. Odd-y overshoot and K3 stay closed.

