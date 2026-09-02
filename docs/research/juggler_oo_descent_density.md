# Juggler odd-to-odd descent density

Status: **FIXED_FAMILY_POSITIVE_LEFTOVER**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Fixed finite certificate families
inside the odd-to-odd class: `OOOEE`, `OOEOE`, and first return
in at most `K` steps. This is not Terras's theorem.

## Branch budget

```text
Mathematical target     Does any fixed finite certificate family
                        cover almost all of OO, or is leftover
                        density bounded away from 0?
Novelty hypothesis      leftover o(|OO|) for a named word or horizon,
                        or a positive leftover plateau
Falsifier               leftover plateau for every fixed family,
                        or a rewrite of Corollary 5.2 / Prop 4.5
Existing machinery      FiniteProgress; wordOOOEE; Prop 4.5
Maximum Phase-0 scope   OOOEE, OOEOE, K=5,10,20,40; N=10^4,10^5,10^6
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **FIXED_FAMILY_POSITIVE_LEFTOVER**
- words: `['OOOEE', 'OOEOE']`
- horizons: `[5, 10, 20, 40]`
- sorry-free: `True`

every tested fixed family has a stable leftover fraction bounded away from 0.

## Census

### N=`1000`

- OO starts: `252`
- all starts: `999`
- realize OOOEE: `32` rate=`0.12698413` leftover=`0.87301587`
- realize OOEOE: `33` rate=`0.13095238` leftover=`0.86904762`
- word union: `65` rate=`0.25793651` leftover=`0.74206349`
- OO return ≤5: `137` rate=`0.54365079` leftover=`115` leftover_rate=`0.45634921`
- OO return ≤10: `187` rate=`0.74206349` leftover=`65` leftover_rate=`0.25793651`
- OO return ≤20: `221` rate=`0.87698413` leftover=`31` leftover_rate=`0.12301587`
- OO return ≤40: `248` rate=`0.98412698` leftover=`4` leftover_rate=`0.01587302`
- all-start return ≤20: `968` rate=`0.96896897`
- exact through horizon: `20`
- unresolved through horizon 20: `0`
- horizon-40 bit-cap exits: `0`

### N=`10000`

- OO starts: `2504`
- all starts: `9999`
- realize OOOEE: `330` rate=`0.13178914` leftover=`0.86821086`
- realize OOEOE: `315` rate=`0.12579872` leftover=`0.87420128`
- word union: `645` rate=`0.25758786` leftover=`0.74241214`
- OO return ≤5: `1262` rate=`0.50399361` leftover=`1242` leftover_rate=`0.49600639`
- OO return ≤10: `1861` rate=`0.74321086` leftover=`643` leftover_rate=`0.25678914`
- OO return ≤20: `2220` rate=`0.88658147` leftover=`284` leftover_rate=`0.11341853`
- OO return ≤40: `2443` rate=`0.97563898` leftover=`61` leftover_rate=`0.02436102`
- all-start return ≤20: `9715` rate=`0.97159716`
- exact through horizon: `20`
- unresolved through horizon 20: `0`
- horizon-40 bit-cap exits: `6`

### N=`100000`

- OO starts: `24984`
- all starts: `99999`
- realize OOOEE: `3181` rate=`0.12732149` leftover=`0.87267851`
- realize OOEOE: `3153` rate=`0.12620077` leftover=`0.87379923`
- word union: `6334` rate=`0.25352225` leftover=`0.74647775`
- OO return ≤5: `12510` rate=`0.50072046` leftover=`12474` leftover_rate=`0.49927954`
- OO return ≤10: `18746` rate=`0.7503202` leftover=`6238` leftover_rate=`0.2496798`
- OO return ≤20: `22379` rate=`0.89573327` leftover=`2605` leftover_rate=`0.10426673`
- OO return ≤40: `24375` rate=`0.9756244` leftover=`609` leftover_rate=`0.0243756`
- all-start return ≤20: `97394` rate=`0.97394974`
- exact through horizon: `20`
- unresolved through horizon 20: `0`
- horizon-40 bit-cap exits: `95`

### N=`1000000`

- OO starts: `249926`
- all starts: `999999`
- realize OOOEE: `31314` rate=`0.12529309` leftover=`0.87470691`
- realize OOEOE: `31125` rate=`0.12453686` leftover=`0.87546314`
- word union: `62439` rate=`0.24982995` leftover=`0.75017005`
- OO return ≤5: `124852` rate=`0.49955587` leftover=`125074` leftover_rate=`0.50044413`
- OO return ≤10: `187394` rate=`0.74979794` leftover=`62532` leftover_rate=`0.25020206`
- OO return ≤20: `223683` rate=`0.89499692` leftover=`26243` leftover_rate=`0.10500308`
- OO return ≤40: `243960` rate=`0.97612893` leftover=`5966` leftover_rate=`0.02387107`
- all-start return ≤20: `973756` rate=`0.97375697`
- exact through horizon: `20`
- unresolved through horizon 20: `0`
- horizon-40 bit-cap exits: `1126`

## Proposition 4.4 reproduction

- present: `True`
- matches N=10^3 row: `True`
- observed: OO=`252` return20=`221` all20=`968`

## Lean witnesses

- `FiniteProgress`: `True`
- `unresolved_is_odd_odd`: `True`
- `power_bound_contracts`: `True`
- `floorPower_oooee_of_follows`: `True`
- `wordOOOEE`: `True`
- `odd_preimage_unique`: `True`
- no halt theorem: `True`
- no all-FiniteProgress theorem: `True`
- no progress tactic: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- almost_all_finiteProgress: `False`
- almost_all_reachesOne: `False`
- terras_for_juggler: `False`
- image_discrepancy_transfer: `False`
- finite_progress_for_all: `False`
- cycle_obstruction: `False`

## Decision

**FIXED_FAMILY_POSITIVE_LEFTOVER**

every tested fixed family has a stable leftover fraction bounded away from 0.

This is not a halt result. It is not almost-all FiniteProgress
and not a density of ReachesOne.

