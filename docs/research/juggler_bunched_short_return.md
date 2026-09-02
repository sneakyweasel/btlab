# Juggler exact short-cluster return sets

Status: **SHORT_RETURN_PARK**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Exact `T_{O^b E O^c E}(y) = n`,
not an interval seal. Not Z5, not a length-11 assembler, and
not a four-even leftover cell.

## Branch budget

```text
Mathematical target     Characterize R_{b,c}(n) and test
                        exact return against CycleMin fronts
Novelty hypothesis      exact preimages of n are rigid and
                        incompatible with CycleMin prefixes
Falsifier               abundant exact returns; fat odd
                        preimages of n^2; no rigidity
Existing machinery      even/odd floor cells; odd_preimage_unique;
                        cycle_last_even_ne_odd_sq
Maximum Phase-0 scope   exact inverses; R counts; CycleMin
                        exact hits; no Lean, no Z5
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **SHORT_RETURN_PARK**
- sorry-free: `True`
- even inverse singleton n^2: `False`
- odd cells of n^2 empty: `477` / `500`
- odd cells of n^2 with an odd integer: `12`
- last-odd empty layers: `15` / max `2`
- CycleMin e=2 landings: `1`
- CycleMin exact hits: `0`

even inverse is an interval of length 2n+1, not {n^2}; odd cells of n^2 are almost always empty, but CycleMin n is odd so n^2 is not in the last-even cell; that cell still has a last-odd layer of size at most 2; (0,0) return sets are abundant (order n^3); no CycleMin exact hit below the front cutoff.

## Attack 1 — even inverse

`floorPower` on an even `z` gives `n` iff `n^2 <= z < (n+1)^2`.
The singleton `z = n^2` is false. On a CycleMin, `n` is odd, so
`n^2` is odd and cannot be the last even landing
(`cycle_last_even_ne_odd_sq`).

- n=`2` count=`3` contains_n2=`True` singleton=`False`
- n=`3` count=`3` contains_n2=`False` singleton=`False`
- n=`12` count=`13` contains_n2=`True` singleton=`False`
- n=`13` count=`13` contains_n2=`False` singleton=`False`
- n=`37` count=`37` contains_n2=`False` singleton=`False`
- n=`100` count=`101` contains_n2=`True` singleton=`False`

## Attack 2 / 5 — odd preimage of n^2

By `odd_preimage_unique` there is at most one integer in the odd cell of `m = n^2`. Through `n <= 500`: empty=`477`, even-blocked=`10`, odd hits=`12`.

On a CycleMin the start `n` is odd, so `n^2` is odd and is not in the last-even cell. The square-edge equation `floor(z^{3/2}) = n^2` is therefore not the CycleMin last-odd condition. The last odd step of an `EOE` tail must hit some even in `[n^2, (n+1)^2)`.

All odd-cell hits at `m = n^2` through the cutoff:
- n=`6` z=`11`
- n=`15` z=`37`
- n=`27` z=`81`
- n=`79` z=`339`
- n=`125` z=`625`
- n=`150` z=`797`
- n=`165` z=`905`
- n=`168` z=`927`
- n=`188` z=`1077`
- n=`273` z=`1771`
- n=`276` z=`1797`
- n=`343` z=`2401`

## Return counts

- (b,c)=`(0,0)` first=`2` nonempty=`47` max=`115297` at12=`2041` at13=`2379`
- (b,c)=`(1,0)` first=`2` nonempty=`15` max=`38` at12=`24` at13=`23` (EE fibre unlisted above n_list)
- (b,c)=`(2,0)` first=`2` nonempty=`9` max=`4` at12=`1` at13=`0` (EE fibre unlisted above n_list)
- (b,c)=`(3,0)` first=`2` nonempty=`2` max=`1` at12=`0` at13=`0` (EE fibre unlisted above n_list)
- (b,c)=`(0,1)` first=`4` nonempty=`32` max=`356` at12=`29` at13=`31`
- (b,c)=`(1,1)` first=`4` nonempty=`28` max=`4` at12=`2` at13=`0`
- (b,c)=`(2,1)` first=`6` nonempty=`5` max=`1` at12=`0` at13=`0`

## CycleMin exact fronts

- landings=`1` follows=`0` exact=`0`

## Lean

- `floorPower_even_eq_iff_sq_interval`: `True`
- `floorPower_odd_eq_iff_cube_interval`: `True`
- `odd_preimage_unique`: `True`
- `cycle_last_even_ne_odd_sq`: `True`
- `cycle_trailing_evens_lt`: `True`
- `CycleMin`: `True`
- `cycleMin_ge_twelve`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- length_eleven_census: `False`
- z5_cells: `False`
- four_even_assembler: `False`

## Decision

**SHORT_RETURN_PARK**

even inverse is an interval of length 2n+1, not {n^2}; odd cells of n^2 are almost always empty, but CycleMin n is odd so n^2 is not in the last-even cell; that cell still has a last-odd layer of size at most 2; (0,0) return sets are abundant (order n^3); no CycleMin exact hit below the front cutoff.

This is not a halt result, not a Z5 exclusion, and not a
length-11 assembler.

