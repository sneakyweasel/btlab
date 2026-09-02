# Juggler O^7 EEEE inverse-cell window

Status: **O7EEEE_WINDOW_EMPTY**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. A cycle itinerary O^7 EEEE is the
seven-odd image landing in the EEEE inverse cell, then four
even square-roots back to n.

## Branch budget

```text
Mathematical target     Is T_{O^7 EEEE}(n)=n empty on the
                        leftover-cell window n<N0?
Novelty hypothesis      the EEEE inverse cell is empty of
                        O^7 images below N0
Falsifier               a hit, or T^7 enters the cell
Existing machinery      leftover_prefix_preimage; trailing evens
                        r=4; odd_preimage_unique; N0=828484409
Maximum Phase-0 scope   exact window scan of one word; no Lean,
                        no thirty-itinerary census, no Z5
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **O7EEEE_WINDOW_EMPTY**
- sorry-free: `True`

no O^7 EEEE cycle on 3<=n<828484409; T^7 never entered the EEEE cell (below=0, in=0, above=3234088); closest ratio 445.01033356279396 at n=289.

## Window

- word: `OOOOOOOEEEE`
- leftover-cell N0: `828484409`
- N0 matches lag table: `True`
- cell holds at N0: `True`
- cell holds at N0-1: `False`
- length-11 census: `False`
- Z5 opened: `False`

## Scans

- pin n<10000: o7=`84` in_cell=`0` hits=`[]` min_ratio=`445.01033356279396` at n=`289`
- near n<10000000: o7=`77692` in_cell=`0` hits=`[]` min_ratio=`445.01033356279396` at n=`289`
- full n<828484409: o7=`6473954` even_z=`3234088` below=`0` in_cell=`0` above=`3234088` hits=`[]` min_ratio=`445.01033356279396` at n=`289`

## Lean

- `leftover_prefix_preimage`: `True`
- `cycle_trailing_evens_lt`: `True`
- `odd_preimage_unique`: `True`
- `even_preimage_iff`: `True`
- `cycle_itinerary_length_ge_eleven`: `True`
- no `no_cycle_itinerary_oooooooeeee`: `True`
- no `no_cycle_itinerary_length_eleven`: `True`
- no `no_cycle_itinerary_four_even`: `True`
- no `juggler_reaches_one`: `True`
- Paper A has no O^7 EEEE theorem: `True`
- FloorPower not rewritten: `True`

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
- finite_progress_for_all: `False`

## Decision

**O7EEEE_WINDOW_EMPTY**

no O^7 EEEE cycle on 3<=n<828484409; T^7 never entered the EEEE cell (below=0, in=0, above=3234088); closest ratio 445.01033356279396 at n=289.

This is not a halt result and not a length-11 census.
The other twenty-nine leftovers are a separate job.

