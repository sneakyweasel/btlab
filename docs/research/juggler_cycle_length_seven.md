# Juggler length-7 cycle-itinerary inventory

Status: **LENGTH_SEVEN_LEFTOVER_TAIL_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Length 7 only; length 8 is open.

## Branch budget

```text
Mathematical target     Which even-terminating expanding length-7
                        words survive the Paper A filters, and do
                        the two leftover tails exclude CycleItinerary?
Novelty hypothesis      Length 7 is the same two-even type as
                        length 6; bootstrap plus Lemma 3.5 tails
Falsifier               A leftover whose tail never fires, or a
                        third leftover shape
Existing machinery      expansion, rotation, odd-run, OO/OOO,
                        CycleMin, internal-E bootstrap, leftover tail
Maximum Phase-0 scope   inventory + N0 + finite table; no Lean
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **LENGTH_SEVEN_LEFTOVER_TAIL_GREEN**
- secondary: `['TWO_EVEN_TYPE_THROUGH_EIGHT']`
- sorry-free: `True`

length 7 has the same two-even geometry as length 6: odd-run excludes OOOOOOE, internal-E bootstrap excludes CycleMin of OOEOOOE and OOOEOOE (n=3 is a parity failure), and the two leftovers die by the Lemma 3.5 tail n^243 > 2^422 (n+1)^128 for n >= 14 together with empty finite tables below the cutoffs; Lean packages both leftovers and assembles no_cycle_itinerary_length_le_seven.

## Even-terminating expanding length-7 words

- `OOOOOOE` α=`729/128` internal_E=`None` suffix=`None` th=`None` bootstrap=`False` cyclemin=`True` filter=`no_cycle_odd_run_append_even`
- `EOOOOOE` α=`243/128` internal_E=`0` suffix=`OOOOO` th=`odd_run_suffix_threshold` bootstrap=`False` cyclemin=`False` filter=`rotate_onto_OOOOOEE`
- `OEOOOOE` α=`243/128` internal_E=`1` suffix=`OOOO` th=`odd_run_suffix_threshold` bootstrap=`False` cyclemin=`False` filter=`cycleMin_not_odd_even`
- `OOEOOOE` α=`243/128` internal_E=`2` suffix=`OOO` th=`ooo_suffix_threshold` bootstrap=`True` cyclemin=`True` filter=`bootstrap_ooo_suffix_threshold`
- `OOOEOOE` α=`243/128` internal_E=`3` suffix=`OO` th=`oo_suffix_threshold` bootstrap=`True` cyclemin=`True` filter=`bootstrap_oo_suffix_threshold`
- `OOOOEOE` α=`243/128` internal_E=`4` suffix=`O` th=`None` bootstrap=`False` cyclemin=`True` filter=`leftover_tail_EOE`
- `OOOOOEE` α=`243/128` internal_E=`5` suffix=`` th=`None` bootstrap=`False` cyclemin=`True` filter=`leftover_tail_EE`

- unique family: `True`
- leftovers: `['OOOOEOE', 'OOOOOEE']`
- bootstrap: `['OOEOOOE', 'OOOEOOE']`
- odd-run: `['OOOOOOE']`
- unclassified: `[]`

## Bootstrap small-n parity

- OOEOOOE at 3 realizes: `False` fail_state=`11`
- OOOEOOE at 3 realizes: `False` fail_state=`6`
- OOOEOOE at 5 realizes: `False` fail_state=`36`

## Leftover tails

- lowerDenom(OOOOO) = 2^422: `True`
- lowerDenom(OOOO) = 2^130: `True`
- lowerDenom(OOOOEO) = 2^550: `True`
- refined comparison: `n^243 > 2^422 (n+1)^128`
- naive EOE comparison: `n^243 > 2^550 (n+1)^128`
- N0 refined: `14`
- N0 naive EOE: `29`
- N0 (y+1)^3 < 2A^4: `2`
- N0 OOOOOEE: `14`
- N0 OOOOEOE: `14`
- refined holds at 256: `True`
- both tails fire: `True`
- both tables empty: `True`

- `OOOOOEE` checked=`12` follows=`0` hits=`[]`
- `OOOOEOE` checked=`12` follows=`0` hits=`[]`

## Two-even observation (not implemented)

- length `6` o_min=`4` max_E=`2` three_even=`False`
- length `7` o_min=`5` max_E=`2` three_even=`False`
- length `8` o_min=`6` max_E=`2` three_even=`False`
- length `9` o_min=`6` max_E=`3` three_even=`True`
- length `10` o_min=`7` max_E=`3` three_even=`True`

- length 8 is the same two-even type: `True`
- length 9 is the first three-even length: `True`
- implemented: `False`
- n-search / length 8 / length 9: `False` / `False` / `False`

## Lean

- `cycle_itinerary_formally_expanding`: `True`
- `no_cycle_odd_run_append_even`: `True`
- `oo_suffix_threshold`: `True`
- `ooo_suffix_threshold`: `True`
- `no_cycleMin_internal_even_threshold`: `True`
- `cycleMin_not_odd_even`: `True`
- `cycleMin_not_start_even`: `True`
- `cycle_last_even_interval`: `True`
- `no_cycle_itinerary_length_le_six`: `True`
- `no_cycle_itinerary_ooeoooe`: `True`
- `no_cycle_itinerary_oooeooe`: `True`
- `no_cycle_itinerary_oooooee`: `True`
- `no_cycle_itinerary_ooooeoe`: `True`
- `no_cycle_itinerary_length_le_seven`: `True`
- certificate unchanged: `True`
- FloorPower not rewritten: `True`
- length eight open in census: `True`
- length-seven census present: `True`
- no length-eight theorem: `True`
- orbit-min hypothesis unused: `True`
- PowerBoundEq not used as cycle attack: `True`
- O-terminating not claimed: `True`
- no all-cycles-impossible theorem: `True`
- no cycle engine: `True`
- no global halt theorem: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- cycles_impossible: `False`
- O_terminating_cycles_impossible: `False`
- length_seven_cycles_impossible: `True`
- length_seven_lean_census: `True`
- useful_uniform_Q0: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`
- paper_b_length_seven_density: `False`
- all_odd_orbit: `False`
- finite_progress_for_all: `False`

## Decision

**LENGTH_SEVEN_LEFTOVER_TAIL_GREEN**

length 7 has the same two-even geometry as length 6: odd-run excludes OOOOOOE, internal-E bootstrap excludes CycleMin of OOEOOOE and OOOEOOE (n=3 is a parity failure), and the two leftovers die by the Lemma 3.5 tail n^243 > 2^422 (n+1)^128 for n >= 14 together with empty finite tables below the cutoffs; Lean packages both leftovers and assembles no_cycle_itinerary_length_le_seven.

This is not a halt result. Length-7 cycle itineraries are Lean-excluded.
Cycles ending in O as CycleItinerary are not treated separately:
mixed itineraries rotate to an even-terminating orientation.
Length 8 and 9 were not opened.

