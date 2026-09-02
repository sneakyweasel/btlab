# Juggler length-9 three-even leftovers

Status: **THREE_EVEN_PREFIX_CELL_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Three-even leftovers only; not a
length-9 Lean census and not induction on period or on n.

## Branch budget

```text
Mathematical target     What argument excludes the length-9
                        three-even leftover CycleItineraries?
Novelty hypothesis      Last-internal suffix is always O^c;
                        leftovers are nine words O^a E O^b E O^c E;
                        odd-prefix + mixed-tail cells replace the
                        two-even families
Falsifier               A leftover whose prefix-cell tail never
                        fires, or a CycleItinerary realization below N0
Existing machinery      expansion, CycleMin, last-internal
                        bootstrap, Lemma 3.5 cells, lowerDenom
Maximum Phase-0 scope   inventory + prefix-cell N0 + finite table;
                        no Lean, no length 10, no halt
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **THREE_EVEN_PREFIX_CELL_GREEN**
- secondary: `['FIRST_E_TRANSPORT_FOR_A2', 'LAST_INTERNAL_SUFFIX_ALWAYS_O_RUN']`
- sorry-free: `True`

length 9 has 28 three-even even-terminating expanding itineraries; last-internal suffix is always O^c so bootstrap still kills c>=2; the nine leftovers O^a E O^b E O^c E with a>=2 and c in {0,1} die by the odd-prefix cell tail (N0<=374) with empty CycleItinerary tables; a=2 remainders are the Lemma 3.5 words OOOOEE / OOOEOE.

## Counts

- expanding even-terminating length-9 words: `37`
- odd-run: `['OOOOOOOOE']`
- two-even: `8` (same type as lengths 6-8; not opened)
- three-even: `28`
- leftovers: `['OOOOOOEEE', 'OOOOOEOEE', 'OOOOOEEOE', 'OOOOEOOEE', 'OOOOEOEOE', 'OOOEOOOEE', 'OOOEOOEOE', 'OOEOOOOEE', 'OOEOOOEOE']`
- bootstrap: `['OOOOEEOOE', 'OOOEOEOOE', 'OOOEEOOOE', 'OOEOOEOOE', 'OOEOEOOOE', 'OOEEOOOOE']`
- unclassified: `[]`
- last-internal suffix contains E: `False`

## Three-even leftovers

- `OOOOOOEEE` abc=`[6, 0, 0]` Cbits=`1330` v=`EE` v_exp=`False` lemma35=`False` N0=`73` follows=`0` hits=`[]`
- `OOOOOEOEE` abc=`[5, 1, 0]` Cbits=`422` v=`OEE` v_exp=`False` lemma35=`False` N0=`89` follows=`0` hits=`[]`
- `OOOOOEEOE` abc=`[5, 0, 1]` Cbits=`422` v=`EOE` v_exp=`False` lemma35=`False` N0=`60` follows=`0` hits=`[]`
- `OOOOEOOEE` abc=`[4, 2, 0]` Cbits=`130` v=`OOEE` v_exp=`False` lemma35=`False` N0=`120` follows=`0` hits=`[]`
- `OOOOEOEOE` abc=`[4, 1, 1]` Cbits=`130` v=`OEOE` v_exp=`False` lemma35=`False` N0=`81` follows=`0` hits=`[]`
- `OOOEOOOEE` abc=`[3, 3, 0]` Cbits=`38` v=`OOOEE` v_exp=`False` lemma35=`False` N0=`188` follows=`1` hits=`[]`
- `OOOEOOEOE` abc=`[3, 2, 1]` Cbits=`38` v=`OOEOE` v_exp=`False` lemma35=`False` N0=`126` follows=`0` hits=`[]`
- `OOEOOOOEE` abc=`[2, 4, 0]` Cbits=`10` v=`OOOOEE` v_exp=`True` lemma35=`True` N0=`374` follows=`0` hits=`[]`
- `OOEOOOEOE` abc=`[2, 3, 1]` Cbits=`10` v=`OOOEOE` v_exp=`True` lemma35=`True` N0=`250` follows=`0` hits=`[]`

- all tails fire: `True`
- all tables empty: `True`
- max N0: `374`
- follows witness (not a return): `{'word': 'OOOEOOOEE', 'n': 183, 'image': 1664}`

## Even-type observation (length 10/12 not opened)

- length `6` o_min=`4` max_E=`2` three_even=`False` four_even=`False`
- length `7` o_min=`5` max_E=`2` three_even=`False` four_even=`False`
- length `8` o_min=`6` max_E=`2` three_even=`False` four_even=`False`
- length `9` o_min=`6` max_E=`3` three_even=`True` four_even=`False`
- length `10` o_min=`7` max_E=`3` three_even=`True` four_even=`False`
- length `11` o_min=`7` max_E=`4` three_even=`True` four_even=`True`
- length `12` o_min=`8` max_E=`4` three_even=`True` four_even=`True`

- length 10 / four-even / n-search: `False` / `False` / `False`

## Lean

- `cycle_itinerary_formally_expanding`: `True`
- `no_cycle_odd_run_append_even`: `True`
- `oo_suffix_threshold`: `True`
- `ooo_suffix_threshold`: `True`
- `no_cycleMin_internal_even_threshold`: `True`
- `cycleMin_not_odd_even`: `True`
- `cycleMin_not_start_even`: `True`
- `cycle_last_even_interval`: `True`
- `cycle_trailing_evens_lt`: `True`
- `no_cycle_itinerary_length_le_six`: `True`
- `no_cycle_itinerary_oooeoe`: `True`
- `no_cycle_itinerary_ooooee`: `True`
- `no_cycle_itinerary_oooooee`: `True`
- `no_cycle_itinerary_ooooeoe`: `True`
- `no_cycle_itinerary_length_le_seven`: `True`
- `no_cycle_itinerary_ooooooeee`: `True`
- length eight open in census: `True`
- no length-nine theorem: `True`
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
- length_nine_cycles_impossible: `False`
- length_nine_lean_census: `False`
- four_even_opened: `False`
- induction_on_period: `False`
- induction_on_n: `False`
- no_escape_orbits: `False`

## Decision

**THREE_EVEN_PREFIX_CELL_GREEN**

length 9 has 28 three-even even-terminating expanding itineraries; last-internal suffix is always O^c so bootstrap still kills c>=2; the nine leftovers O^a E O^b E O^c E with a>=2 and c in {0,1} die by the odd-prefix cell tail (N0<=374) with empty CycleItinerary tables; a=2 remainders are the Lemma 3.5 words OOOOEE / OOOEOE.

This is not a halt result and not a length-9 census.
Two-even length-9 leftovers were not opened. Length 10 and
four-even words were not opened. Lean excludes `OOOOOOEEE`
only (`cycle_trailing_evens_lt`, `no_cycle_itinerary_ooooooeee`).

