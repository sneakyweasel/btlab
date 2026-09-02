# Juggler fixed cycle-itinerary size bounds

Status: **CYCLE_BOUND_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. Cycle return is not envelope
equality. Lower growth still produces `n^{3^o-2^k} ≤ D_w`.

## Branch budget

```text
Mathematical target     CycleItinerary ⇒ n^{3^o-2^k} ≤ D_w and an explicit n ≤ B_w
Novelty hypothesis      lower-growth turns cycle return into a finite size bound
Falsifier               a cycle with n > lowerDenom w; or PowerBoundEq as the cycle attack
Existing machinery      lower_growth_word, cycle_strict_envelope, EOO cells
Maximum Phase-0 scope   CycleItinerary; size bound; exclude contracting, O, OO, EOO; bound OOE
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **CYCLE_BOUND_GREEN**
- secondary: `['CYCLE_WORD_EXCLUDED']`
- sorry-free: `True`

cycle return implies n^{3^o-2^k} ≤ D_w and n ≤ D_w; contracting itineraries, O, OO, and EOO are excluded; OOE is finite-bounded.

## Itinerary bounds

- `O` expand=`True` D=`4` e=`1` n≤`4` searched=`4` hits=`[]`
- `E` expand=`False` D=`4` e=`-1` n≤`None` searched=`0` hits=`[]`
- `OE` expand=`False` D=`64` e=`-1` n≤`None` searched=`0` hits=`[]`
- `EO` expand=`False` D=`1024` e=`-1` n≤`None` searched=`0` hits=`[]`
- `OO` expand=`True` D=`1024` e=`5` n≤`4` searched=`4` hits=`[]`
- `OOO` expand=`True` D=`274877906944` e=`19` n≤`4` searched=`4` hits=`[]`
- `OOE` expand=`True` D=`262144` e=`1` n≤`262144` searched=`262144` hits=`[]`
- `OEO` expand=`True` D=`67108864` e=`1` n≤`67108864` searched=`3000` hits=`[]`
- `EOO` expand=`True` D=`274877906944` e=`1` n≤`274877906944` searched=`0` hits=`[]`

## Lean

- `CycleItinerary`: `True`
- `cycle_itinerary_formally_expanding`: `True`
- `cycle_itinerary_not_contracting`: `True`
- `cycle_lower_growth`: `True`
- `cycle_pow_le_lowerDenom`: `True`
- `cycle_le_lowerDenom`: `True`
- `no_cycle_itinerary_odd`: `True`
- `no_cycle_itinerary_oo`: `True`
- `no_cycle_itinerary_eoo`: `True`
- `cycle_ooe_le_lowerDenom`: `True`
- certificate unchanged: `True`
- `PowerHeight` absent: `True`
- FloorPower not rewritten: `True`
- PowerBoundEq not used as cycle attack: `True`
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
- all_odd_orbit: `False`
- finite_progress_for_all: `False`
- cycles_impossible: `False`
- cycle_is_envelope_equality: `False`
- power_bound_eq_forbids_cycles: `False`

## Decision

**CYCLE_BOUND_GREEN**

cycle return implies n^{3^o-2^k} ≤ D_w and n ≤ D_w; contracting itineraries, O, OO, and EOO are excluded; OOE is finite-bounded.

This is not a halt result. Cycles are not proved impossible.
Cycle return is not envelope equality.

