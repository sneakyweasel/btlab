# Juggler prefix-NC arithmetic admissibility

Status: **PREFIX_NC_ARITHMETIC_COMPLEX**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. A prefix-NC word has every
prefix exponent gap `G_j = 2^j - 3^{o_j} ≤ 0`. The question is
whether exact floor-cell pullback empties the realizing set.

## Branch budget

```text
Mathematical target     Does arithmetic realizability eliminate
                        long mixed prefix-NC words?
Novelty hypothesis      backward floor cells empty or shrink A_NC
Falsifier               existing cells rewritten; horizon ≠ L;
                        realized mixed itineraries survive
Existing machinery      inverse-floor iff, odd_preimage_unique,
                        prefix_nc_words, compensated contraction
Maximum Phase-0 scope   pullback on mixed k<=8 plus known witnesses
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **PREFIX_NC_ARITHMETIC_COMPLEX**
- secondary: `None`
- sorry-free: `True`
- algorithm: `prefix-nc-admissibility-v1`

backward constraints are the existing even/odd cells; long mixed prefix-NC words remain realizable; empty-over-image-24 is not unrealizable; no jointly preserved obstruction.

## Window

- mixed prefix-NC words `k<=8`: `43`
- realized with `n<=800`: `43`
- unrealized in that forward window: `0`
- empty over images `1..24`: `41`
- truncated pullbacks: `0`
- O-extension shrinks: `True`
- E-extension widens: `False`
- only O^k E shadows survive: `False`
- search horizon is not L: `True`

## Known witnesses

- `OOE` min=`5` empty_over_image=`False` truncated=`False` compensated=`False` E-count=`1`
- `OOOOEE` min=`271` empty_over_image=`False` truncated=`True` compensated=`None` E-count=`2`
- `OOOOEOOOEE` min=`37` empty_over_image=`False` truncated=`True` compensated=`None` E-count=`3`
- `OOEOOOOOOO` min=`173` empty_over_image=`True` truncated=`False` compensated=`None` E-count=`1`
- `OOOOEOEOOO` min=`103` empty_over_image=`True` truncated=`False` compensated=`None` E-count=`2`
- `OOOEOOOOOE` min=`113` empty_over_image=`True` truncated=`False` compensated=`None` E-count=`2`
- `OOOOOOEOEE` min=`163` empty_over_image=`False` truncated=`True` compensated=`None` E-count=`3`
- `OOOOEOOOOEE` min=`2127` empty_over_image=`False` truncated=`True` compensated=`None` E-count=`3`

## Lean

- `floor_sqrt_eq_iff_sq_interval`: `True`
- `floorPower_even_eq_iff_sq_interval`: `True`
- `floorPower_odd_eq_iff_cube_interval`: `True`
- `odd_preimage_unique`: `True`
- `power_bound_compensated_contracts`: `True`
- new PrefixNCAdmissibility file absent: `True`
- ResidualStep not extended: `True`
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
- search_horizon_is_L: `False`
- odd_odd_chains_bounded: `False`
- prefix_nc_words_unrealizable: `False`
- scalar_must_grow: `False`

## Decision

**PREFIX_NC_ARITHMETIC_COMPLEX**

backward constraints are the existing even/odd cells; long mixed prefix-NC words remain realizable; empty-over-image-24 is not unrealizable; no jointly preserved obstruction.

A dangerous finite itinerary is not a dangerous infinite
trajectory. A search-horizon depth is not a bound L.

