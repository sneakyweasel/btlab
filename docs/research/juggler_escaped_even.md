# Juggler escaped even after third OOE

Status: **ESCAPED_EVEN_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. After a third OOE, an escaped
even still has an OE landing below n^2. This is not a
length-11 cycle census.

## Branch budget

```text
Mathematical target     After a 429-type third OOE with
                        even T(y) >= n^2, is there a
                        CE-capable constraint on that even?
Novelty hypothesis      the OE landing stays below n^2
Existing machinery      third-OOE square; power_bound;
                        even_floorPower_lt_iff
Maximum Phase-0 scope   11-letter square; CE even-trap;
                        429/1517; no length-11 census
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **ESCAPED_EVEN_GREEN**
- sorry-free: `True`
- square gap 2187<4096: `True`
- escaped even: `3`
- even w / odd w: `2` / `1`
- 429 w: `646`
- 1517 w: `2493`

OOEOOEOOEOE < n^2; CE even OE landing drops; 429 dies by even w; 1517 survives with odd w.

## Lean

- `itineraryOOEOOEOOEOE`: `True`
- `follows_ooeooeooeoe_image_lt_sq`: `True`
- `minimal_ooeooeooe_follows_o`: `True`
- `minimal_ooeooeooeoe_not_even_landing`: `True`
- `minimal_ooeooeooe_not_even_landing`: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- no_escape: `False`
- cycles_impossible: `False`
- uniform_escaped_drop: `False`
- length_eleven_census: `False`

## Decision

**ESCAPED_EVEN_GREEN**

OOEOOEOOEOE < n^2; CE even OE landing drops; 429 dies by even w; 1517 survives with odd w.

This is not a halt result and not a length-11 census.

