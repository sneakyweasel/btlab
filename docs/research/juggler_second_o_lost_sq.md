# Juggler second O loses the square cell

Status: **SECOND_O_LOST_SQ_GREEN**

Standalone application phase. Not a Research Engine experiment
and not a termination theorem. The second O after the new OO
is the first lost square-cell letter on this CE spine.

## Branch budget

```text
Mathematical target     After 1517 -> 124475, does the
                        second O still lie below n^2?
Novelty hypothesis      19683 > 16384 loses the square;
                        19683 < 24576 keeps the cube
Existing machinery      next-O square; power_bound_word
Maximum Phase-0 scope   lost-square decide; cube envelope;
                        1517 corridor; no letter chain
```

## Metadata

- basin: `[1]`
- engine control layer modified: `False`
- classification: **SECOND_O_LOST_SQ_GREEN**
- sorry-free: `True`
- loses square 19683>16384: `True`
- cube gap 19683<24576: `True`
- 1517 u: `43916043`
- 1517 in [n^2, n^3): `True`

the second O loses the square cell (19683 > 16384) and keeps the cube (19683 < 24576); 1517 lands odd in [n^2, n^3).

## Lean

- `itineraryOOEOOEOOEOEOO`: `True`
- `ooeooeooeoeoo_loses_square`: `True`
- `follows_ooeooeooeoeoo_image_lt_cube`: `True`
- `minimal_ooeooeooeoeo_follows_o`: `True`
- `minimal_ooeooeooeoeo_not_even`: `True`

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
- second_o_below_sq: `False`
- length_eleven_census: `False`

## Decision

**SECOND_O_LOST_SQ_GREEN**

the second O loses the square cell (19683 > 16384) and keeps the cube (19683 < 24576); 1517 lands odd in [n^2, n^3).

This is not a halt result and not a length-11 census.

