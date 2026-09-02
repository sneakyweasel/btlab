# Juggler equality-word language and parity rigidity

Status: **EXTREMAL_FAMILY_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Mixed-word strictness remains REFUTED.
This page records whether envelope equality can use both letters.

## Branch budget

```text
Mathematical target     Must a realized equality word be E^k or O^k?
Novelty hypothesis      Exact perfect-power states keep the base parity,
                        so the itinerary cannot switch letters.
Falsifier               MIXED_EQUALITY_WORD_FOUND
Existing machinery      HasPowTwoDepth, exact E/O transitions, rigidity,
                        saturation budget, local-tightness probe
Maximum Phase-0 scope   Parity lemmas; monochromatic theorem; exact E^k/O^k
                        trajectories if cheap; mixed-word probe.
```

## Metadata

- domain layer: `n <= 10000`, `k <= 8`
- engine control layer modified: `False`
- classification: **EXTREMAL_FAMILY_GREEN**
- domain saturations: `99`
- mixed saturations: `0`
- prescribed mixed itineraries realized: `0`
- tower mixed count: `0`
- family witnesses match: `True`
- sorry-free: `True`

Envelope equality is exactly the two monochrome towers a^{2^k} --E^k--> a and a^{2^k} --O^k--> a^{3^k}.

## Witnesses

- word `O` at 9: base `3`,
  monochrome `True`
- word `EE` at 16: base `2`,
  trajectory `[16, 4, 2]`
- word `OO` at 81: base `3`
- mixed itinerary `EO` at 9: `False`

Exact even towers contract (`3^0 < 2^k`). Exact odd towers expand
(`3^k > 2^k`). Both saturate the one-sided envelope.

## Lean

- `even_iff_pow_even`: `True`
- `floorPower_sq_preserves_parity`: `True`
- `floorPower_pow_two_depth_preserves_parity`: `True`
- `power_bound_eq_implies_monochrome`: `True`
- `floorPower_iterate_even_pow_two_eq`: `True`
- `floorPower_iterate_odd_pow_two_eq`: `True`
- `follows_replicate_even_pow_two`: `True`
- `follows_replicate_odd_pow_two`: `True`
- `power_bound_eq_iff_extremal`: `True`
- `two_pow_two_pow_extremal_even`: `True`
- `three_pow_two_pow_extremal_odd`: `True`
- `odd_equality_three_pow_le`: `True`
- `PowerHeight` absent: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**EXTREMAL_FAMILY_GREEN**

Envelope equality is exactly the two monochrome towers a^{2^k} --E^k--> a and a^{2^k} --O^k--> a^{3^k}.

This is a finite-itinerary boundary statement, not a global halt result.

