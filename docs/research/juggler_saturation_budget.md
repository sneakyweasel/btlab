# Juggler exact perfect-power dynamics and saturation budget

Status: **SATURATION_BUDGET_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Mixed-word strictness remains REFUTED.
This page records the 2-adic perfect-power budget of envelope
equality.

## Branch budget

```text
Mathematical target     Does k consecutive exact envelope branches require
                        the start to be a 2^k-th power?
Novelty hypothesis      Each exact E/O step consumes one unit of 2-adic
                        perfect-power depth.
Falsifier               POWER_TWO_DEPTH_COUNTEREXAMPLE.
Existing machinery      PowerBoundEq, power_bound_eq_implies_square,
                        floorPower_of_even_sq / floorPower_of_odd_sq,
                        isSquare_pow_three_iff.
Maximum Phase-0 scope   Exact a^(2^r) transitions; HasPowTwoDepth drop
                        lemmas; budget theorem if it holds; square-depth
                        probe without cmp_pow or PowerHeight.
```

## Metadata

- domain layer: `n <= 10000`, `k <= 8`
- prescribed-word layer: `k <= 6`
- engine control layer modified: `False`
- classification: **SATURATION_BUDGET_GREEN**
- depth status: **POWER_TWO_DEPTH_GREEN**
- domain saturations: `99`
- domain counterexamples: `0`
- mixed saturations on the domain: `0`
- contracting saturations on the domain: `50`
- prescribed words realized in bound: `6`
- prescribed mixed realizations: `0`
- tower counterexamples: `0`
- sorry-free: `True`

Each exact branch consumes one unit of 2-adic perfect-power depth, so a realized equality itinerary of length k forces the start to be a 2^k-th power.

## Local transitions

If `n = a^{2^r}` and `r >= 1`, an exact even branch is
`a^{2^{r-1}}` and an exact odd branch is `a^{3 · 2^{r-1}}`.
Both drop one factor of `2` from the exponent. The next state is
again a square iff `r >= 2`, or iff the remaining base is itself
a square when `r = 1`.

- word `O` at 9: depth `1`,
  length `1`,
  independent `True`
- word `EE` at 16: depth `2`,
  length `2`,
  trajectory `[16, 4, 2]`
- word `OO` at 81: depth `2`,
  length `2`
- word `EEE` at 256: depth `3`,
  length `3`
- depth 1 at 36: saturates `E`
  and then stops; the image 6 is not a square

Exact steps preserve parity, so a mixed itinerary cannot saturate.
All-even equality is formally contracting and meets the lower
bound `2^{2^k}` at the towers `2^{2^k}`.

## Lean

- `floorPower_of_pow_two_depth_even`: `True`
- `floorPower_of_pow_two_depth_odd`: `True`
- `hasPowTwoDepth_even_exact`: `True`
- `hasPowTwoDepth_odd_exact`: `True`
- `hasPowTwoDepth_ge_two_image_square`: `True`
- `hasPowTwoDepth_of_cube`: `True`
- `localsTight_implies_power_bound_eq`: `True`
- `power_bound_eq_implies_pow_two_depth`: `True`
- `power_bound_eq_contracts_pow_two_lb`: `True`
- `HasPowTwoDepth` definition: `True`
- `PowerHeight` absent: `True`
- `mixed_word_power_lt` absent: `True`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**SATURATION_BUDGET_GREEN**

Each exact branch consumes one unit of 2-adic perfect-power depth, so a realized equality itinerary of length k forces the start to be a 2^k-th power.

This is a finite local budget, not a global halt result.

