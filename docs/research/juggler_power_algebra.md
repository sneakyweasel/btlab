# Juggler finite-itinerary power algebra and equality rigidity

Status: **EQUALITY_RIGIDITY_GREEN**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. Mixed-word strictness remains REFUTED.
This page records local square characterizations and equality
propagation of the one-sided envelope.

## Branch budget

```text
Mathematical target     Does global envelope equality for a realized finite itinerary
                        force every local branch inequality to be tight, and is
                        each local tightness equivalent to the branch input
                        being a perfect square?
Novelty hypothesis      Equality is a rigid chain of exact local square
                        conditions, not mixed-word strictness (already REFUTED).
Falsifier               LOCAL_SQUARE_EQ_FALSE or GLOBAL_EQ_PROPAGATION_FALSE.
Existing machinery      PowerBound, power_bound_follows / power_bound_contracts,
                        floorPower_odd_sq_eq_cube_of_sq, Nat.sqrt, powers_equal.
Maximum Phase-0 scope   Local iff-square theorems; equality-propagation theorem;
                        square-state corollary; square/root computational probe;
                        thin power_bound_word alias.
```

## Metadata

- itinerary layer: `n <= 10000`, `k <= 8`
- local iff-square layer: `n <= 1000000`
- engine control layer modified: `False`
- classification: **EQUALITY_RIGIDITY_GREEN**
- local-square mismatches: `0`
- propagation mismatches (tiny independent check): `0`
- predicted equalities: `118`
- predicted equalities containing O: `62`
- predicted both-letter equalities: `0`
- sorry-free: `True`

Local branch equality is equivalent to a perfect square, and global envelope equality forces every local inequality to be tight, hence every relevant state is a square.

## Local equality

Even `T(n)^2 = n` iff `n` is a square. Odd `T(n)^2 = n^3` iff `n` is a
square. Search uses `isqrt` only; it does not construct `n^{3^o}`.

- even equal count on the iff layer: `500`
- odd equal count on the iff layer: `500`

## Structured witnesses

- word `O` at 9: predicted `True`,
  squares `[True]`,
  independent `True`
- word `EE` at 16: predicted `True`,
  squares `[True, True]`,
  trajectory `[16, 4, 2]`
- word `OO` at 81: predicted `True`,
  squares `[True, True]`

Relevant states are branch inputs. The images `27` and `2` need not be squares.

## Lean

- `power_bound_word`: `True`
- `floorPower_even_sq_eq_iff_square`: `True`
- `floorPower_odd_sq_eq_cube_iff_square`: `True`
- `power_bound_eq_of_append_even`: `True`
- `power_bound_eq_of_append_odd`: `True`
- `power_bound_eq_implies_local_eq`: `True`
- `power_bound_eq_implies_square`: `True`
- `power_bound_follows`: `True`
- `power_bound_contracts`: `True`
- `PowerBoundEq` definition: `True`
- `mixed_word_power_lt` absent: `True`
- `PowerBoundStrict` absent: `True`
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

**EQUALITY_RIGIDITY_GREEN**

Local branch equality is equivalent to a perfect square, and global envelope equality forces every local inequality to be tight, hence every relevant state is a square.

Do not census equality words. Do not replace contraction by a strict floor theorem.

