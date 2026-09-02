# Juggler floor-power equality rigidity

Status: **MIXED_EQUALITY_FOUND**

Standalone application phase. Not a Research Engine experiment and
not a termination theorem. The weak envelope `T_w(n)^{2^k} <= n^{3^o}`
remains. This page records whether mixed-word equality can occur.

## Branch budget

```text
Mathematical target     Does every odd step make the composed bound
                        strict for n>=2, forbidding mixed-word equality?
Novelty hypothesis      Mixed-word equality does not occur for n>=2.
Falsifier               A realized mixed itinerary with T_w(n)^{2^k} = n^{3^o}.
Existing machinery      power_itineraries cmp_pow; PowerBound composition.
Maximum Phase-0 scope   Mixed-equality search; one-step odd analysis;
                        stop strictness API if a witness appears.
```

## Metadata

- deep layer: `n <= 10000`, `k <= 12`
- wide layer: `n <= 1000000`, `k <= 8`
- odd squares through: `100000000`
- perfect-power targets through: `1000000000`
- bit cap on itinerary states: `8192`
- engine control layer modified: `False`
- classification: **MIXED_EQUALITY_FOUND**
- mixed equality hits: `15996`
- hits containing E: `0`
- near-critical mixed equalities: `0`
- alternating mixed equalities: `0`

A realized mixed itinerary attains the envelope: odd n that is a perfect square forces T(n)^2 = n^3, so n^{3/2} is an integer.

## Smallest mixed-equality witness

- word: `O`
- n: `9`
- k: `1`
- odd_count: `1`
- T^k(n): `27`
- left_power: `27^2`
- right_power: `9^3`
- parity_trace: `[9, 27]`

Phase B: `T(n)^2 < n^3` fails for odd `n>=3` exactly when `n` is a
square, because then `n^{3/2}` is an integer. The working hypothesis
that every odd step is locally strict is **REFUTED**.

## Both-letter words

No equality with both `O` and `E` was found on the searched domain.

A tight odd step from an odd square produces an odd image, so an even
letter cannot immediately follow a tight odd step. Inserting `E`
appears to require a slack odd step, which the composition then keeps
strict. That observation is **OBSERVATION**, not a theorem of this phase.

Near-critical exponent gaps (`3^o ~ 2^k`) are a different comparison:
they decide contraction of the weak bound, not whether the floor
composition is itself an equality. No mixed near-critical equality
was found.

## Lean

- `floorPower_odd_sq_eq_cube_of_sq`: odd `m` implies `T(m^2)^2 = (m^2)^3`.
- `floorPower_nine_odd_eq`: word `O` at `n=9`.
- `mixed_word_power_lt` is absent: the strict mixed-word claim is false.
- `floorPower_odd_sq_lt_cube` is absent: odd `n>=3` need not be strict.
- `PowerBoundStrict` is absent.

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**MIXED_EQUALITY_FOUND**

A realized mixed itinerary attains the envelope: odd n that is a perfect square forces T(n)^2 = n^3, so n^{3/2} is an integer.

Stop the mixed-strictness generalization. Do not add `mixed_word_power_lt`.

