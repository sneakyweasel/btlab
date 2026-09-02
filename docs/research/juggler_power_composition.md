# Juggler one-sided floor-power composition

Status: **POWER_COMPOSITION_GREEN**

Standalone application phase. Not a Research Engine experiment, not a
termination theorem, and not a parity-frequency theorem. The Phase-13
two-sided exponent law remains `POWER_WORD_COUNTEREXAMPLE`. This page
records whether the surviving one-sided envelope is a finite-itinerary theorem.

## Branch budget

```text
Mathematical target     Does every realized finite parity itinerary satisfy
                        T_w(n)^{2^k} <= n^{3^o} by inductive floor composition?
Novelty hypothesis      OOOEE / OOOEEEOO are instances of one weak bound plus
                        an exponent-gap contraction corollary.
Falsifier               A realized (w,n) with T_w(n)^{2^k} > n^{3^o}.
Existing machinery      power_itineraries cmp_pow; FloorPower even/odd square bounds;
                        pow_sq_le / pow_sq_le_cube.
Maximum Phase-0 scope   Near-equality scan reusing power_itineraries; then a tiny
                        Lean API if the weak bound survives. No engine edits.
```

## Metadata

- n_max (near-equality focus): `50000`
- k_max: `8`
- engine control layer modified: `False`
- classification: **POWER_COMPOSITION_GREEN**
- Lean empty/even/odd/follows/contracts: `True`/`True`/`True`/`True`/`True`
- sorry-free: `True`

The weak bound is an inductive floor-power composition on realized finite itineraries; strict contraction follows from the exponent gap at n>=2.

## Weak composition law

`PowerBound m n k o` means `m^{2^k} <= n^{3^o}`.

- empty: `PowerBound n n 0 0`
- append even: `(k,o) -> (k+1,o)` via `T(m)^2 <= m`
- append odd: `(k,o) -> (k+1,o+1)` via `T(m)^2 <= m^3`

Numerical append-even check: `True`.
Numerical append-odd check: `True`.

## Near-equality

- onesided failures in the focus scan: `0`
- mixed-word equalities: `[]`
- states immediately above square towers still one-sided: `True`

Smallest positive mixed gaps (raw `G_w` when it fits in 4096 bits):

| word | n | G_w | m |
| --- | --- | --- | --- |
| `EO` | 2 | 7 | 1 |
| `OE` | 11 | 35 | 6 |
| `EEO` | 4 | 63 | 1 |
| `OEE` | 7 | 87 | 2 |
| `OEEE` | 7 | 342 | 1 |
| `EOO` | 2 | 511 | 1 |
| `EEEO` | 16 | 4095 | 1 |
| `EOE` | 50 | 59464 | 4 |
| `EOEE` | 50 | 59464 | 2 |
| `OEEEE` | 41 | 68920 | 1 |
| `EOEEE` | 50 | 124999 | 1 |
| `EEOO` | 4 | 262143 | 1 |

Equality observed in the focus scan is the square-tower / `n=1` family,
not mixed itineraries. The weak theorem is therefore non-strict by design.

## Strict corollary

If `3^o < 2^k` and `n>=2`, then `n^{3^o} < n^{2^k}`, so the weak bound
implies `T_w(n) < n`. At `n=1` both powers are 1 and the gap is silent.

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**POWER_COMPOSITION_GREEN**

The weak bound is an inductive floor-power composition on realized finite itineraries; strict contraction follows from the exponent gap at n>=2.

