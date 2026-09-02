# Juggler fixed-itinerary power inequalities

Status: **POWER_WORD_COUNTEREXAMPLE**

Standalone computational falsifier. Not a Research Engine control-layer
experiment, not a termination theorem, not a divergence theorem, and not
a parity-frequency theorem. `OOOEE` is a calibration example.

## Branch budget

```text
Mathematical target     Do fixed parity-word compositions obey the canonical
                        integer-power comparison T^k(n)^{2^k} ≶ n^{3^o} with
                        the sign of 3^o vs 2^k, independently of letter order?
Novelty hypothesis      The OOOEE exponents 32 vs 27 are the general (k,o)
                        shadow of floor-power composition, not a lucky word.
Falsifier               A realizing n whose first |w| bits are w and whose
                        power comparison has the opposite sign; or two words
                        with the same (k,o) and different behaviour.
Existing machinery      math.isqrt Juggler step; FloorPower.lean (OE, OO,
                        OOOEE); Phase-12 calibration on n in {3,25,39}.
Maximum Phase-0 scope   Exhaustive |w|<=8 on 1<=n<=N, plus a targeted
                        (k,o)=(9,6) scan for 729/512. No engine-control edits.
```

## Metadata

- n_max: `1000000`
- k_max: `8`
- targeted k=9 family 729/512: `True`
- engine control layer modified: `False`
- classification: **POWER_WORD_COUNTEREXAMPLE**
- two-sided hypothesis: `H1`
- one-sided hypothesis: `H1`
- one-sided floor composition holds: `True`
- contracting two-sided holds for n>=2: `False`
- mixed contracting two-sided holds for n>=2: `True`
- expanding two-sided fails: `True`
- Lean gate open: `True`
- Lean target word: `OOOEEEOO`
- Lean status: `PROVED`
- Lean theorem: `floorPower_oooeeeoo_eight_step_lt`

The two-sided exponent-only law fails: expanding itineraries obey the floor upper bound rather than the reverse inequality, and pure-even strict contraction fails with equality on perfect squares; the one-sided composition T^k(n)^{2^k} <= n^{3^o} holds independently of order.

## OOOEE calibration

| n | word | m = T^5(n) | m^32 ? n^27 | T^5(n)<n |
| --- | --- | --- | --- | --- |
| 3 | `OOOEE` | 2 | `<` | `True` |
| 25 | `OOOEE` | 15 | `<` | `True` |
| 39 | `OOOEE` | 21 | `<` | `True` |

## Closest formal exponent to 1

| k | o | 3^o / 2^k | |3^o-2^k| | regime |
| --- | --- | --- | --- | --- |
| 1 | 0 | `1/2` | 1 | contracting |
| 2 | 1 | `3/4` | 1 | contracting |
| 3 | 2 | `9/8` | 1 | expanding |
| 4 | 2 | `9/16` | 7 | contracting |
| 5 | 3 | `27/32` | 5 | contracting |
| 6 | 4 | `81/64` | 17 | expanding |
| 7 | 4 | `81/128` | 47 | contracting |
| 8 | 5 | `243/256` | 13 | contracting |

## Priority families

| ratio | (k,o) | regime | realized itineraries | two-sided survivors n>=2 | first n>1 failure |
| --- | --- | --- | --- | --- | --- |
| `27/32` | (5,3) | contracting | 10 | 10 | — |
| `243/256` | (8,5) | contracting | 49 | 49 | — |
| `9/8` | (3,2) | expanding | 3 | 0 | `EOO` at n=2 |
| `81/64` | (6,4) | expanding | 15 | 0 | `EEOOOO` at n=4 |
| `729/512` | (9,6) | expanding | 73 | 0 | `OOOEEEOOO` at n=3 |

## First two-sided counterexamples (n>1)

Expanding itineraries are expected to fail the reverse inequality because
floor composition only yields the upper bound `T^k(n)^{2^k} <= n^{3^o}`.

| word | n | k | o | exponent | m | expected | actual |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `O` | 3 | 1 | 1 | `3/2` | 5 | `>` | `<` |
| `E` | 4 | 1 | 0 | `1/2` | 2 | `<` | `=` |
| `OO` | 3 | 2 | 2 | `9/4` | 11 | `>` | `<` |
| `EE` | 16 | 2 | 0 | `1/4` | 2 | `<` | `=` |
| `EOO` | 2 | 3 | 2 | `9/8` | 1 | `>` | `<` |
| `OOO` | 3 | 3 | 3 | `27/8` | 36 | `>` | `<` |
| `OOE` | 5 | 3 | 2 | `9/8` | 6 | `>` | `<` |
| `OEO` | 15 | 3 | 2 | `9/8` | 18 | `>` | `<` |
| `EEE` | 256 | 3 | 0 | `1/8` | 2 | `<` | `=` |
| `EOOO` | 2 | 4 | 3 | `27/16` | 1 | `>` | `<` |
| `OOOE` | 3 | 4 | 3 | `27/16` | 6 | `>` | `<` |
| `OOEO` | 9 | 4 | 3 | `27/16` | 36 | `>` | `<` |
| `OEOO` | 19 | 4 | 3 | `27/16` | 140 | `>` | `<` |
| `OOOO` | 37 | 4 | 4 | `81/16` | 86818724 | `>` | `<` |
| `EEEE` | 65536 | 4 | 0 | `1/16` | 2 | `<` | `=` |
| `EOOOO` | 2 | 5 | 4 | `81/32` | 1 | `>` | `<` |
| `OOOOE` | 37 | 5 | 4 | `81/32` | 9317 | `>` | `<` |
| `OOEOO` | 69 | 5 | 4 | `81/32` | 44992 | `>` | `<` |
| `OOOEO` | 77 | 5 | 4 | `81/32` | 59436 | `>` | `<` |
| `OOOOO` | 115 | 5 | 5 | `243/32` | 4446080344234036 | `>` | `<` |
| `OEOOO` | 135 | 5 | 4 | `81/32` | 233046 | `>` | `<` |
| `EOOOOO` | 2 | 6 | 5 | `243/64` | 1 | `>` | `<` |
| `EEOOOO` | 4 | 6 | 4 | `81/64` | 1 | `>` | `<` |
| `OEOOEO` | 19 | 6 | 4 | `81/64` | 36 | `>` | `<` |

## One-sided floor composition

No counterexample to `T^k(n)^{2^k} <= n^{3^o}` was found on the
tested domain. Equality holds at the odd fixed point `n=1`.

## Same-count permutations

| (k,o) | ratio | regime | two-sided | one-sided | fail n>1 | ok n>1 |
| --- | --- | --- | --- | --- | --- | --- |
| (1,0) | `1/2` | contracting | H1 | H1 | `E` | — |
| (1,1) | `3/2` | expanding | H1 | H1 | `O` | — |
| (2,0) | `1/4` | contracting | H1 | H1 | `EE` | — |
| (2,1) | `3/4` | contracting | H1 | H1 | — | `EO`,`OE` |
| (2,2) | `9/4` | expanding | H1 | H1 | `OO` | — |
| (3,0) | `1/8` | contracting | H1 | H1 | `EEE` | — |
| (3,1) | `3/8` | contracting | H1 | H1 | — | `EEO`,`EOE`,`OEE` |
| (3,2) | `9/8` | expanding | H1 | H1 | `EOO`,`OEO`,`OOE` | — |
| (3,3) | `27/8` | expanding | H1 | H1 | `OOO` | — |
| (4,0) | `1/16` | contracting | H1 | H1 | `EEEE` | — |
| (4,1) | `3/16` | contracting | H1 | H1 | — | `EEEO`,`EEOE`,`EOEE`,`OEEE` |
| (4,2) | `9/16` | contracting | H1 | H1 | — | `EEOO`,`EOEO`,`EOOE`,`OEEO` |
| (4,3) | `27/16` | expanding | H1 | H1 | `EOOO`,`OEOO`,`OOEO`,`OOOE` | — |
| (4,4) | `81/16` | expanding | H1 | H1 | `OOOO` | — |
| (5,0) | `1/32` | contracting | H1 | H1 | — | `EEEEE` |
| (5,1) | `3/32` | contracting | H1 | H1 | — | `EEEEO`,`EEOEE`,`EOEEE`,`OEEEE` |
| (5,2) | `9/32` | contracting | H1 | H1 | — | `EEEOO`,`EEOEO`,`EEOOE`,`EOEEO` |
| (5,3) | `27/32` | contracting | H1 | H1 | — | `EEOOO`,`EOEOO`,`EOOEO`,`EOOOE` |
| (5,4) | `81/32` | expanding | H1 | H1 | `EOOOO`,`OEOOO`,`OOEOO`,`OOOEO` | — |
| (5,5) | `243/32` | expanding | H1 | H1 | `OOOOO` | — |
| (6,1) | `3/64` | contracting | H1 | H1 | — | `EEEEEO`,`EEOEEE`,`EOEEEE`,`OEEEEE` |
| (6,2) | `9/64` | contracting | H1 | H1 | — | `EEEEOO`,`EEEOOE`,`EEOEEO`,`EEOEOE` |
| (6,3) | `27/64` | contracting | H1 | H1 | — | `EEEOOO`,`EEOEOO`,`EEOOEO`,`EEOOOE` |
| (6,4) | `81/64` | expanding | H1 | H1 | `EEOOOO`,`EOEOOO`,`EOOEOO`,`EOOOEO` | — |
| (6,5) | `243/64` | expanding | H1 | H1 | `EOOOOO`,`OEOOOO`,`OOEOOO`,`OOOEOO` | — |
| (6,6) | `729/64` | expanding | H1 | H1 | `OOOOOO` | — |
| (8,4) | `81/256` | contracting | H1 | H1 | — | `EEEEOOOO`,`EEOEEOOO`,`EEOEOOEO`,`EEOOOEEO` |
| (8,5) | `243/256` | contracting | H1 | H1 | — | `EEEOOOOO`,`EOEOEOOO`,`EOEOOEOO`,`EOEOOOEO` |
| (9,6) | `729/512` | expanding | H1 | H1 | `EEEOOOOOO`,`EOEOOEOOO`,`EOEOOOEOO`,`EOEOOOOOE` | — |

### OE vs EO

Both have formal exponent `3/4`. Two-sided: H1. One-sided: H1.

- two-sided fail n>1: []
- two-sided ok n>1: ['EO', 'OE']

## Power-gap sample

Raw `Delta = n^{3^o} - T^k(n)^{2^k}` is computed only when both
powers fit in 4096 bits. Sign changes of this gap would falsify
the one-sided composition.

- contracting itineraries with a raw delta: 292
- delta sign changes: none

- `EE`: min_delta=0 at n=16; equalities=15; sign_change=False
- `OE`: min_delta=35 at n=11; equalities=0; sign_change=False
- `EO`: min_delta=7 at n=2; equalities=0; sign_change=False
- `OOOEE`: min_delta=7621302517691 at n=3; equalities=0; sign_change=False

## Exceptional state

`T(1)=1`. Every all-odd itinerary is realized at `n=1` with equality
`1^{2^k} = 1^{3^k}`. Strict two-sided inequalities fail; the one-sided
upper bound holds. This is not a termination theorem.

Pure-even words (`o=0`) have canonical comparison `T^k(n)^{2^k} < n`.
Equality holds on the infinite family of even perfect-power towers
(for example `E` at every even square, `EE` at `n=16`, `EEE` at `n=256`).
That family is definitional `isqrt` exactness, not a mixed-word
composition failure, and it is not a finite exceptional set.

## Lean gate

Open. Representative word `OOOEEEOO` of length 8 with ratio `243/256`, first realized at n=3. Lean `PROVED`: `floorPower_oooeeeoo_eight_step_lt`. Not a general-word theorem.

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`

## Decision

**POWER_WORD_COUNTEREXAMPLE**

The two-sided exponent-only law fails: expanding itineraries obey the floor upper bound rather than the reverse inequality, and pure-even strict contraction fails with equality on perfect squares; the one-sided composition T^k(n)^{2^k} <= n^{3^o} holds independently of order.

