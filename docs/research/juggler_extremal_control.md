# Juggler extremal control and realizability gap

Status: **CONTROL_FRONTIER_GREEN**

Standalone deterministic-control layer on the exact Juggler floor-power
map. `L = log log x` is a diagnostic. It never defines the map. This is
not a termination theorem. Closed symbolic-compression branches stay
closed. The parked statistical model is used only as an extremal
target, not as a new census.

Every result below is labelled
`EXACT CONTROL RESULT` | `EXACT COMPUTATION` | `COMPUTATIONALLY OBSERVED`
| `MODEL PREDICTION` | `CANDIDATE CONJECTURE` | `COUNTEREXAMPLE`.

## 1. Exact control model

Ignoring floor corrections, the diagnostic

```text
L = log log x
```

has idealized increments

```text
O: a = log(3/2)
E: b = log(1/2)
```

For a binary control word the cumulative displacement is

```text
S_j = o_j log 3 − j log 2 = log(3^{o_j} / 2^j).
```

The comparison that does not use floating logarithms is

```text
S_j >= 0  ⇔  3^{o_j} >= 2^j
S_k <  0  ⇔  3^o     <  2^k.
```

Label: **EXACT CONTROL RESULT**. This is the ideal control process, not
the exact map `J`. The identity `S_k = o log 3 − k log 2` is the known
exponent surplus rewritten in additive form and is **not** promoted.

The first-return control constraint is

```text
S_j >= 0 for j < k,     S_k < 0.
```

The last letter is necessarily `E`: an `O` step cannot cross below
zero from a nonnegative height. The landing corridor is therefore

```text
0 <= S_{k-1} < log 2
⇔  2^{k-1} <= 3^o < 2^k.
```

Label: **EXACT CONTROL RESULT**. The interval for `o` has length
`log 2 / log 3 < 1`, so there is at most one admissible odd-count.

Admissible horizons in `k = 1..50`: [1, 2, 4, 5, 7, 8, 10, 12, 13, 15, 16, 18, 20, 21, 23, 24, 26, 27, 29, 31, 32, 34, 35, 37, 39, 40, 42, 43, 45, 46, 48, 50].
Inadmissible horizons (empty corridor): [3, 6, 9, 11, 14, 17, 19, 22, 25, 28, 30, 33, 36, 38, 41, 44, 47, 49].
Label: **EXACT CONTROL RESULT**.

## 2. Ideal first-return optimization

The useful objective is not raw endpoint height (all-`O` wins that
trivially). It is the maximum peak among first-return controls of
length `k`:

```text
H(w) = max_j S_j(w)
H_k^* = max H(w) over first-return itineraries of length k.
```

For fixed admissible `o`, front-loading every `O` uniquely maximises
the peak: any earlier `E` strictly lowers every later height, and any
peak taken with fewer than `o` odds is at most `(o-1) log(3/2)`.
The unique optimiser is therefore the bang-bang word

```text
O^o E^{k-o},     o = o_k^*,     H_k^* = o_k^* log(3/2).
```

Equivalently, parameterised by the odd-run length,

```text
k(o) = min{k : 2^{k-1} <= 3^o < 2^k}
e(o) = k(o) − o
w_o  = O^o E^{e(o)}.
```

A finite-horizon DP on the state `(j, o_j)` with `k <= 24` reproduces
this itinerary and peak at every horizon. Label: **EXACT CONTROL RESULT**.
DP agreement: `True`.

This is not the 2025 large-deviation optimiser. The Cramér tilt for
rare *ascent* under fair coins is `p^* = 3/4`, slope
`a^* = (3/4) log 3 − log 2 ≈ 0.130812`. That path has positive
drift and is not a first-return path. The deterministic first-return
odd frequency is `o/k → log 2 / log 3 ≈ 0.630930`. Label:
**EXACT CONTROL RESULT** for the distinction;
**MODEL PREDICTION** for `p^*` itself.

## 3. Ideal control frontier

| k | admissible | o | word | peak | endpoint |
|---|------------|---|------|------|----------|
| 1 | True | 0 | `E` | 0.000000 | -0.693147 |
| 2 | True | 1 | `OE` | 0.405465 | -0.287682 |
| 3 | False | — | `—` | — | — |
| 4 | True | 2 | `OOEE` | 0.810930 | -0.575364 |
| 5 | True | 3 | `OOOEE` | 1.216395 | -0.169899 |
| 6 | False | — | `—` | — | — |
| 7 | True | 4 | `OOOOEEE` | 1.621860 | -0.457581 |
| 8 | True | 5 | `OOOOOEEE` | 2.027326 | -0.052116 |
| 9 | False | — | `—` | — | — |
| 10 | True | 6 | `OOOOOOEEEE` | 2.432791 | -0.339798 |
| 11 | False | — | `—` | — | — |
| 12 | True | 7 | `OOOOOOOEEEEE` | 2.838256 | -0.627480 |
| 13 | True | 8 | `OOOOOOOOEEEEE` | 3.243721 | -0.222015 |
| 14 | False | — | `—` | — | — |
| 15 | True | 9 | `OOOOOOOOOEEEEEE` | 3.649186 | -0.509697 |
| 16 | True | 10 | `OOOOOOOOOOEEEEEE` | 4.054651 | -0.104232 |
| 17 | False | — | `—` | — | — |
| 18 | True | 11 | `OOOOOOOOOOOEEEEEEE` | 4.460116 | -0.391914 |
| 19 | False | — | `—` | — | — |
| 20 | True | 12 | `OOOOOOOOOOOOEEEEEEEE` | 4.865581 | -0.679596 |
| 24 | True | 15 | `OOOOOOOOOOOOOOOEEEEEEEEE` | 6.081977 | -0.156348 |
| 25 | False | — | `—` | — | — |
| 32 | True | 20 | `OOOOOOOOOOOO…EEEEEEEE` | 8.109302 | -0.208464 |
| 40 | True | 25 | `OOOOOOOOOOOO…EEEEEEEE` | 10.136628 | -0.260580 |
| 48 | True | 30 | `OOOOOOOOOOOO…EEEEEEEE` | 12.163953 | -0.312696 |
| 50 | True | 31 | `OOOOOOOOOOOO…EEEEEEEE` | 12.569418 | -0.600378 |

Longer admissible rows through `k = 50` are in
`data/research/juggler/extremal_control/ideal_frontier.csv`.
Label: **EXACT CONTROL RESULT**.

The value function of the ideal DP is closed-form: from the origin,
`V_k(0) = H_k^*` when the corridor is nonempty, and `−∞` otherwise.
From a later state `(j, o)` with `o <= o_k^*` and `S_j >= 0`, the
remaining optimiser is still bang-bang in the unused odds; the
achievable peak is strictly less than `H_k^*` as soon as an `E` has
already been used.

## 4. Exact Juggler frontier

Exact first-return walks use `floor_power` / `isqrt` only.
`A_i = log log x_i − log log n` when both arguments are at least 3.

Phase 0 window: `2 <= n <= 4000`, complete
returns `3999` of `3999`
starts. Label: **EXACT COMPUTATION**.

Bang-bang first-return words realized in the window (smallest `n`):

| k | o | n | word |
|---|---|---|------|
| 1 | 0 | 2 | `E` |
| 2 | 1 | 7 | `OE` |
| 4 | 2 | 5 | `OOEE` |
| 5 | 3 | 3 | `OOOEE` |
| 7 | 4 | 271 | `OOOOEEE` |
| 8 | 5 | 129 | `OOOOOEEE` |
| 10 | 6 | 1589 | `OOOOOOEEEE` |
| 12 | 7 | 289 | `OOOOOOOEEEEE` |
| 13 | 8 | 591 | `OOOOOOOOEEEEE` |

Label: **EXACT COMPUTATION**. `n = 3` realizes the `k = 5` optimiser
`OOOEE`. `n = 5` realizes `OOEE`. `n = 7` is the smallest `OE`.
`n = 9` realizes the same `(k, o) = (5, 3)` with the split word
`OOEOE`, which is a valid ideal first-return but is not peak-optimal.

The best *realized* peak at a horizon `k` is the actual frontier.
When a bang-bang realizer exists it is the actual peak winner at that
`k`, up to floor error in `A`. When no bang-bang realizer is found,
the actual winner is a mixed itinerary.

## 5. Control gaps

Peak and return gaps are kept separate.

```text
control_gap_peak(k)   = H_k^* − max A_i
control_gap_return(k) = S_k^{ideal} − A_τ
```

| k | ideal peak | actual peak | gap | witness n | bang-bang n |
|---|------------|-------------|-----|-----------|-------------|
| 1 | 0.000000 | — | — | 2 | 2 |
| 2 | 0.405465 | 0.405465 | 0.000000 | 3903 | 7 |
| 4 | 0.810930 | 0.810930 | 0.000000 | 1369 | 5 |
| 5 | 1.216395 | 1.216395 | 0.000000 | 2401 | 3 |
| 7 | 1.621860 | 1.621860 | 0.000000 | 3025 | 271 |
| 8 | 2.027326 | 2.027326 | 0.000000 | 2559 | 129 |
| 10 | 2.432791 | 2.432791 | 0.000000 | 1925 | 1589 |
| 12 | 2.838256 | 2.838256 | 0.000000 | 3443 | 289 |
| 13 | 3.243721 | 3.243717 | 0.000004 | 591 | 591 |
| 15 | 3.649186 | 2.838252 | 0.810934 | 437 | — |
| 16 | 4.054651 | 3.243718 | 0.810933 | 773 | — |
| 18 | 4.460116 | 3.649186 | 0.810930 | 3039 | — |
| 20 | 4.865581 | 2.956039 | 1.909543 | 2213 | — |

Label: **EXACT COMPUTATION** for the numbers;
**COMPUTATIONALLY OBSERVED** for the pattern.

At every admissible `k <= 13` the bang-bang word is realized in
`n <= 4000`, the actual peak winner is that itinerary, and the `A`-peak
gap is floor error (numerically `0` at large `n`, `0.034` at `n = 3`).
Admissible `k ∈ {15, 16, 18}` have no bang-bang realizer in the
window; the best mixed-word peak equals `(o_k^* − 2) log(3/2)`, so
the gap is exactly two ideal `O` increments. At `k = 20` the gap is
`1.90954` and is no longer a clean two-step deficit. These are window
statements, not prohibitions.

Selected Phase-1 leftovers from the parked statistical census
(`n <= 10^5`, not a new Atlas scan):

| n | status | k | O-run | peak A | peak gap | Hamming(BB) |
|---|--------|---|-------|--------|----------|-------------|
| 11229 | BIT_CAP | — | 3 | 7.613156 | — | — |
| 15065 | BIT_CAP | — | 13 | 7.533938 | — | — |
| 15343 | BIT_CAP | — | 4 | 7.783055 | — | — |
| 15845 | BIT_CAP | — | 19 | 7.703837 | — | — |
| 17033 | BIT_CAP | — | 11 | 7.533938 | — | — |
| 30817 | BIT_CAP | — | 3 | 7.599605 | — | — |
| 34175 | RETURNED | 183 | 5 | 7.155575 | 39.472912 | 76 |
| 48443 | BIT_CAP | — | 4 | 7.481822 | — | — |
| 63185 | BIT_CAP | — | 13 | 7.651721 | — | — |
| 78901 | BIT_CAP | — | 4 | 7.377590 | — | — |
| 88053 | BIT_CAP | — | 2 | 7.429706 | — | — |
| 93883 | BIT_CAP | — | 3 | 7.547489 | — | — |
| 95281 | BIT_CAP | — | 6 | 7.599605 | — | — |
| 98605 | BIT_CAP | — | 4 | 7.325473 | — | — |
| 99679 | BIT_CAP | — | 2 | 7.364039 | — | — |

Label: **EXACT COMPUTATION** on completed returns. Bit-cap rows are
not scored against `H_k^*` and are not infinite excursions. Only
`n = 34175` among the selected leftovers completed a first-return
(`k = 183`, peak gap `39.47`, Hamming `76` to bang-bang).

## 6. Long O-run realizability

`r(n)` is the exact initial odd run. Smallest `n` in the Phase-0
window realizing each observed `r`:

| r | smallest n in window | bits | subsequent E-run | source |
|---|----------------------|------|------------------|--------|
| 1 | 3 | 2 | 3 | phase0 |
| 2 | 3 | 2 | 3 | phase0 |
| 3 | 3 | 2 | 3 | phase0 |
| 4 | 37 | 6 | 1 | phase0 |
| 5 | 115 | 7 | 2 | phase0 |
| 6 | 163 | 8 | 1 | phase0 |
| 7 | 289 | 9 | 8 | phase0 |
| 8 | 293 | 9 | 3 | phase0 |
| 9 | 357 | 9 | 5 | phase0 |
| 10 | 357 | 9 | 5 | phase0 |
| 11 | 663 | 10 | 2 | phase0 |
| 12 | 15065 | 14 | 1 | phase1 |
| 13 | 15065 | 14 | 1 | phase1 |
| 14 | 15845 | 14 | 2 | phase1 |
| 15 | 15845 | 14 | 2 | phase1 |
| 16 | 15845 | 14 | 2 | phase1 |
| 17 | 15845 | 14 | 2 | phase1 |
| 18 | 15845 | 14 | 2 | phase1 |
| 19 | 15845 | 14 | 2 | phase1 |

Word Atlas PE `a_k` records, reused as *upper bounds* on the scale
that realizes a long leading `O`-prefix (not a new census; absence
is `NOT OBSERVED WITHIN SEARCH BOUND`):

| leading O | atlas min n | bits | word |
|-----------|-------------|------|------|
| 2 | 69 | 7 | `OOE` |
| 3 | 99 | 7 | `OOOE` |
| 4 | 37 | 6 | `OOOOE` |
| 5 | 241 | 8 | `OOOOOE` |
| 5 | 427 | 9 | `OOOOOEE` |
| 7 | 425 | 9 | `OOOOOOOE` |
| 8 | 329 | 9 | `OOOOOOOOE` |
| 7 | 1307 | 11 | `OOOOOOOEEE` |
| 8 | 293 | 9 | `OOOOOOOOEEE` |
| 9 | 4997 | 13 | `OOOOOOOOOEEE` |
| 11 | 13013 | 14 | `OOOOOOOOOOOEE` |
| 9 | 6745 | 13 | `OOOOOOOOOEEEEE` |
| 10 | 357 | 9 | `OOOOOOOOOOEEEEE` |
| 13 | 45191 | 16 | `OOOOOOOOOOOOOEEE` |
| 15 | 100145 | 17 | `OOOOOOOOOOOOOOOEE` |
| 16 | 366757 | 19 | `OOOOOOOOOOOOOOOOEE` |
| 13 | 171393 | 18 | `OOOOOOOOOOOOOEEEEEE` |
| 18 | 354119 | 19 | `OOOOOOOOOOOOOOOOOOEE` |
| 14 | 237019 | 18 | `OOOOOOOOOOOOOOEEEEEEE` |
| 20 | 1509681 | 21 | `OOOOOOOOOOOOOOOOOOOOEE` |
| 20 | 3476685 | 22 | `OOOOOOOOOOOOOOOOOOOOEEE` |
| 21 | 5190867 | 23 | `OOOOOOOOOOOOOOOOOOOOOEEE` |

Label: **EXACT COMPUTATION** for the Phase-0 minima;
**COMPUTATIONALLY OBSERVED** for the Atlas upper bounds.

`log n` required to realize `O^k` is not fitted. The Phase-0 minima
are not monotone in a way that would justify an exponential /
double-exponential claim. Atlas upper bounds grow, irregularly, into
the `10^6`–`10^7` range by leading-`O` length 20–24. There is no
proved `F(k)` lower bound. `O_RUN_GREEN` is not awarded.

## 7. Hard-path comparison

Canonical witnesses, replayed on CPU:

| n | k | o | O-run | peak A | H_k^* | peak gap | Hamming(BB) | Hamming(LD) | word prefix |
|---|---|---|-------|--------|-------|----------|-------------|-------------|-------------|
| 3 | 5 | 3 | 3 | 1.182297 | 1.216395 | 0.034098 | 0 | 1 | `OOOEE` |
| 9 | 5 | 3 | 2 | 0.810503 | 1.216395 | 0.405893 | 2 | 1 | `OOEOE` |
| 193 | 70 | 44 | 3 | 4.774877 | 17.840465 | 13.065587 | 26 | 26 | `OOOEOOOOOOOEOOOEEOEE…` |
| 425 | 46 | 29 | 7 | 3.322929 | 11.758488 | 8.435559 | 18 | 23 | `OOOOOOOEOOEEOOOEOEEO…` |
| 761 | 62 | 39 | 9 | 4.487214 | 15.813139 | 11.325925 | 24 | 27 | `OOOOOOOOOEEOEOEEOOEE…` |
| 2183 | 54 | 34 | 2 | 7.481815 | 13.785814 | 6.303999 | 14 | 20 | `OOEOOOOEOOOOOOOOEOOO…` |
| 3431 | 54 | 34 | 2 | 5.977735 | 13.785814 | 7.808078 | 18 | 24 | `OOEOOOOEOOOOOEOEOOOO…` |
| 3889 | 77 | 48 | 5 | 5.637946 | 19.462325 | 13.824379 | 30 | 38 | `OOOOOEOEOOOEOOEOEOEO…` |

Label: **EXACT COMPUTATION**.

`n = 3` lies on the deterministic control boundary. The long records
`193`, `425`, `761`, `2183`, `3889` do not: they keep a long initial
`O`-run, then deviate from bang-bang, and their Hamming distance to
the same-horizon optimiser is large. They are also far from the
constant-frequency `p^* = 3/4` word. They are therefore neither the
deterministic first-return optimiser nor the stochastic ascent
optimiser. They remain canonical witnesses of *realized* hardness,
not of control optimality.

## 8. Stochastic vs deterministic optimum

| object | odd frequency | arrangement | first-return? |
| --- | --- | --- | --- |
| deterministic control | `log 2 / log 3 ≈ 0.630930` | bang-bang `O^o E^e` | yes, by construction |
| LD ascent (Prasad–Prasad model) | `p^* = 3/4` | roughly constant frequency | no; positive slope `a^*` |
| `n = 3` | `3/5 = 0.6` | `OOOEE` | yes, exact optimiser |
| long records | mixed, after a long `O` prefix | not bang-bang, not iid `3/4` | yes as exact `J` returns |

Label: **EXACT CONTROL RESULT** for the first row;
**MODEL PREDICTION** for the second;
**EXACT COMPUTATION** for the witnesses.

The two optima do not coincide, even asymptotically as frequency
statements: `0.630930 ≠ 0.75`. `STATISTICAL_CONTROL_BRIDGE_GREEN` is
false in this phase.

## 9. Exact arithmetic deviations

```text
ε_i = (log log J(x_i) − log log x_i) − δ(parity(x_i))
```

when both logs are defined. `∑ ε_i` is not treated as an invariant.

On states of bit length `≥ 64` along the canonical hard paths, the
recorded `|ε|` is at float noise. The gap between long records and
`H_k^*` is therefore not explained by floor drift in `L`. It is
explained by the *admissible branch*: Juggler emits an `E` while the
same-horizon bang-bang controller still wants `O`, or continues after
the ideal return time. Label: **EXACT COMPUTATION** for the
increments; **COMPUTATIONALLY OBSERVED** for the interpretation.
`CONTROL_ARITHMETIC_GREEN` as a *mechanism theorem* is not awarded:
the mechanism is the already-known exact parity of `J(x)`, not a new
floor identity.

## 10. Word operations

Operations are evaluated relative to the bang-bang optimum, not as a
new word-shape census.

| source n | operation | mutant | Δ peak | first-return? | realizer |
|----------|-----------|--------|--------|---------------|----------|
| 3 | swap_first_O_E | `EOOOE` | -0.693147 | False | — |
| 3 | move_last_prefix_O_later | `OOEOE` | -0.405465 | True | 9 |
| 3 | split_o_run | `OOEOE` | -0.405465 | True | 9 |
| 5 | swap_first_O_E | `EOOE` | -0.693147 | False | — |
| 5 | move_last_prefix_O_later | `OEOE` | -0.405465 | False | — |
| 5 | split_o_run | `OEOE` | -0.405465 | False | — |
| 7 | swap_first_O_E | `EO` | -0.405465 | False | — |
| 7 | move_last_prefix_O_later | `EO` | -0.405465 | False | — |
| 129 | swap_first_O_E | `EOOOOOEE` | -0.693147 | False | — |
| 129 | move_last_prefix_O_later | `OOOOEOEE` | -0.405465 | True | 519 |
| 129 | split_o_run | `OOOOEOEE` | -0.405465 | True | 519 |
| 271 | swap_first_O_E | `EOOOOEE` | -0.693147 | False | — |
| 271 | move_last_prefix_O_later | `OOOEOEE` | -0.405465 | True | 81 |
| 271 | split_o_run | `OOOEOEE` | -0.405465 | True | 81 |
| 289 | swap_first_O_E | `EOOOOOOOEEEE` | -0.693147 | False | — |
| 289 | move_last_prefix_O_later | `OOOOOOEOEEEE` | -0.405465 | True | 621 |
| 289 | split_o_run | `OOOOOOEOEEEE` | -0.405465 | True | 621 |
| 591 | swap_first_O_E | `EOOOOOOOOEEEE` | -0.693147 | False | — |
| 591 | move_last_prefix_O_later | `OOOOOOOEOEEEE` | -0.405465 | True | — |
| 591 | split_o_run | `OOOOOOOEOEEEE` | -0.405465 | True | — |
| 1589 | swap_first_O_E | `EOOOOOOEEE` | -0.693147 | False | — |
| 1589 | move_last_prefix_O_later | `OOOOOEOEEE` | -0.405465 | True | 165 |
| 1589 | split_o_run | `OOOOOEOEEE` | -0.405465 | True | 165 |

Moving an `O` later, or splitting the `O`-run, weakly decreases the
ideal peak. Some mutants remain ideal first-return words at the same
`(k, o)` (`OOEOE` at `n = 9` is the `k = 5` example) and are
strictly suboptimal. Merging a same-`(k, o)` word back to bang-bang
restores `H_k^*`. No local edit *increases* the ideal peak past
bang-bang. Exact realizability of the mutants is the existing
finite-window language, not a new grammar. Stop: this reproduces the
known arrangement sensitivity at fixed `(k, o)` and is not continued.

## 11. Candidate deterministic bounds

Examples only; none is claimed.

1. Any exact trajectory that stays at or above `n` for `k` steps
   lies at most `H_k^*` plus floor error above `L(n)` in the ideal
   coordinate. This is tautological for the *ideal* walk and is
   **not** a bound on `max x_i`.
2. Realizing the bang-bang word `O^o E^{e(o)}` requires some
   starting scale `F(o)`. Phase 0 supplies examples, not `F`.
3. Every long exact trajectory incurs a control-forcing event: an
   even state while `o_so_far < o_k^*` for its own return horizon.
   This is **COMPUTATIONALLY OBSERVED** on the long records and is
   not a theorem for every `n`.

`CANDIDATE CONJECTURE` (not promoted): for each admissible `k`, the
bang-bang word is realized by some positive integer. The Phase-0
window neither proves nor refutes this. A clean refutation would be a
single admissible `k` with a proof that `O^{o_k^*} E^{k-o_k^*}`
has no realizer. None was obtained.

A finite-horizon gap does not prove termination.

## 12. Counterexamples

- **COUNTEREXAMPLE** to “the LD optimiser is the control optimiser”:
  `p^* = 3/4` versus `o/k → log 2 / log 3`, and `ld_is_first_return`
  is false for every `k` in the table.
- **COUNTEREXAMPLE** to “no exact trajectory realizes the ideal
  frontier”: `n = 3` realizes `OOOEE`.
- **COUNTEREXAMPLE** to “every first-return of length `k` is
  bang-bang”: `n = 9`, word `OOEOE`.
- **COUNTEREXAMPLE** to “the known hard records lie on the control
  boundary”: `193`, `425`, `2183`, `3889` have large Hamming
  distance to `O^{o_k^*} E^{k-o_k^*}`.
- **COUNTEREXAMPLE** to “floor arithmetic is what keeps long records
  off the frontier”: large-bit `|ε|` is negligible on those paths.
- No counterexample was found to the closed-form bang-bang
  characterisation for `k <= 50`.

## 13. Decision

Classification: **CONTROL_FRONTIER_GREEN**.

The ideal first-return frontier is the unique bang-bang itinerary, and it is realized at small admissible horizons, but the known long first-return records are not bang-bang and sit a definite peak gap below the same-horizon optimum. No uniform all-horizon realizability theorem is proved.

The conjunction “adversarial first-return control + exact Juggler
realizability” is a well-posed object. The ideal side is settled as a
combinatorial theorem. The realizability side is not: small bang-bang
words are realized, long bang-bang words are not found in `n <= 4000`,
and the Atlas upper bounds show that long *leading* `O`-runs exist at
much larger scale without proving they complete the exact first-return
bang-bang word. No uniform gap theorem and no `F(k)` lower bound are
proved. Phase 2 CUDA is not launched.

The parked statistical model stays `STATISTICAL_ONLY`.

Branch status in the dossier: **PARK**.
