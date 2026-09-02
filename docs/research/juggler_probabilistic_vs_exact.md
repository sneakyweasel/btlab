# Exact Juggler trajectories versus the 2025 large-deviation geometry

Status: **MODEL_ONLY**

Standalone comparison of exact `floor_power` trajectories with the
Prasad–Prasad 2025 juggler-like random-walk model reconstructed in
[juggler_probabilistic_model.md](juggler_probabilistic_model.md).
`L = log log x` is a diagnostic. It never defines the map. This is not
a termination theorem, not a proof that Juggler is random, and not a
proof of asymptotic constants.

Every statement is labelled
`MODEL ASSUMPTION` | `COMPUTATIONALLY OBSERVED` | `STATISTICAL ESTIMATE` |
`EXACT COMPUTATION` | `LEAN-CERTIFIED` | `CANDIDATE CONJECTURE`.

Closed Atlas branches stay closed. The previous drift census
([juggler_probabilistic.md](juggler_probabilistic.md)) remains
`STATISTICAL_ONLY` / `PARK` and is not reopened as a scalar-invariant hunt.

## 1. Literature model

The reconstruction is on the model page. The working optimizer, derived
from M0 (iid fair parity, idealized increments log(3/2) / log(1/2)),
is **MODEL ASSUMPTION** plus algebra:

- p* = 3/4
- a* = (3/4) log 3 - log 2 ≈ 0.130812036
- rho* = 1, finite-size predictor 1 + log log n / log n
- gamma = 1/I_Ber(log 2 / log 3) ≈ 28.828259
- t_peak* = 1/a* ≈ 7.644557
- t_stop* = 1/a* + 1/|mu| ≈ 14.596675

The reported literature figures rho ≈ 1 and gamma ≈ 28.828
are these derived constants, not independent oracles. Label:
**MODEL ASSUMPTION** / derived **MODEL PREDICTION**.

The comparison chart is t_i = i / log n, Z_i = log log x_i / log n.

## 2. Exact Juggler data

The map is exact `isqrt` even / `isqrt(n^3)` odd. Label:
**EXACT COMPUTATION**.

- Phase 0: every n in [2, 4000] walked to first return
  below n, horizon 10000, bit cap 25000.
- Phase 1: stored records plus the previous n<=10^5 leftovers
  `11229, 15065, 15343, 15845, 17033, 30817, 34175, 48443, 63185, 78901, 88053, 93883, 95281, 98605, 99679` and 24 odd draws from
  three scale bins. Huge-digit records used bit cap 4000000.
- Stopping time is first-return length plus the cheap continuation to 1
  after the state has already dropped below n.
- CUDA was not used. Leftovers are bit-cap / horizon, not H=infinity.

Known stored records replayed: 2, 3, 9, 37, 77, 113, 173, 193, 425, 761, 2183, 3431, 3889.
Label: **EXACT COMPUTATION**.

## 3. Parity statistics

Orbit-induced frequencies. Label: **STATISTICAL ESTIMATE**.
Uniform one-step P(O)=1/2 is counting, not dynamics.

| ensemble | steps | P(O) | P(O|O) | P(O|E) | Markov gap | Corr ΔL lag-1 |
| --- | --- | --- | --- | --- | --- | --- |
| orbit_n<=4000 | 14081 | 0.500959 | 0.504253 | 0.494716 | 0.009537 | 0.008662 |
| ordinary_n<=4000 | 12409 | 0.484084 | 0.481938 | 0.472824 | 0.009114 | 0.008188 |
| hard_families_n<=4000 | 1672 | 0.626196 | 0.632283 | 0.586919 | 0.045364 | 0.044717 |
| records | 1957 | 0.627491 | 0.645765 | 0.582026 | 0.06374 | 0.062434 |

One-step uniform P(O) by log10 scale, n<=10^5:

| bin | P(O) | ci95 lo | ci95 hi | N |
| --- | --- | --- | --- | --- |
| 1e0-1e1 | 0.5 | 0.215213 | 0.784787 | 8 |
| 1e1-1e2 | 0.5 | 0.398835 | 0.601165 | 90 |
| 1e2-1e3 | 0.5 | 0.467403 | 0.532597 | 900 |
| 1e3-1e4 | 0.5 | 0.489672 | 0.510328 | 9000 |
| 1e4-1e5 | 0.5 | 0.496733 | 0.503267 | 90000 |
| all | 0.499995 | 0.496896 | 0.503094 | 99999 |

M1 (Markov) is treated as needed if the bulk Markov gap exceeds 0.08:
`False`. M2 (scale-conditioned) is treated as needed if
one-step scale bins move by more than 0.05: `False`.
Neither is promoted to an automaton.

Question: does fair / independent parity become more accurate for ordinary
paths and fail on extremals? Ordinary Markov gap
`0.009114`; hard-family gap
`0.045364`; record gap
`0.06374`. Label:
**COMPUTATIONALLY OBSERVED**.

## 4. Log-log increments

Ideal terms log(3/2)≈0.405465, log(1/2)≈-0.693147.
Label of the terms: **MODEL ASSUMPTION**. Empirical means:
**STATISTICAL ESTIMATE**.

| ensemble | mean dL on O | O minus log(3/2) | mean dL on E | E minus log(1/2) |
| --- | --- | --- | --- | --- |
| orbit_n<=4000 | 0.405453 | -1.2e-05 | -0.694854 | -0.001707 |
| hard_families_n<=4000 | 0.405465 | -1e-06 | -0.693205 | -5.8e-05 |
| records | 0.405434 | -3.1e-05 | -0.693279 | -0.000132 |

On hard and record orbits the O/E means sit on the ideal terms to
about `10^{-5}` or better. Floor error is negligible on the states
that actually occur on extremal paths in this window. Label:
**COMPUTATIONALLY OBSERVED**. That does not make the increment an
exact law.

## 5. Independence / correlation tests

Lag-1 correlation of consecutive `ΔL` is in the parity table.
Ordinary `0.008188`; hard
`0.044717`; records
`0.062434`. Label:
**STATISTICAL ESTIMATE**.

Ordinary lag-1 correlation is near zero. Hard and record paths show a
small positive letter memory (Markov gap `0.05`–`0.06`), not an
independent extra `ΔL` mechanism. Label: **COMPUTATIONALLY OBSERVED**.

## 6. Large-deviation tails

Odd starts `n<=4000` that returned. The model column is the un-normalized
`e^{-k I_0}`. Compare the *slope* of `log P(H>=k)` to `I_0=0.034688185`,
not the intercept. Label: **MODEL ASSUMPTION** for the rate;
**STATISTICAL ESTIMATE** for the empirical tail.

Empirical rate `0.089366`, model `I_0`,
ratio `2.576277`, `r^2=0.981744`.

| k | emp P(H>=k) | e^{{-k I0}} | log P + k I0 | count |
| --- | --- | --- | --- | --- |
| 5 | 0.377189 | 0.840767 | -0.801569 | 754 |
| 8 | 0.212106 | 0.757671 | -1.273163 | 424 |
| 10 | 0.157579 | 0.706889 | -1.500948 | 315 |
| 16 | 0.084542 | 0.574066 | -1.915493 | 169 |
| 20 | 0.058029 | 0.499692 | -2.153048 | 116 |
| 32 | 0.017509 | 0.329552 | -2.935032 | 35 |
| 40 | 0.013007 | 0.249692 | -2.954778 | 26 |
| 54 | 0.007004 | 0.153637 | -3.088183 | 14 |
| 70 | 0.001501 | 0.088198 | -4.073617 | 3 |
| 77 | 0.0005 | 0.069184 | -4.929412 | 1 |

A fitted exponential is not a Cramér theorem. Label: **STATISTICAL ESTIMATE**.

## 7. Extremal trajectory geometry

Pre-peak fit of `Z` against `t` versus slope `a*`. Several windows are
stored on each record (`full`, `first_half`, `second_half`,
`drop_first_two`, `middle_60`). A path that is linear on one window and
not on another is not a structural law. Label:
**COMPUTATIONALLY OBSERVED**.

Hard families were ranked independently and not merged. On `n<=4000`
Hard_peak and Hard_ratio coincided. Hard_duration is closer to
`p*=3/4` than Hard_peak / Hard_margin, which stay more odd-heavy.
Different hardness notions do not collapse to one geometry. Label:
**COMPUTATIONALLY OBSERVED**.

| family | N | mean Z_peak | mean t_peak | mean p_O pre | mean slope |
| --- | --- | --- | --- | --- | --- |
| Hard_peak | 20 | 0.926471 | 4.192886 | 0.812866 | 0.163434 |
| Hard_ratio | 20 | 0.926471 | 4.192886 | 0.812866 | 0.163434 |
| Hard_duration | 20 | 0.850994 | 4.847538 | 0.757789 | 0.097093 |
| Hard_margin | 20 | 0.686168 | 1.769698 | 0.861637 | 0.212359 |
| records | 13 | 0.961647 | 3.63655 | 0.845161 | 0.208517 |

Mandatory / stored records (peak, peak/n, log peak / log n, Z, t_peak, H):

| n | peak | peak/n | log peak/log n | Z_peak | t_peak | H | H/log n |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 2 | 1.0 | 1.0 |  | 0.0 | 1 | 1.442695 |
| 3 | 36 | 12.0 | 3.26186 | 1.16178 | 2.730718 | 5 | 4.551196 |
| 9 | 140 | 15.555556 | 2.249038 | 0.727144 | 0.910239 | 5 | 2.275598 |
| 37 | 24906114455136 | 673138228517.1875 | 8.542463 | 0.949623 | 2.215503 | 15 | 4.154068 |
| 77 | 2322378 | 30160.753247 | 3.374484 | 0.61812 | 0.690639 | 10 | 2.302129 |
| 113 | bits:88 | 1.7957928223373872e+24 | 12.813604 | 0.868107 | 1.9038 | 13 | 2.749933 |
| 173 | bits:272 | 2.5726062775784095e+79 | 36.48201 | 1.016138 | 3.298862 | 26 | 5.045319 |
| 193 | bits:900 | 3.4940775147613496e+268 | 118.495777 | 1.222857 | 8.930794 | 70 | 13.301182 |
| 425 | bits:243 | 1.936670103180806e+70 | 27.741497 | 0.84654 | 6.278824 | 46 | 7.600681 |
| 761 | bits:851 | 1.5750732875772432e+253 | 88.873481 | 0.961548 | 7.385487 | 62 | 9.344902 |
| 2183 | bits:19694 |  | 1775.498451 | 1.23842 | 4.162084 | 54 | 7.023517 |
| 3431 | bits:4634 |  | 394.570579 | 0.991892 | 3.80807 | 54 | 6.633412 |
| 3889 | bits:3350 |  | 280.88532 | 0.937597 | 4.960133 | 77 | 9.315372 |

## 8. Record comparison with model

Side-by-side. Columns are observations versus M0 predictors. Nothing
here is a theorem.

| n | H | sigma | Z_peak | rho_pred | Z resid | t_peak | p_O pre | slope | status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 1 | 1 |  |  |  | 0.0 |  |  | RETURNED |
| 3 | 5 | 6 | 1.16178 | 1.085606 | 0.076174 | 2.730718 | 1.0 | 0.39456 | RETURNED |
| 9 | 5 | 7 | 0.727144 | 1.358268 | -0.631124 | 0.910239 | 1.0 | 0.405251 | RETURNED |
| 37 | 15 | 17 | 0.949623 | 1.355578 | -0.405955 | 2.215503 | 0.875 | 0.222358 | RETURNED |
| 77 | 10 | 19 | 0.61812 | 1.338125 | -0.720005 | 0.690639 | 1.0 | 0.405419 | RETURNED |
| 113 | 13 | 16 | 0.868107 | 1.32859 | -0.460483 | 1.9038 | 0.888889 | 0.24566 | RETURNED |
| 173 | 26 | 32 | 1.016138 | 1.318172 | -0.302035 | 3.298862 | 0.823529 | 0.221785 | RETURNED |
| 193 | 70 | 73 | 1.222857 | 1.31555 | -0.092693 | 8.930794 | 0.723404 | 0.048583 | RETURNED |
| 425 | 46 | 67 | 0.84654 | 1.297485 | -0.450945 | 6.278824 | 0.710526 | 0.016725 | RETURNED |
| 761 | 62 | 66 | 0.961548 | 1.285216 | -0.323668 | 7.385487 | 0.714286 | 0.039296 | RETURNED |
| 2183 | 54 | 72 | 1.23842 | 1.265296 | -0.026877 | 4.162084 | 0.84375 | 0.234725 | RETURNED |
| 3431 | 54 | 61 | 0.991892 | 1.257581 | -0.265689 | 3.80807 | 0.806452 | 0.167459 | RETURNED |
| 3889 | 77 | 80 | 0.937597 | 1.255524 | -0.317928 | 4.960133 | 0.756098 | 0.100389 | RETURNED |
| 11229 | 92 | 101 | 1.055728 | 1.239414 | -0.183686 | 5.790105 | 0.759259 | 0.112106 | RETURNED |
| 15065 | 62 | 66 | 1.060616 | 1.235325 | -0.174709 | 2.598718 | 0.92 | 0.28227 | RETURNED |
| 15343 | 83 | 128 | 1.042579 | 1.235076 | -0.192496 | 5.083824 | 0.77551 | 0.10698 | RETURNED |
| 15845 | 132 | 139 | 1.128698 | 1.234638 | -0.10594 | 4.446462 | 0.813953 | 0.124038 | RETURNED |
| 17033 | 89 | 112 | 1.048552 | 1.233661 | -0.18511 | 2.565969 | 0.92 | 0.28227 | RETURNED |
| 30817 | 81 | 93 | 1.118158 | 1.225973 | -0.107815 | 3.773285 | 0.846154 | 0.219237 | RETURNED |
| 34175 | 183 | 193 | 0.910137 | 1.224688 | -0.314551 | 5.843332 | 0.737705 | 0.071934 | RETURNED |
| 48443 | 149 | 157 | 1.355342 | 1.220469 | 0.134873 | 5.561661 | 0.816667 | 0.178248 | RETURNED |
| 63185 | 51 | 63 | 0.946276 | 1.217371 | -0.271095 | 2.53306 | 0.892857 | 0.242026 | RETURNED |
| 78901 | 253 | 258 | 1.211428 | 1.214853 | -0.003425 | 9.666592 | 0.724771 | 0.098548 | RETURNED |
| 88053 | 61 | 68 | 0.86618 | 1.213633 | -0.347453 | 3.513181 | 0.8 | 0.179809 | RETURNED |
| 93883 | 89 | 106 | 0.872108 | 1.212927 | -0.340819 | 3.755523 | 0.790698 | 0.140064 | RETURNED |
| 95281 | 62 | 71 | 0.885915 | 1.212765 | -0.32685 | 3.314555 | 0.815789 | 0.184186 | RETURNED |
| 98605 | 73 | 95 | 0.84945 | 1.21239 | -0.36294 | 4.870041 | 0.75 | 0.081891 | RETURNED |
| 99679 | 59 | 73 | 0.852083 | 1.212272 | -0.360189 | 2.519612 | 0.862069 | 0.251244 | RETURNED |

Running record-breakers among `n<=4000` (last eight breaks):

| n | broke | Z_peak | Z resid | p_O pre | H/log n |
| --- | --- | --- | --- | --- | --- |
| 113 | peak,ratio | 0.868107 | -0.460483 | 0.888889 | 2.749933 |
| 163 | duration | 0.797213 | -0.522398 | 1.0 | 4.711656 |
| 173 | peak,ratio,duration | 1.016138 | -0.302035 | 0.823529 | 5.045319 |
| 193 | peak,ratio,duration | 1.222857 | -0.092693 | 0.723404 | 13.301182 |
| 241 | margin | 0.923183 | -0.387125 | 0.909091 | 4.922698 |
| 425 | margin | 0.84654 | -0.450945 | 0.710526 | 7.600681 |
| 2183 | peak,ratio | 1.23842 | -0.026877 | 0.84375 | 7.023517 |
| 3889 | duration | 0.937597 | -0.317928 | 0.756098 | 9.315372 |

Mean absolute slope error on long records: `0.08402`.
Mean absolute `p_O` error: `0.066167`. Late-chain
`Z` residual: `-0.262934`. Label:
**COMPUTATIONALLY OBSERVED**.

## 9. Exceptional trajectories

Threshold declared before ranking: a hard / record / `H>=16` path with
at least `8` pre-peak steps is exceptional
if `max |Z-Z_model| > 0.2` or
`|p_O(pre-peak)-3/4| > 0.25`. Label of the region:
**MODEL ASSUMPTION** (finite-sample cut). Membership:
**EXACT COMPUTATION** of the coordinates, **COMPUTATIONALLY OBSERVED**
as a set.

Count: `95`. Only-long-O reading:
`True`. Residue `mod 8` concentrated:
`False`.

| n | why | H | p_O pre | max |dZ| | O-run0 | n mod 8 | word |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 163 | Z_dev | 24 | 1.0 | 0.323517 | 6 | 3 | OOOOOOEOEEOOOEOE |
| 173 | Z_dev | 26 | 0.823529 | 0.373028 | 2 | 5 | OOEOOOOOOOOEOOEO |
| 193 | Z_dev | 70 | 0.723404 | 0.57408 | 3 | 1 | OOOEOOOOOOOEOOOE |
| 229 | Z_dev | 24 | 0.916667 | 0.404322 | 2 | 5 | OOEOOOOOOOOOEOEE |
| 241 | Z_dev | 27 | 0.909091 | 0.350525 | 5 | 1 | OOOOOEOOOOOEOEOO |
| 265 | Z_dev | 26 | 0.888889 | 0.246112 | 5 | 1 | OOOOOEOOOEEEOOOE |
| 293 | Z_dev | 43 | 0.791667 | 0.386822 | 8 | 5 | OOOOOOOOEEEOOOOO |
| 329 | Z_dev | 23 | 0.857143 | 0.379088 | 8 | 1 | OOOOOOOOEOOEOOEE |
| 357 | Z_dev | 24 | 1.0 | 0.467276 | 10 | 5 | OOOOOOOOOOEEEEEO |
| 425 | Z_dev | 46 | 0.710526 | 0.589961 | 7 | 1 | OOOOOOOEOOEEOOOE |
| 427 | Z_dev | 21 | 1.0 | 0.226731 | 5 | 3 | OOOOOEEOOOEEOEOO |
| 451 | Z_dev | 21 | 1.0 | 0.404464 | 9 | 3 | OOOOOOOOOEOEEEEO |
| 477 | Z_dev | 26 | 0.8125 | 0.311724 | 7 | 5 | OOOOOOOEEOOEOOOO |
| 557 | Z_dev | 27 | 0.928571 | 0.4344 | 5 | 5 | OOOOOEOOOOOOOOEO |
| 565 | Z_dev | 24 | 0.866667 | 0.303382 | 2 | 5 | OOEOOEOOOOOOOOOE |
| 659 | Z_dev | 27 | 0.916667 | 0.338517 | 3 | 3 | OOOEOOOOOOOOEOEO |

## 10. Exact arithmetic causes of model deviations

The exact itinerary, not the random model, produces every deviation.
On this window the dominant exact mechanism is:

- an initial odd run (the expanding branch of `J`), often frequency 1
  on a short prefix;
- a pre-peak mix whose `p_O` is near `3/4` on the *longest* records
  (`3889`, `11229`, `34175`) and higher on peak-record families;
- a full-word frequency on hard orbits near `p0=log 2/log 3≈0.631`
  (the model zero-drift / survival frequency), not `p*`;
- floor error that is already negligible on those orbits.

No new residue family, no new finite itinerary, and no floor-boundary search
was opened. `power_bound_contracts` and `floorPower_odd_ge` remain the
exact contraction certificates for completed words. Label of those
lemmas: **LEAN-CERTIFIED**. Label of the deviation reading:
**COMPUTATIONALLY OBSERVED**, not a **CANDIDATE CONJECTURE**.

## 11. Statistical → exact synthesis candidates

The attractive chain — typical negative drift, LD-dangerous geometry
`(p*, a*)`, exact prohibition of that geometry — does **not** close.
The model-dangerous path is a long block with odd frequency `3/4`.
Exact hard paths begin with a long odd run (frequency 1), then a mix
whose full-word frequency sits near the *zero-drift* value `p0`,
while only the longest delay records have pre-peak `p_O` near `p*`.
That is the expanding branch plus an ordinary suffix, already visible
in the itinerary. No new finite-itinerary constraint is proposed. No
**CANDIDATE CONJECTURE** is opened.

## 12. Limitations

- `n<=4000` plus selected `n<=10^5` is not an asymptotic.
- `Z_0=log log n / log n` is still `0.2`–`0.3`; `ρ→1` cannot be seen.
- `γ log n ≈ 239` at `n=4000` while the delay record is `77`.
- Huge records may hit the bit cap; leftovers are not infinite.
- M0 increments are independent by fiat; exact `ΔL` is a function of
  the integer.
- Floating `L` overflows are avoided by bit-length logarithms; they
  remain diagnostics.
- No CUDA Phase 2: no stable new statistical quantity appeared that
  needed a `10^8` sample.

## 13. Decision

**MODEL_ONLY**. Branch decision: **CLOSE**.

The random-walk model describes bulk log-log increments, near-iid ordinary parity, and (on the longest delay records) pre-peak odd frequency near p*=3/4. It does not give a stable ascent slope a*, the duration-tail rate is about 2.6 I0 on this window, and the exceptional set is the expanding odd prefix already visible in the itinerary. Descriptive, not proof-producing.

| criterion | flag |
| --- | --- |
| LD_GEOMETRY_GREEN | False |
| LD_CONSTANT_GREEN | False |
| PARITY_MODEL_GREEN | True |
| EXTREMAL_FREQUENCY_GREEN | True |
| EXCEPTIONAL_STRUCTURE_GREEN | False |
| STATISTICAL_EXACT_BRIDGE_GREEN | False |
| MODEL_REFUTED | False |
| MODEL_ONLY | True |

Best next question: none from this branch as an automatic sequel.
Do not claim termination. Do not reopen a closed Atlas branch.
A later theorem would need an exact constraint on long expanding
odd prefixes, which is the already-closed realization / envelope
problem, not a new large-deviation theorem.
