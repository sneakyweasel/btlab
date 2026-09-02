# Juggler probabilistic drift and large-deviation frontier

Status: **STATISTICAL_ONLY**

Standalone statistical phase on the exact Juggler floor-power map.
`L = log log x` is a diagnostic. It never defines the map. This is not
a termination theorem. Closed symbolic-compression branches stay closed.

Every result below is labelled with the Phase-0 evidence axis
`LEAN-CERTIFIED` | `EXACT COMPUTATION` | `COMPUTATIONALLY OBSERVED` |
`STATISTICAL ESTIMATE` | `MODEL ASSUMPTION` | `CANDIDATE CONJECTURE`.
Ledger tags in the dossier remain the seven laboratory labels.

## 1. Literature context

Ordinary Collatz heuristics compress several parity steps and model
`log` of the accelerated orbit by a random walk: odd growth against
dyadic contraction. Tao (`tao-2019-almost-all-collatz`) goes far beyond
that heuristic, proving that almost all Collatz orbits attain almost
bounded values, using logarithmic density and an approximate transport
statement. That is a Collatz theorem. It is not imported here as a
Juggler theorem. Label: **LEAN-CERTIFIED** is not claimed; the citation
is literature context.

A 2025 preprint of Vikram Prasad and M. A. Prasad
(`prasad-prasad-2025-juggler-like`) applies a random-walk /
large-deviation model to *juggler-like* sequences and reports estimated
excursion and stopping constants. Treat it as literature context, not
as an established theorem on the exact floor-power map
`J(even)=⌊√n⌋`, `J(odd)=⌊n^{3/2}⌋`. Label: **MODEL ASSUMPTION** of
that preprint; **not** a laboratory theorem.

OEIS A007320 remains the computational step-count table. Label:
**EXACT COMPUTATION** on published terms only; totality is unclaimed.

This experiment derives the increment from exact `J`, estimates the
conditional law of `ΔL`, and measures the gap between a baseline
stochastic model and the deterministic positive-integer dynamics.
It does not reproduce the Prasad constants and does not assume
`P(O)=P(E)=1/2` as a law.

Phase-12 parity-drift already recorded the *conceptual* costs
`+log(3/2)` / `+log(1/2)` and proved exact block inequalities
(`OOOEE`, `EE`) as `T^k(n)<n`. Those are finite-itinerary certificates.
They are not a statistical law. Label of the block lemmas:
**LEAN-CERTIFIED**. This page is not a reopen of that branch.

## 2. Choice of measure

Four ensembles were compared on the same exact one-step map.

| ensemble | P(O) | mean ΔL | sample size |
| --- | --- | --- | --- |
| uniform [16,4000] | 0.499875 | -0.146328 | 3985 |
| log-uniform [16,4000] | 0.497087 | -0.157105 | 3985 |
| odd-uniform [16,4000] | 1.0 | 0.405458 | 1992 |
| uniform [16,1e5] | 0.499995 | -0.144187 | 99985 |
| log-uniform [16,1e5] | 0.498163 | -0.152383 | 99985 |
| odd-uniform [16,1e5] | 1.0 | 0.405465 | 49992 |
| orbit-induced n<=4000 | 0.500889 | -0.143731 | walk steps |

Uniform integers have `P(O)=1/2` by counting. That is not a dynamical
law. Evens are exactly contracting for `n>=2`
(`floorPower` even branch; `T(n)<n`). Label: **LEAN-CERTIFIED** even
contraction, **EXACT COMPUTATION** of `H(n)=1` on every even start in
the window.

Log-uniform (`weight 1/x`) is the multiplicative analogue of the
Collatz logarithmic density. Odd-uniform removes the trivial even
mass. Orbit-induced counts actual steps along first-return walks.

Odd-uniform one-step drift is tautologically `μ_O ≈ log(3/2) > 0`,
because every odd integer takes an `O` step. It is not a competing
`μ_∞`. Mixed-parity ensembles (uniform, log-uniform, orbit-induced)
all have negative mean `ΔL` near the ideal half-and-half value
`-0.143841`. Label: **STATISTICAL ESTIMATE**. They are not equivalent
as tail laws: even mass forces `P(H>=2)=1/2` under uniform counting.
The natural ensemble for excursion tails is therefore odd-uniform or
log-uniform on odds. The natural ensemble for one-step drift of `L`
at large scale is log-uniform or large-bit random integers.

## 3. Exact Juggler increment

The map is exact:

```
J(n) = isqrt(n)        if n even
J(n) = isqrt(n^3)      if n odd
```

For `x >= 16` and `J(x) >= 3` the diagnostic is

```
ΔL = log log J(x) - log log x
   = branch_term + floor_error
```

with `branch_term = log(3/2)` on `O` and `log(1/2)` on `E`. This
identity is an algebraic rewrite of the two floating logarithms.
Label: **EXACT COMPUTATION** of `J`; **STATISTICAL ESTIMATE** of `ΔL`.

Ideal half-and-half drift: `μ_ideal = -0.143841`.
This is a **MODEL ASSUMPTION**, not an empirical claim.

## 4. Parity statistics

Uniform one-step `P(O)` on `[16,4000]` is `0.499875` and on
`[16,1e5]` is `0.499995`. That is counting, not dynamics.

Orbit-induced `P(O)` on first-return walks `n<=4000` is
`0.500889`. One-step history conditionals:

| history | P(O|history) |
| --- | --- |
| O | 0.504042 |
| EO | 0.491322 |
| OO | 0.50928 |
| E | 0.494876 |
| OE | 0.487424 |
| EE | 0.518776 |

Short history changes `P(O)` but does not produce a finite-memory
symbolic process that can replace the current integer. After an `O`
the next state is a specific integer `floor(x^{3/2})`, not a random bit.
Label: **STATISTICAL ESTIMATE**. Do not read this as an automaton.
Do not read `P(O)` as a residual invariant.

## 5. Run statistics

Run lengths among first-return words `n<=4000`, compared with a
geometric baseline from the empirical mean length. This is frequency,
not word semantics, and not a PE-density law.

| type | len | freq | geometric | dev | count |
| --- | --- | --- | --- | --- | --- |
| O | 1 | 0.501001 | 0.495747 | 0.005254 | 1752 |
| O | 2 | 0.244209 | 0.249982 | -0.005773 | 854 |
| O | 3 | 0.121819 | 0.126054 | -0.004235 | 426 |
| O | 4 | 0.066629 | 0.063563 | 0.003065 | 233 |
| O | 5 | 0.032599 | 0.032052 | 0.000547 | 114 |
| O | 6 | 0.017158 | 0.016162 | 0.000995 | 60 |
| O | 7 | 0.008293 | 0.00815 | 0.000143 | 29 |
| O | 8 | 0.004003 | 0.00411 | -0.000106 | 14 |
| E | 1 | 0.78461 | 0.782268 | 0.002341 | 4313 |
| E | 2 | 0.165181 | 0.170325 | -0.005144 | 908 |
| E | 3 | 0.03984 | 0.037085 | 0.002755 | 219 |
| E | 4 | 0.00855 | 0.008075 | 0.000476 | 47 |
| E | 5 | 0.001273 | 0.001758 | -0.000485 | 7 |
| E | 6 | 0.000546 | 0.000383 | 0.000163 | 3 |

Long `O`-runs remain visible. Their frequencies are not promoted to
an asymptotic PE law. Label: **STATISTICAL ESTIMATE**. The closed
PE-density branch stays closed.

## 6. Empirical drift

One-step uniform `[16,1e5]` by the scale partition
`[e^{2^j}, e^{2^{j+1}})`:

| scale | branch | N | mean ΔL | var |
| --- | --- | --- | --- | --- |
| exp(2^1)--exp(2^2) | ALL | 39 | -0.182753 | 0.337575 |
| exp(2^1)--exp(2^2) | E | 20 | -0.741152 | 0.001435 |
| exp(2^1)--exp(2^2) | O | 19 | 0.405035 | 0.0 |
| exp(2^2)--exp(2^3) | ALL | 2926 | -0.146344 | 0.30461 |
| exp(2^2)--exp(2^3) | E | 1463 | -0.698149 | 3.3e-05 |
| exp(2^2)--exp(2^3) | O | 1463 | 0.405461 | 0.0 |
| exp(2^3)--exp(2^4) | ALL | 97020 | -0.144107 | 0.302032 |
| exp(2^3)--exp(2^4) | E | 48510 | -0.693678 | 0.0 |
| exp(2^3)--exp(2^4) | O | 48510 | 0.405465 | 0.0 |

Large-bit random integers (exact `J`, 80 samples per class):

| class | N | mean ΔL | branch term | mean floor_error |
| --- | --- | --- | --- | --- |
| bits_16_O | 80 | 0.405465 | 0.405465 | -0.0 |
| bits_16_E | 80 | -0.693573 | -0.693147 | -0.000425 |
| bits_32_O | 80 | 0.405465 | 0.405465 | -0.0 |
| bits_32_E | 80 | -0.693148 | -0.693147 | -1e-06 |
| bits_64_O | 80 | 0.405465 | 0.405465 | -0.0 |
| bits_64_E | 80 | -0.693147 | -0.693147 | -0.0 |
| bits_128_O | 80 | 0.405465 | 0.405465 | 0.0 |
| bits_128_E | 80 | -0.693147 | -0.693147 | 0.0 |
| bits_256_O | 80 | 0.405465 | 0.405465 | 0.0 |
| bits_256_E | 80 | -0.693147 | -0.693147 | 0.0 |
| bits_512_O | 80 | 0.405465 | 0.405465 | 0.0 |
| bits_512_E | 80 | -0.693147 | -0.693147 | 0.0 |

At large bit length the increment approaches the branch term and the
floor error collapses. Conditional drift on `mod 2,4,8,3,9` is
dominated by parity: even residues carry `μ ≈ log(1/2)`, odd residues
carry `μ ≈ log(3/2)`. Residues that mix parities (none of these moduli
do for a single residue) are not used as a hunt. Label:
**STATISTICAL ESTIMATE** on the stated windows.

Orbit-induced mean `ΔL` on `n<=4000` walks:
`-0.143731`.

Large-scale mixed-parity drift is negative on this window.
This is **not** `μ_J` as a theorem. Finite-range cutoff: one-step
`n<=10^5`, orbit `n<=4000` plus leftover-aware `n<=10^5`, large-bit
probe through 512 bits. Label: **STATISTICAL ESTIMATE**.

## 7. Model comparison

Baseline models, simulated on the `L`-coordinate only
(4000 paths, horizon 80):

| model | mean H | max H | P(H>=5) | P(H>=10) | P(H>=20) |
| --- | --- | --- | --- | --- | --- |
| M0 | 3.48775 | 80 | 0.1845 | 0.075 | 0.02875 |
| M1 | 3.413 | 80 | 0.184 | 0.071 | 0.0275 |
| M2 | 3.3025 | 80 | 0.1755 | 0.06825 | 0.02675 |
| M3 | 3.533 | 80 | 0.19425 | 0.0745 | 0.02975 |
| M4 | 3.4095 | 80 | 0.18325 | 0.06925 | 0.02625 |

- `M0`: independent Bernoulli with empirical orbit `P(O)`.
- `M1`: one-step Markov on `{O,E}`.
- `M2`: magnitude-conditioned `P(O)`.
- `M3`: short history (`<=2`) plus the Markov fallback.
- `M4`: run-length comparison reduced to the same Markov step; it is
  not an automaton.

The scientific object is the difference between these models and exact
`H(n)`. Exact `P(H>=k)` on `n<=4000`:

| k | P(H>=k) | count | ci95 lo | ci95 hi |
| --- | --- | --- | --- | --- |
| 1 | 1.0 | 3999 | 0.99904 | 1.0 |
| 2 | 0.499875 | 1999 | 0.484385 | 0.515365 |
| 3 | 0.252313 | 1009 | 0.239093 | 0.266008 |
| 4 | 0.252313 | 1009 | 0.239093 | 0.266008 |
| 5 | 0.188547 | 754 | 0.176725 | 0.200967 |
| 8 | 0.106027 | 424 | 0.096859 | 0.11595 |
| 10 | 0.07877 | 315 | 0.070819 | 0.087529 |
| 16 | 0.042261 | 169 | 0.036452 | 0.048948 |
| 20 | 0.029007 | 116 | 0.02424 | 0.034678 |
| 32 | 0.008752 | 35 | 0.0063 | 0.012147 |
| 40 | 0.006502 | 26 | 0.004441 | 0.00951 |
| 54 | 0.003501 | 14 | 0.002087 | 0.005868 |
| 70 | 0.00075 | 3 | 0.000255 | 0.002203 |
| 77 | 0.00025 | 1 | 4.4e-05 | 0.001415 |
| 80 | 0.0 | 0 | 0.0 | 0.00096 |

Models using idealized additive `ΔL` miss the exact floor and the
forced even contraction `H(n)=1`. Additional model complexity past
`M1` does not create a deterministic constraint. Label:
**MODEL ASSUMPTION** for the simulators; **EXACT COMPUTATION** for
`H(n)` on completed returns.

## 8. Large-deviation tails

Descriptive fit of `log P(H>=k)` versus `k` on `n<=4000`:
rate `c ≈ 0.120103`, `r^2 ≈ 0.977852`.
Family: `exponential_descriptive`. Label: **STATISTICAL ESTIMATE**.
This is not a Cramér theorem and not a Gaussian theorem.

The candidate inequality `P(x_i >= n for all i<=k) <= exp(-c k)` is
compatible with the sample as a description. It is **not** proved.
What would still be required for every positive integer: a uniform
tail bound under a named measure, plus a pointwise argument that no
infinite exceptional family exists. Phase 0 does not supply either.

## 9. Exceptional trajectories

`H>=16` starts on `n<=4000`: `169`
(table below is the longest `40`).
All odd among those listed: `True`. Mean initial `O`-run:
`4.65`. Named arithmetic family:
`False`.

Exceptional finite paths are odd starts with a long initial O-run. Residues mod 8/9 are not concentrated. This is the expanding branch, not a new exact arithmetic family.

| n | H | O-run0 | n mod 8 | obs drift | word prefix |
| --- | --- | --- | --- | --- | --- |
| 3889 | 77 | 5 | 1 | 0.130812 | OOOOOEOEOOOEOOEOEOEO |
| 193 | 70 | 3 | 1 | 0.199474 | OOOEOOOOOOOEOOOEEOEE |
| 3547 | 70 | 3 | 3 | 0.268139 | OOOEOOOEOOOOOOOOEEEE |
| 2681 | 69 | 2 | 1 | 0.130811 | OOEOOOOOOOEOOOEEOEEO |
| 3271 | 69 | 2 | 7 | 0.199475 | OOEOOOOOOOEOEOOOOOOE |
| 761 | 62 | 9 | 1 | 0.062149 | OOOOOOOOOEEOEOEEOOEE |
| 3085 | 62 | 4 | 5 | 0.062149 | OOOOEOOOOOOEEEOEOOEO |
| 3439 | 62 | 10 | 7 | 0.199475 | OOOOOOOOOOEOEOOEOOOE |
| 3973 | 59 | 7 | 5 | 0.199475 | OOOOOOOEOOOOEEOOOOOO |
| 2247 | 56 | 9 | 7 | 0.199475 | OOOOOOOOOEOOEOEOOOEO |
| 3981 | 56 | 3 | 5 | 0.130812 | OOOEOOOEOOOOOEEOEOEO |
| 3987 | 56 | 6 | 3 | 0.130812 | OOOOOOEEEOOEOOOOOOOE |

Known records replayed on CPU (exact `J`):

| n | status | tau | peak bits | tau match | word prefix |
| --- | --- | --- | --- | --- | --- |
| 3 | RETURNED | 5 | 6 | True | OOOEE |
| 9 | RETURNED | 5 | 8 | True | OOEOE |
| 193 | RETURNED | 70 | 900 | True | OOOEOOOOOOOEOOOEEOEEOOOO |
| 425 | RETURNED | 46 | 243 | True | OOOOOOOEOOEEOOOEOEEOOEOO |
| 761 | RETURNED | 62 | 851 | True | OOOOOOOOOEEOEOEEOOEEOOOE |
| 2183 | RETURNED | 54 | 19694 | True | OOEOOOOEOOOOOOOOEOOOEOOO |
| 3431 | RETURNED | 54 | 4634 | True | OOEOOOOEOOOOOEOEOOOOOEOO |
| 3889 | RETURNED | 77 | 3350 | True | OOOOOEOEOOOEOOEOEOEOOOOO |

`n=193` first-return length `70` and `n=3889` length `77` remain the
`n<=4000` delay records. `n=2183` remains the peak-bit record in that
window. Label: **EXACT COMPUTATION**. Rarity under `M0` is not an
explanation: the exact feature is a long expanding odd prefix, already
visible in the itinerary.

## 10. Scale dependence

`H` on `[N,2N)`-style bit bands from `n<=4000` and the `n<=10^5`
census:

- `n<=4000`: starts `3999`, returned `3999`,
  leftovers `[]`, max `H=77` at
  `n=3889`, max peak bits `19694` at
  `n=2183`.
- `n<=10^5`: starts `99999`, returned
  `99985`, leftovers `[11229, 15065, 15343, 15845, 17033, 30817, 48443, 63185, 78901, 88053, 93883, 95281, 98605, 99679]`,
  max completed `H=183` at `n=34175`.
  Leftovers are bit-cap / horizon, not a proof that `H=∞`.

| k | P(H>=k) n<=1e5 | count |
| --- | --- | --- |
| 1 | 1.0 | 99999 |
| 2 | 0.499995 | 49999 |
| 3 | 0.249842 | 24984 |
| 4 | 0.249842 | 24984 |
| 5 | 0.188082 | 18808 |
| 8 | 0.101331 | 10133 |
| 10 | 0.074091 | 7409 |
| 16 | 0.0394 | 3940 |
| 20 | 0.02851 | 2851 |
| 32 | 0.01096 | 1096 |
| 40 | 0.00661 | 661 |
| 54 | 0.00294 | 294 |
| 70 | 0.00128 | 128 |
| 77 | 0.00089 | 89 |
| 80 | 0.00078 | 78 |

Normalized excursion law: even starts remain `H=1`. Odd-start tails
stay heavy enough that `max H` grows from the `n<=4000` window to the
`n<=10^5` leftovers. The distribution of typical `H` is stable
(`H=1` on evens; short returns on most odds). The rare-event tail is
slowly drifting / record-driven, not a settled asymptotic. Label:
**COMPUTATIONALLY OBSERVED**.

## 11. Potential exact / statistical synthesis

The attractive architecture — statistical contraction, Atlas list of
exceptions, exact inequalities forbidding persistence — does **not**
close in Phase 0. The exceptions are exactly the starts that realize
a long odd expanding prefix. That is the definition of the expanding
branch plus the already-closed realization / adversarial / first-return
questions. No new finite exceptional family appears.

Existing exact certificates that remain in force:
`power_bound_contracts` (`3^o < 2^k ⇒ T_w(n)<n` for `n>=2`) and
`floorPower_odd_ge`. Label: **LEAN-CERTIFIED**. They already handle
every completed contracting itinerary. They do not bound `H(n)` uniformly.

## 12. What is NOT proved

- Negative mean drift does not imply every orbit terminates.
- `P(H>=k) → 0` in a window does not imply no exceptional orbit exists.
- An observed near-geometric run law does not imply an independent
  parity process.
- A fitted exponential tail is not a large-deviation theorem.
- `μ_J` is not a theorem. No candidate conjecture is opened.
- CUDA was not used. No GPU float defined `J`.

## 13. Decision

**STATISTICAL_ONLY**. Branch decision: **PARK**.

Large-scale log-log drift is negative and robust across the named ensembles, and the increment law approaches the branch terms at large bit length. The deterministic exceptional set is odd starts with long initial O-runs: the expanding branch, not a new exact family. The stochastic model does not yield a usable pointwise constraint. Typical contraction is not universal contraction.

Flags: drift `True`, run-law
`True`, LD `True`,
exceptional `False`, synthesis
`False`.

Best next question: none from this branch as an automatic sequel.
A later theorem phase would need a named measure and a genuine tail
inequality, not another census.

Pointwise gap on `n<=4000`, horizon `k=10`: almost-all contraction
rate `0.92123`; every-start contraction
by 10 is `False`; max `H=77`
at `n=3889`. Typical contraction is not universal
contraction.
