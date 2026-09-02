# Juggler parity discrepancy transfer

Status: **TRANSFER_COMPLEX**

One-step question only: can the exact image-parity sum
`D(I)=sum_{n odd in I} (-1)^{floor(n^{3/2})}` be transferred
from an integer interval to a Juggler-generated set? Not a halt
theorem and not a frequency theorem. Closed compression / PE /
residual / 2-adic / landing-θ / LD branches stay closed. No Weyl
engine.

## 1. Existing interval theorem

On the anchored prefix,

```
S_O(N) = sum_{n <= N, n odd} (-1)^{floor(n^{3/2})}
|S_O(N)| << N^{5/6}.
```

Label: **CLASSICAL ANALYTIC BOUND** (parent branch; van der Corput
+ Erdős–Turán). This is the starting point, not the target. It is
not a transfer theorem. Label for that refusal: **REJECTED** as
`IMAGE_TRANSFER`.

On this window `N=1000000`: `S_O=146`,
`max|S_O|=256` at `n=985351`. Label:
**EXACT COMPUTATION**.

## 2. Exact interval discrepancy

For `I=[A,B] ∩ Z`,

```
D(I) = sum_{n in O(I)} (-1)^{J_O(n)}
     = S_O(B) - S_O(A-1)
     = sum_m (-1)^m c_I(m),
```

with `c_I(m) in {0,1}` by `odd_preimage_unique`. Differencing identity
holds: `True`. Cell-sum identity
holds: `True`. Label:
**EXACT IDENTITY**; uniqueness **LEAN-CERTIFIED**.

The source-parity sum `sum_{n in O(I)} (-1)^n` equals
`-#O(I)` and is not `D(I)`. The two differ on `[1,99]`:
`True`. Label:
**EXACT IDENTITY**.

Differencing plus the parent bound gives only

```
|D([A,B])| <= |S_O(B)| + |S_O(A-1)| << B^{5/6}.
```

This depends on the right endpoint, not on `|I|` alone. On the
census window the trivial pairing of prefixes also yields
`|D(I)| <= 512`. Label:
**CLASSICAL ANALYTIC BOUND** / **EXACT COMPUTATION**. Neither
statement is `|I|`-uniform in `A`, and neither is a transfer
theorem.

A short-interval van der Corput sketch produces a location-dependent
majorant of the shape `min(|I|, C(|I| A^{-1/6} + A^{1/4}))`.
That is a **CANDIDATE THEOREM** in the same classical toolkit; it is
not proved in Lean and is not `|I|`-uniform.

## 3. Expanding image structure

`J_O` is nondecreasing on odd sources, and `c_m <= 1` forces the
occupied images to be strictly increasing. Endpoints of
`Y=J_O(O([A,B]))` are exactly `J_O` of the first and last odd
points of `I`. Label: **EXACT IDENTITY**.

| A | B | |Y| | span | holes | components | min_g | max_g | shape |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 20 | 10 | 82 | 72 | 10 | 4 | 12 | highly_fragmented |
| 1 | 100 | 50 | 985 | 935 | 50 | 4 | 30 | highly_fragmented |
| 1 | 1000 | 500 | 31575 | 31075 | 500 | 4 | 95 | highly_fragmented |
| 1 | 10000 | 5000 | 999850 | 994850 | 5000 | 4 | 300 | highly_fragmented |
| 1 | 1000000 | 500000 | 999998500 | 999498500 | 500000 | 4 | 3000 | highly_fragmented |

On every nonempty sample above, `Y` is not a single interval: the
integer hull has many holes and the occupied set is a union of
`|Y|` singletons once gaps are at least 2. Label:
**EXACT COMPUTATION**. Shape: highly fragmented with growing gaps
`~ 3 sqrt(n)`. An independent discrepancy estimate on `Y` would
require a sparse-sequence argument. That is Weyl territory and is
not opened.

## 4. Gap-parity formulation

For consecutive odd sources, `g_j = J_O(n+2)-J_O(n)` is an exact
integer. Then `s(n+2)=s(n)` iff `g_j` is even. The smooth main term
is the integer proxy `3 floor(sqrt(n))`; the floor correction is
`g_j - 3 floor(sqrt(n))`, kept as an integer and never used as a
parity. Label: **EXACT IDENTITY**.

Census `n<=1000000`: `499999` gaps, odd-gap
fraction `0.499999`, min gap `4` at
`n=1`, max gap `3000` at
`n=999353`, floor-error range
`[0, 3]`, lag-1
same-parity frequency `0.50391402`. Label:
**EXACT COMPUTATION**. Adjacent gap parities are not a deterministic
pairing law. No independence is assumed.

## 5. Record intervals

For each length `L` on the grid, `A` runs through every admissible
start in `[1, N-L+1]`. `[1,L]` is not assumed worst.

| L | A | B | max|D| | |Y| | pattern | |D|/L | anchored |D| |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 10 | 10 | 19 | 5 | 5 | monochrome | 0.5 | 3 |
| 20 | 1014 | 1033 | 10 | 10 | monochrome | 0.5 | 2 |
| 50 | 55670 | 55719 | 25 | 25 | monochrome | 0.5 | 1 |
| 100 | 813554 | 813653 | 50 | 50 | monochrome | 0.5 | 2 |
| 200 | 817066 | 817265 | 48 | 100 | pos | 0.24 | 14 |
| 500 | 85178 | 85677 | 58 | 250 | pos | 0.116 | 4 |
| 1000 | 222446 | 223445 | 92 | 500 | pos | 0.092 | 6 |
| 2000 | 523180 | 525179 | 126 | 1000 | pos | 0.063 | 12 |
| 5000 | 950222 | 955221 | 204 | 2500 | pos | 0.0408 | 12 |
| 10000 | 650084 | 660083 | 230 | 5000 | pos | 0.023 | 10 |
| 20000 | 275056 | 295055 | 252 | 10000 | neg | 0.0126 | 22 |
| 50000 | 630482 | 680481 | 256 | 25000 | pos | 0.00512 | 26 |
| 100000 | 879930 | 979929 | 326 | 50000 | pos | 0.00326 | 30 |

Maximal monochromatic run: length `52` on
`[952525,952627]` with
`|D|=52`. Label: **EXACT COMPUTATION**.
That interval realises `|D|=#O(I)`, so any claimed
`|D| <= C |I|^alpha` with `alpha<1`, uniform in `A`, already fails
on a short interval. Longer lengths inside `[1,N]` cannot exceed
the prefix majorant `512`; that upper
cut is an artefact of the ambient window, not translation
uniformity at large `A`.

## 6. Location dependence

Fixed-length slices `[1,L]`, dyadic translates, squares, cubes, and
hard Atlas starts.

| A | B | L | D | |D|/L | family |
| --- | --- | --- | --- | --- | --- |
| 1 | 100 | 100 | -2 | 0.02 | anchored |
| 2 | 101 | 100 | -2 | 0.02 | dyadic |
| 4 | 103 | 100 | -2 | 0.02 | square |
| 9 | 108 | 100 | -2 | 0.02 | square |
| 16 | 115 | 100 | -8 | 0.08 | square |
| 32 | 131 | 100 | -18 | 0.18 | dyadic |
| 37 | 136 | 100 | -16 | 0.16 | hard |
| 64 | 163 | 100 | -10 | 0.1 | square |
| 74 | 173 | 100 | -12 | 0.12 | hard |
| 100 | 199 | 100 | -12 | 0.12 | square |
| 128 | 227 | 100 | 0 | 0.0 | dyadic |
| 163 | 262 | 100 | 4 | 0.04 | hard |
| 173 | 272 | 100 | 2 | 0.02 | hard |
| 193 | 292 | 100 | 10 | 0.1 | hard |
| 229 | 328 | 100 | 10 | 0.1 | hard |
| 256 | 355 | 100 | 8 | 0.08 | square |
| 326 | 425 | 100 | 8 | 0.08 | hard |
| 346 | 445 | 100 | 4 | 0.04 | hard |
| 357 | 456 | 100 | 4 | 0.04 | hard |
| 386 | 485 | 100 | -4 | 0.04 | hard |
| 458 | 557 | 100 | -20 | 0.2 | hard |
| 714 | 813 | 100 | 2 | 0.02 | hard |
| 961 | 1060 | 100 | 6 | 0.06 | square |
| 1024 | 1123 | 100 | -8 | 0.08 | square |

Label: **EXACT COMPUTATION**. Absolute `D` on a fixed length varies
with `A`, but inside this window it remains bounded by twice the
prefix max. The useful proved dependence is the right endpoint
`B`, not a collapse to `|I|` alone.

## 7. One-step transfer tests

The transfer object is `D(Y)` with `Y=J_O(O(I))`: the same sign
sum, now evaluated on the generated image as a source set. `D(I)`
itself is not counted as transfer.

| source | |Y| | odd | D(Y) | |D|/#odd | depth |
| --- | --- | --- | --- | --- | --- |
| [1,20] Y | 10 | 4 | 0 | 0.0 | 1 |
| [1,50] Y | 25 | 12 | 2 | 0.16666667 | 1 |
| [1,100] Y | 50 | 26 | 4 | 0.15384615 | 1 |
| [1,200] Y | 100 | 57 | 17 | 0.29824561 | 1 |
| [1,500] Y | 250 | 127 | 15 | 0.11811024 | 1 |
| [1,1000] Y | 500 | 253 | 13 | 0.0513834 | 1 |
| [1,2000] Y | 1000 | 506 | 2 | 0.00395257 | 1 |
| [1,10000] Y | 5000 | 2505 | -5 | 0.00199601 | 1 |
| [1,100000] Y | 50000 | 24985 | -51 | 0.00204122 | 1 |
| [1,1000000] Y | 500000 | 249927 | -19 | 7.602e-05 | 1 |
| [2,101] Y | 50 | 26 | 6 | 0.23076923 | 1 |
| [2,1001] Y | 500 | 252 | 14 | 0.05555556 | 1 |
| [2,10001] Y | 5000 | 2504 | -4 | 0.00159744 | 1 |
| [4,103] Y | 50 | 26 | 6 | 0.23076923 | 1 |
| [4,1003] Y | 500 | 252 | 16 | 0.06349206 | 1 |
| [4,10003] Y | 5000 | 2503 | -3 | 0.00119856 | 1 |
| [8,107] Y | 50 | 26 | 6 | 0.23076923 | 1 |
| [8,1007] Y | 500 | 252 | 14 | 0.05555556 | 1 |
| [8,10007] Y | 5000 | 2502 | -4 | 0.00159872 | 1 |
| [9,108] Y | 50 | 26 | 6 | 0.23076923 | 1 |
| [9,1008] Y | 500 | 252 | 14 | 0.05555556 | 1 |
| [9,10008] Y | 5000 | 2502 | -4 | 0.00159872 | 1 |
| [16,115] Y | 50 | 29 | 5 | 0.17241379 | 1 |
| [16,1015] Y | 500 | 253 | 13 | 0.0513834 | 1 |
| [16,10015] Y | 5000 | 2501 | -5 | 0.0019992 | 1 |
| [27,126] Y | 50 | 31 | 9 | 0.29032258 | 1 |
| [27,1026] Y | 500 | 252 | 14 | 0.05555556 | 1 |
| [27,10026] Y | 5000 | 2504 | -6 | 0.00239617 | 1 |
| [32,131] Y | 50 | 34 | 10 | 0.29411765 | 1 |
| [32,1031] Y | 500 | 252 | 14 | 0.05555556 | 1 |

Label: **EXACT COMPUTATION**. Large odd-images can look balanced
relative to `#odd(Y)`. That is a census. Small and specially placed
images need not. The interval theorem does not apply because `Y`
is not an interval.

## 8. Weighted transfer tests

Deterministic weights `w=1`, `w=n`, and the monotone Jacobian proxy
`w=3 floor(sqrt(n))`. No learned weights.

| A | B | |D_1|/#odd | |D_n|/mass | |D_jac|/mass |
| --- | --- | --- | --- | --- |
| 1 | 20 | 0.2 | 0.64 | 0.46153846 |
| 1 | 50 | 0.04 | 0.0368 | 0.00934579 |
| 1 | 100 | 0.04 | 0.1344 | 0.09032258 |
| 1 | 200 | 0.14 | 0.2058 | 0.18526786 |
| 1 | 500 | 0.016 | 0.020896 | 0.01662971 |
| 1 | 1000 | 0.012 | 0.004264 | 0.00776699 |
| 1 | 2000 | 0.012 | 0.000848 | 0.00641069 |
| 1 | 10000 | 0.002 | 0.00027544 | 0.00021158 |
| 1 | 100000 | 0.0006 | 0.0007171 | 0.00083625 |
| 1 | 1000000 | 0.000292 | 0.00053385 | 0.00041715 |
| 37 | 136 | 0.32 | 0.37069767 | 0.35023041 |
| 163 | 262 | 0.08 | 0.12433962 | 0.1025641 |
| 173 | 272 | 0.04 | 0.0609009 | 0.05 |
| 193 | 292 | 0.2 | 0.22380165 | 0.21010638 |
| 229 | 328 | 0.2 | 0.18158273 | 0.19059406 |
| 357 | 456 | 0.08 | 0.0720197 | 0.07520325 |

Label: **EXACT COMPUTATION**. Normalised cancellation under `n` or
the Jacobian is not uniformly stronger than the unweighted sum.
`WEIGHTED_TRANSFER_GREEN` is `False`.
Weights are not piled on.

## 9. Diagnostic iterated images

`I_1=J(I_0)` and `I_2=J(I_1)` on small exact samples only. No
iterated theorem.

| source | |J^2| | odd | D | |D|/#odd |
| --- | --- | --- | --- | --- |
| [1,20] J2 | 20 | 11 | -7 | 0.63636364 |
| [37,56] J2 | 20 | 4 | 2 | 0.5 |
| [163,182] J2 | 20 | 6 | -4 | 0.66666667 |
| [173,192] J2 | 20 | 2 | 2 | 1.0 |
| [1,50] J2 | 50 | 23 | 1 | 0.04347826 |
| [37,86] J2 | 50 | 14 | 12 | 0.85714286 |
| [163,212] J2 | 50 | 22 | -14 | 0.63636364 |
| [173,222] J2 | 50 | 23 | -15 | 0.65217391 |
| [1,100] J2 | 100 | 45 | 21 | 0.46666667 |
| [37,136] J2 | 100 | 41 | 7 | 0.17073171 |
| [163,262] J2 | 100 | 40 | -16 | 0.4 |
| [173,272] J2 | 100 | 36 | -14 | 0.38888889 |
| [1,200] J2 | 200 | 87 | -7 | 0.08045977 |
| [37,236] J2 | 200 | 89 | -23 | 0.25842697 |
| [163,362] J2 | 200 | 67 | -15 | 0.2238806 |
| [173,372] J2 | 200 | 64 | -10 | 0.15625 |
| [1,500] J2 | 500 | 177 | -33 | 0.18644068 |
| [37,536] J2 | 500 | 165 | -41 | 0.24848485 |

Label: **EXACT COMPUTATION**. Concentration on a `J^2` sample is
not a contradiction to a hypothetical one-step theorem; it is a
warning that unweighted iteration is not automatic. No
`ITERATED_TRANSFER_GREEN`.

## 10. Candidate transfer inequalities

- `|D([A,B])| << B^{5/6}` by differencing. **CLASSICAL ANALYTIC BOUND**.
  Not new. Not transfer.
- `|D([A,B])| <= C |I|^alpha` uniformly in `A`. **COUNTEREXAMPLE**
  (monochromatic run).
- `|D(Y)| <= C |I|^alpha` or `C |Y|^alpha` for `Y=J_O(O(I))`.
  **CANDIDATE THEOREM**, not established. Census smallness on some
  large `Y` is not a proof. Concentration samples refute uniformity.
- Push-forward of `f(m)=(-1)^m` through `J_*`. Not opened: the
  basic parity case has no surviving one-step bound.
- Branch-frequency / log-log drift from transferred discrepancy.
  Not opened.

## 11. Counterexamples

- `|I|`-uniform sublinear bound: run
  `[952525,952627]` of `52`
  odd sources, `|D|=#odds`. **COUNTEREXAMPLE**.
- “`Y` is an interval.” **COUNTEREXAMPLE**; see the structure table.
- “Prefix `N^{5/6}` is a transfer theorem.” **REJECTED**.
- “Source parity is the object.” **REJECTED**.
- Uniform transfer to every generated set:
  `[1000,1099] Y` has 25 odd points and |D|/#odd=0.36.
  Label: **COUNTEREXAMPLE** if a concentration row exists.

## 12. Decision

Classification **TRANSFER_COMPLEX**. Branch
**CLOSE**.

D([A,B]) equals the prefix difference S_O(B)-S_O(A-1), so the classical |S_O(N)| << N^{5/6} bound yields only a location-dependent majorant << B^{5/6}. That is not a transfer theorem and is not |I|-uniform: a monochromatic run of length 52 on [952525,952627] has |D|=#odds. The expanding image Y=J_O(O(I)) is strictly increasing and highly fragmented, so the interval theorem does not apply to Y. Witness: Y of [1000,1099] has 25 odd points and |D(Y)|/#odd(Y)=0.36. 19 odd-images with at least 20 odd points concentrate at level 0.25; 12 diagnostic J^2 samples do as well. Interval cancellation does not survive Juggler-generated sets in a useful uniform form.

Flags: `{'INTERVAL_UNIFORM_GREEN': False, 'IMAGE_TRANSFER_GREEN': False, 'WEIGHTED_TRANSFER_GREEN': False, 'OPERATOR_TRANSFER_GREEN': False, 'ITERATED_TRANSFER_GREEN': False, 'DRIFT_BRIDGE_GREEN': False, 'TRANSFER_COMPLEX': True}`.

This is not a termination theorem. `parity_frequency_theorem` stays
false. No Lean analytic-number-theory file was added.
