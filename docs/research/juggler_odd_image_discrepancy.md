# Juggler odd-image discrepancy

Status: **ODD_IMAGE_DISCREPANCY_GREEN**

Standalone Archimedean counting phase on the odd-start sequence
`s(n)=(-1)^{floor(n^{3/2})}`. Not a halt theorem and not a
frequency theorem. Closed PE / residual / 2-adic / landing-θ /
probabilistic-LD branches stay closed.

## 1. Exact sequence definition

For odd `n`,

```
a_n = floor(n^{3/2}) = isqrt(n^3)
s(n) = (-1)^{a_n}
S_O(N) = sum_{odd n <= N} s(n)
```

This is exact integer arithmetic. Label: **EXACT IDENTITY**.

If `O_O(N)` is the number of odd `n<=N` with `a_n` odd, then
`S_O(N) = #{odd n<=N} - 2 O_O(N) = -2 D_O(N)`, where `D_O` is the
Phase-0 odd-start discrepancy. Census identity holds:
`True`. Label: **EXACT IDENTITY**.

`floor(x)` is odd iff `{x/2} >= 1/2`. So `s(n)=-1` iff
`{n^{3/2}/2} >= 1/2`. No complex exponential is substituted for
the floor. Label: **EXACT IDENTITY**.

## 2. Cell decomposition

`C_m = {odd n : a_n = m}` is the odd part of the cube cell
`m^2 <= n^3 < (m+1)^2`. `odd_preimage_unique` says that cell contains at
most one integer, so `c_m = |C_m| in {0,1}`. Label:
**LEAN-CERTIFIED** (`odd_preimage_unique`).

Prefix `m<= 8000`: value counts `{0: 7800, 1: 200, 'ge2': 0}`,
`c_m <= 1` is `True`. Label: **EXACT COMPUTATION**.

Therefore

```
S_O(N) = sum_m (-1)^m c_m
```

over occupied cells with occupant `<=N`, plus nothing from empty
cells. Label: **EXACT IDENTITY**.

Occupied cells for `n<= 1000000`: `500000`.
Adjacent occupied pairs `(m,m+1)`: `0`.
Typical gaps are `a_{n+2}-a_n ~ 3 sqrt(n)`, so occupied cells are
isolated. Label: **COMPUTATIONALLY OBSERVED**.

## 3. Elementary bounds

Adjacent pairing: `sum_r |c_{2r}-c_{2r+1}|` on occupied pairs is
`500000`, ratio to `#odds` is
`1.0`. Because occupied
cells are isolated, each occupant contributes `1` to the variation.
This is a linear bound, i.e. the trivial `|S_O| <= #odds`. Label:
**COUNTEREXAMPLE** to pairing-as-cancellation.

Sign runs of `s(n)` on consecutive odd `n`: `250000`
runs, max length `52`, mean
`2.0`, length-1 count
`125978`. Jumps `a_{n+2}-a_n` are odd with
frequency `0.499999`. Label:
**COMPUTATIONALLY OBSERVED**. No deterministic pairing of runs was
found that beats the trivial bound.

The even-start bound `|D_E| <= floor(sqrt(N))+1` is not restated as
the main theorem. Label: **EXACT — HUMAN PROOF** in the parent
branch; rejected here as the odd-start result.

## 4. Analytic bounds

Write `n=2r+1` and `g(r)=(2r+1)^{3/2}/2`. Then `S_O` is twice the
discrepancy of `{g(r)}` from `1/2`. Label: **EXACT IDENTITY**.

`g''` is positive and decreasing. Van der Corput on dyadic blocks,
plus Erdős–Turán, gives the explicit interval bound

```
|S_O(N)| << N^{5/6}.
```

The argument is in the dossier. The floor is not replaced by
`exp(pi i n^{3/2})`: the exponential sums are those of
`exp(2 pi i k g(r))`, which is the standard discrepancy expansion of
`{g(r)}`. Label: **ANALYTIC THEOREM**.

This is `O(N^{1-1/6})`. It is not the observed `N^{1/3}` and is
not claimed sharp. Implied constants are those of the two cited
lemmas, not fitted.

On the census window the inequality holds with room:
`max|S_O|/N^{5/6}` at `N=1000000` is
`0.00256`.
Label: **EXACT COMPUTATION**.

## 5. Computational scaling

One exact pass, `n<= 1000000`. Label: **EXACT COMPUTATION**.

| N | S_O | max|S_O| | argmax | max/N^{1/3} | max/N^{1/2} | max/N^{5/6} |
| --- | --- | --- | --- | --- | --- | --- |
| 10 | -3 | 3 | 5 | 1.39247665 | 0.9486833 | 0.44033978 |
| 100 | -2 | 6 | 31 | 1.29266081 | 0.6 | 0.12926608 |
| 1000 | -6 | 17 | 705 | 1.7 | 0.5375872 | 0.05375872 |
| 10000 | -10 | 47 | 5565 | 2.18154675 | 0.47 | 0.02181547 |
| 100000 | 30 | 112 | 74327 | 2.41296685 | 0.3541751 | 0.00763047 |
| 1000000 | 146 | 256 | 985351 | 2.56 | 0.256 | 0.00256 |

Spot `N=10000000`: `S_O=208`, `max|S_O|=459` at `n=6363789`, `max/N^{1/3}=2.13048927`, `max/N^{5/6}=0.00067372`.

Descriptive log-log slope of `max|S_O|` vs `N` on
`[1000, 1000000]` is `0.34595847`. This is a
diagnostic, not an exponent theorem. Label: **COMPUTATIONALLY OBSERVED**.

## 6. Lower-bound / sharpness evidence

Running-max witnesses exist (last records stored). At
`N=1000000`, `max|S_O|=256` at
`n=985351`. Relative to `N^{1/3}` the ratio stays
order-1; relative to `N^{5/6}` it tends to `0`. No explicit
infinite family `|S_O(N_j)| >= c N_j^alpha` was constructed. Label:
**COMPUTATIONALLY OBSERVED**. The `N^{1/3}` envelope is **not** a
**CANDIDATE CONJECTURE**.

## 7. Structured Juggler-image sets

`S_O(A)` sums `s(x)` over odd `x in A`, not over the starts that
produced `A`. Interval bounds do not apply automatically.

| set | N | |A| | odd | diam | S_O(A) | |S|/odd | |S|/|A| |
| --- | --- | --- | --- | --- | --- | --- | --- |
| J([1,N]) | 100 | 58 | 29 | 985 | 3 | 0.10344828 | 0.05172414 |
| J^2([1,N]) | 100 | 49 | 22 | 30913 | 12 | 0.54545455 | 0.24489796 |
| J([1,N]) | 1000 | 526 | 265 | 31575 | 19 | 0.07169811 | 0.03612167 |
| J^2([1,N]) | 1000 | 394 | 192 | 5610674 | -14 | 0.07291667 | 0.03553299 |
| J([1,N]) | 10000 | 5089 | 2551 | 999850 | -7 | 0.00274402 | 0.00137552 |
| J^2([1,N]) | 10000 | 3408 | 1707 | 996178937 | -63 | 0.03690685 | 0.01848592 |
| J([1,N]) | 100000 | 50293 | 25132 | 31622302 | -48 | 0.00190992 | 0.00095441 |
| J^2([1,N]) | 100000 | 30344 | 15202 | 177815932888 | 92 | 0.00605184 | 0.0030319 |
| J([1,N]) | 1000000 | 500950 | 250401 | 999998500 | -29 | 0.00011581 | 5.789e-05 |
| J^2([1,N]) | 1000000 | 280771 | 140416 | 31619005707956 | -32 | 0.00022789 | 0.00011397 |
| T_O | 10000 | 5000 | 2505 | 999850 | -5 | 0.00199601 | 0.001 |
| T_E | 10000 | 100 | 50 | 100 | -2 | 0.04 | 0.02 |
| T_OE | 10000 | 902 | 451 | 999 | -7 | 0.01552106 | 0.00776053 |
| T_OO | 10000 | 2505 | 1255 | 996178937 | -53 | 0.04223108 | 0.02115768 |
| T_EO | 10000 | 50 | 26 | 985 | 4 | 0.15384615 | 0.08 |
| T_OOE | 10000 | 1250 | 633 | 31548 | -3 | 0.00473934 | 0.0024 |
| T_OOOEE | 10000 | 317 | 153 | 2367 | -5 | 0.03267974 | 0.01577287 |

Label: **EXACT COMPUTATION** of the listed finite sets.
Normalization is `|S_O(A)| / #{odd x in A}` and
`|S_O(A)| / |A|`. Diameter is recorded and is not used as a fake
interval length.

## 8. Iteration tests

The table above includes `J([1,N])` and `J^2([1,N])` on the same
grid. Numerical smallness is not a propagation theorem. Label:
**COMPUTATIONALLY OBSERVED**. Flag
`image_balanced=True`,
`image_concentrated=False`.

## 9. Potential deterministic parity theorem

An interval `O(N^{5/6})` bound replaces “`P(O)≈1/2` on `[1,N]`
odds after one odd step” by an explicit discrepancy rate. It does
not by itself control branch frequencies along orbits, and it does
not transfer to arbitrary Juggler-generated sets. Label:
**HEURISTIC** for the desired counting-to-dynamics chain; not a
drift theorem.

## 10. Counterexamples

- Adjacent `c_{2r}-c_{2r+1}` pairing as a sublinear bound.
  **COUNTEREXAMPLE** (variation / `#odds` ≈
  `1.0`).
- “`N^{1/3}` is the theorem.” **REJECTED** as a promotion.
- “`exp(pi i n^{3/2})` may replace the floor.” **REJECTED**; the
  exact object is `{n^{3/2}/2}`.
- Interval bound used on a non-interval `A` without a transfer
  proof. **REJECTED**.

## 11. Lean candidates

Existing: `odd_preimage_unique`, `odd_preimage_iff`,
`landingParity_odd_iff`, `floorPower_odd_macro_direction`.
Present: `{'sorry_free': True, 'odd_preimage_unique': True, 'odd_preimage_iff': True, 'floorPower_odd_macro_direction': True, 'landingParity_odd_iff': True, 'no_forbidden_engines': True}`.

Not added: van der Corput / Erdős–Turán. The elementary cell-sum
identity is a packaging of `odd_preimage_unique` and is not a new Lean
file. No `sorry`.

## 12. Decision

Classification **ODD_IMAGE_DISCREPANCY_GREEN**.

S_O(N) = -2 D_O(N) and the cell rewrite S_O = sum_m (-1)^m c_m with c_m in {0,1} are exact. Adjacent pairing has linear variation and is not a cancellation theorem. The fractional-part identity plus van der Corput / Erdős–Turán give the explicit interval bound |S_O(N)| << N^{5/6}. The observed N^{1/3} envelope is not promoted. One-step Juggler images stay small relative to |A_odd|; that is a census, not a transfer theorem.

This is not a termination theorem.
