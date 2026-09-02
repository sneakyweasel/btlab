# Juggler one-step image-parity discrepancy

Status: **IMAGE_PARITY_CENSUS**

Standalone Archimedean counting phase on the exact floor-power map.
Not a Research Engine experiment, not a frequency theorem, and not a
termination theorem. Closed 2-adic, landing-θ, and probabilistic /
large-deviation branches stay closed.

## A. Object

Write `J(n) = isqrt(n)` on even `n` and `J(n) = isqrt(n^3)` on odd `n`.
The counting target is

```
O(N) = #{n <= N : J(n) odd}
D(N) = O(N) - N/2
```

This is image parity, the second itinerary letter, not start parity.
Uniform `P(n odd) = 1/2` is exact counting and is not the target.
Label of the split below: **EXACT COMPUTATION**.

`D(N) = D_E(N) + D_O(N)`, where `D_E` uses even starts and `D_O` uses
odd starts.

## B. Even cells — EXACT — HUMAN PROOF

For even `n`, `even_preimage_iff` says `J(n) = q` iff `q^2 <= n < (q+1)^2`.
Let `Q = floor(sqrt(N))`.

A complete cell of odd `q` is the interval `[q^2, (q+1)^2)` of length
`2q+1`. It starts at the odd square `q^2`, so it contains exactly `q`
even integers, all with odd image `q`. A complete even-`q` cell has
even image, so it contributes `0` to `O_E`.

There are `Q//2` complete odd cells `q = 1, 3, ..., 2(Q//2)-1`. Their
contribution is `1+3+...+(2(Q//2)-1) = (Q//2)^2`.

If `Q` is odd the last cell `[Q^2, N]` is an odd-image cell and adds
the even count in that range; if `Q` is even it adds `0`. This is the
closed form `even_image_odd_count`. It matches the one-pass census at
every recorded checkpoint: `True`.

The complete-cell discrepancy is `1/4` when `Q` is even and
`-(Q-1)/2` when `Q` is odd. The last cell has length at most `2Q+1`
and moves `D_E` by at most `(Q+1)/2`. Therefore

```
|D_E(N)| <= floor(sqrt(N)) + 1.
```

The census records `even_bound_holds = True`
on `n <= 1000000`. Label: **EXACT — HUMAN PROOF**, and
**REPARAMETERIZATION** of `even_preimage_iff`. This is not the promotion
theorem.

## C. Odd cells — n^{3/2} census

For odd `n`, `odd_preimage_iff` plus `odd_preimage_unique` say the cell
`m^2 <= n^3 < (m+1)^2` contains at most one integer. So `O_O(N)` is
the number of occupied odd-`m` singletons with occupant `<= N`, not a
length sum.

Equivalently, `J(n)` is odd iff `isqrt(n^3)` is odd. The fractional-part
form `{n^{3/2}/2} >= 1/2` is only a rewrite; every count below uses
`isqrt`. Label: **EXACT COMPUTATION**.

For odd `n >= 3`, `floorPower_odd_macro_direction` already splits the
two-step on this bit: `J(n)` even implies `T^2(n) < n`, and `J(n)` odd
implies `T^2(n) > n`. `D_O` is therefore also the discrepancy of
expanding versus contracting two-step odd starts. The lemma is cited,
not reproved. No two-step itinerary census.

## D. Prefix census

One pass on `n <= 1000000`. Label: **COMPUTATIONALLY VERIFIED**.

| N | O | D | D_E | D_O | max|D| | max|D_E| | max|D_O| | max|D_O|/N^{1/3} | max|D_O|/N^{1/2} |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 10 | 6 | 1.0 | -0.5 | 1.5 | 1.5 | 1.0 | 1.5 | 0.69623833 | 0.47434165 |
| 100 | 51 | 1.0 | 0.0 | 1.0 | 5.0 | 4.0 | 3.0 | 0.64633041 | 0.3 |
| 1000 | 498 | -2.0 | -5.0 | 3.0 | 14.0 | 15.0 | 8.5 | 0.85 | 0.2687936 |
| 10000 | 5005 | 5.0 | 0.0 | 5.0 | 57.0 | 49.0 | 23.5 | 1.09077338 | 0.235 |
| 100000 | 49949 | -51.0 | -36.0 | -15.0 | 198.0 | 157.0 | 56.0 | 1.20648343 | 0.17708755 |
| 1000000 | 499927 | -73.0 | 0.0 | -73.0 | 613.0 | 499.0 | 128.0 | 1.28 | 0.128 |

Odd-start spot through `n<=10000000`:

| N | O_O | D_O | max|D_O| | max|D_O|/N^{1/3} | max|D_O|/N^{1/2} |
| --- | --- | --- | --- | --- | --- |
| 10 | 4 | 1.5 | 1.5 | 0.69623833 | 0.47434165 |
| 100 | 26 | 1.0 | 3.0 | 0.64633041 | 0.3 |
| 1000 | 253 | 3.0 | 8.5 | 0.85 | 0.2687936 |
| 10000 | 2505 | 5.0 | 23.5 | 1.09077338 | 0.235 |
| 100000 | 24985 | -15.0 | 56.0 | 1.20648343 | 0.17708755 |
| 1000000 | 249927 | -73.0 | 128.0 | 1.28 | 0.128 |
| 10000000 | 2499896 | -104.0 | 229.5 | 1.06524464 | 0.07257427 |

No linear bias: `|D_O(N)|/N` at `N = 1000000` is
`7.3e-05`. The running odd-start
envelope tracks `N^{1/3}` more closely than `N^{1/2}`. The
`N^{1/3}` ratio stays order-1 on the window (about 0.65 to 1.65),
so the named class is `N^{1/3}` times a possible log factor, not a
proved exponent. Label: **OBSERVATION**.

Total `D` is even-cell dominated. The written target
`|O(N) - N/2| <= E(N)` therefore admits the elementary majorant
`E(N) = floor(sqrt(N)) + 1 + N/4`, which is useless, or
`E(N) = O(sqrt(N))` once `D_O = O(sqrt(N))` is granted by the census.
That total bound is not a new `n^{3/2}` law.

## E. What this is not

- Start-parity `P(n odd) = 1/2` is exact counting, already recorded in
  the probabilistic census. **KNOWN**.
- `landingParity = J(n) mod 2` is tautological in `T`.
  **REPARAMETERIZATION**.
- Letter 2 is not a 2-adic function of `n mod 2^P`. Already **CLOSE**.
- `θ = ρ/(2T+1)` does not predict the next landing. Already **CLOSE**.
- `P(O) = 1/2` as an orbit law is already **REFUTED**.
- `parity_frequency_theorem` stays `False`.

## F. Decision record

Classification **IMAGE_PARITY_CENSUS**.

The even-cell discrepancy is an explicit O(sqrt(N)) identity. The odd-start n^{3/2} count has no linear bias and tracks a named N^{1/3} envelope (max|D_O|/N^{1/3} ≈ 1.06524464 on the window), but that envelope is only a census.

This is not a termination theorem.
