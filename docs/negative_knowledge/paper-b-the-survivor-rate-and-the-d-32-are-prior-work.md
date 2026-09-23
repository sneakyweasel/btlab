# Paper B: the survivor rate and the `d^(-3/2)` are prior work

Two pieces of the survivor asymptotic were read as laboratory findings and are
not. Settled 19 September 2026 by reading the sources OEIS A076227 links, under
`J-paper-b-survivors-are-oeis-a076227`.

The exponential rate is **Lagarias 1985, Theorem D**. In the survey's notation
`1 - F(k) <= 2^(-eta k)` with `eta = 1 - H(beta)` about `.05004`, `H` the binary
entropy function, and the remark after it supplies the matching lower bound
`2^(-(eta+epsilon)k)`, so it is two-sided on the exponential scale. The set the
proof bounds, the inflating words of length `k`, is our `N_k` outright, and
`2^(-eta) = 0.9659065532334377236055` equals `beta^(-beta)(1-beta)^(beta-1)/2`
on all thirty digits computed. Our Lean `neverNegCount_div_pow_le_theta`
(`J-survivor-count-decay`) is Theorem D's upper half.

The `d^(-3/2)` is **Hikawa, July 2026, Conjecture 7.1**,
`W(d) = Theta(d^(-3/2) 2^(gamma d))`, from the residual tracking
`-(3/2) log_2 d` to within `0.3` bits. His Section 6 proves the rate again by a
cycle lemma, in the weight basis, and his constants are Lagarias's `eta` over
`beta`.

Kind: **prior work**, not a refutation. Do not re-derive either as a laboratory
finding, and do not write the asymptotic up as a discovery -- it is a refinement
of Theorem D and of Conjecture 7.1. What survives the search is the prefactor
itself: the oscillation in `frac(d beta)`, the jump spectrum, the closed form for
`a_1`, and the Fourier identity, none of which appears in any source that could
be read. **The readability caveat is discharged, 21 September 2026.** All four
sources of the cluster have now been read from their own texts -- the January
Hikawa-Nakanishi paper last, the one the clause was bounded by -- and the January
text contains no asymptotic at all: no growth constant, no power of the length,
no oscillation, and it never names A076227, A100982 or A260591. So the prefactor
clause is no longer bounded by what was readable; it is bounded only by the
sources themselves. The prior-art clock splits: the counting objects start in
January 2026, the asymptotic layer not until July. Source-by-source reading:
[jump spectrum](../problems/juggler_jump_spectrum.md).

