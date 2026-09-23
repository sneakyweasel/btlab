# Prime divisors of the cycle gap are a dead direction, by a density theorem

Killed claim (20 September 2026): "a prime that never divides the pinned gap
`3^o - 2^K` would constrain the cycle problem".

Kind: `METHOD_OBSTRUCTION`. There is no such prime. Writing `m_p` for
`|<2><3>|` in `(Z/p)^*`, the pairs `(K, o)` with `p | 3^o - 2^K` form a sublattice
of index exactly `m_p`, and along the pinned diagonal `o(K) = floor(K log_2 3) + 1`
the density of hits is exactly `1 / m_p`, by Weyl on `{K theta / m}` -- positive
for every prime `p` outside `{2, 3}`. So every prime divides the pinned gap at a
positive density of lengths and no prime and no length is excluded. Verified
independently: 44 primes `5 <= p < 200` against all `(K, o)` in `[0,60]^2`, 163724
triples, 0 disagreements; observed densities for all 60 primes `5 <= p < 300` at
`K <= 20000` match `1 / m_p` digit for digit, with no prime never hit.

The quadratic-residue refinements are real and equally inert: `K` even with `o` odd
forces `p = +-1 mod 12`, `K` odd with `o` even forces `p = +-1 mod 8`, both odd
forces `p` in `{1, 5, 19, 23} mod 24`; in particular `5` never divides the gap when
`K` is odd and `o` even, checked to `K <= 20000` and consistent with the divisor
lists at the leftover lengths 19, 25781, 176251 and 780239. None of this changes a
bound, a floor, a threshold or a word count.

`p = 2` and `p = 3` are the complete excluded set, already owned as EXACT by the
REFUTED `juggler_cycle_padic_coupling`. The reason classical primitive-divisor
theory does not reach the gap is already recorded at
`J-repunit-floor-power-is-closed-form`: `2^n - 1` is a one-base Cunningham number
and `3^o - 2^K` has two bases with two independently moving exponents, so Bang,
Zsigmondy and Carmichael do not apply. The unit case is settled elementarily --
`|3^o - 2^K| = 1` has only `(o,K) = (0,1), (1,1), (1,2), (2,3)`, which are the
degenerate point and the three known cycles, and `|gap| = 3` forces `3 | 2^K`, so a
fourth cycle has `|2^K - 3^o| >= 5` (recorded in `literature/mihailescu-2004-catalan.json`).

Do not reopen as: a search for a prime avoiding the gap, a congruence obstruction
on cycle lengths from a fixed prime, a Zsigmondy or Bang argument on `3^o - 2^K`,
or a Mersenne/Fermat primality reading of the leftover lengths.
