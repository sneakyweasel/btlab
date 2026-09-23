# The (lambda, a, b) coordinate on x+1 is Williams 2026, not ours

Killed claim (20 September 2026): "the conserved 6-free part of `x + 1` along an odd
run, with `(v_2, v_3)` as a two-valuation clock, is a new organising principle for
the Collatz map".

Kind: `KNOWN`. It is the skeleton coordinate system of
`williams-2026-collatz-coordinates` (arXiv:2607.01718, compiled 3 July 2026), and the
correspondence is exact, verified on odd `n < 2e5`. Every odd `n` has a unique
`n + 1 = lambda 2^a 3^b` with `gcd(lambda,6) = 1`, `a >= 1`; her `(lambda, a, b)` is
`(6-free part of x+1, v_2(x+1), v_3(x+1))`. Her Theorem 3.6 and Proposition 3.11 are
the diagonal flow `(a,b) -> (a-1,b+1)` multiplying `n+1` by exactly `3/2`, i.e. the
`u -> 3u/2` conjugation; her Corollary 3.9 is Lemma 8's run length; her preserved row
index `k = a + b` is the first integral; her preserved `lambda` is the conserved
6-free part; her Proposition 3.10 is the boundary LTE statement; and her row `k` of
the principal skeleton traversed from `(a,0)` is the closed form
`T^j(2^a - 1) = 3^j 2^(a-j) - 1`.

Do not reopen as: a two-valuation clock, a conserved `6`-free or unit part, a
`(v_2, v_3)` first integral, a lattice-translation reading of the odd run, or a
Mersenne/Thabit column observation. All of it is in that paper, with priority. The
20 September prime fan-out's `six-free-invariant` direction is this entry; its
`general-exponent-family` direction is answered by her open problem (2), where
`pn + 1 = lambda 2^a p^(b+1) - (p-1)` needs `p - 1` to be a power of two and `p = 3`
is the unique case preserving the weight `a + b`.

What is NOT hers, and stands: the paper is pure Collatz, with no Juggler and no
floor-power map. The exponent transport (`exactRun(n) = v_2(e(n))`, `HasPowTwoDepth`,
the attained floors, the monochrome fibre, the `N^(2^-k)` against `2^(-k) N` density
contrast), the Juggler floor-power closed forms, the `3x-1` verification floor and its
period bound, and the negative-side window are the laboratory's.

Dossiers: [exponent_valuation_mirror](../problems/juggler_exponent_valuation_mirror.md),
[mersenne_floor_power](../problems/juggler_mersenne_floor_power.md).
