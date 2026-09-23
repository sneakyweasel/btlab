# A Juggler result about words alone is a Collatz result

Both maps realise the same additive walk: accelerated Collatz moves `log x` by
`-log 2` or `+log(3/2)`, and Juggler moves `log log n` by the same two steps,
because `n -> floor(n^(3/2))` multiplies `log n` by `3/2`
(`J-juggler-is-collatz-one-exponential-up`, verified to `2e-16`). So the two
problems share the multiplier semigroup, the non-contracting condition
`3^o >= 2^m`, and therefore every statement whose content is the combinatorics
of those words.

Kind: `REPARAMETERIZATION` of scope, not of any result.
`J-word-density-results-are-not-juggler-specific`. By this test the survivor
recursion, the empty-window theorem, the transposition cost, the jump spectrum,
`a_1` and the ladder profile all belong to Collatz as well.

What remains Juggler-specific is everything using how orbits *realise* words:
Hypothesis FD, the Weyl differencing, the kernel bounds, and the densities
resting on them. For Collatz that half is free -- Terras makes the parity word a
function of `x mod 2^d`, bijectively -- which is precisely why Juggler is not an
easier Collatz but Collatz's word problem plus a Weyl-sum problem.

Before recording a row as a Juggler result, ask whether its statement mentions
how words are realised. If it does not, the Collatz literature is where priority
lives, and the row should say so. This is the same failure as
`J-paper-b-survivors-are-oeis-a076227` one level up: there a sequence was
searchable and nobody searched; here the theorems are about an object under
another name.
