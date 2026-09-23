# The Mersenne numbers in the Lemma 8 floor carry no prime content

Killed claim (20 September 2026): "the Lemma 8 floor being attained exactly at
the Mersenne numbers `2^a - 1` is prime structure worth pursuing".

Kind: `REFUTED` as decoration. The floor is attained at `2^a - 1` for EVERY `a`,
prime or composite -- `15 = 3*5`, `63 = 7*9`, `255`, `511 = 7*73` all have
`run = a`. What is structural is `u = x + 1 = 2^a`, the least value with
`v_2(u) >= a`; "Mersenne" is `u - 1`, an artifact of that coordinate. Under the
exponential bridge of `J-lemma-eight-is-the-exponent-valuation` the extremal
transports to the exponent `e = 2^r` -- one one-bit, not a repunit -- so the
all-ones pattern does not survive the transport at all. The same verdict covers
the Fermat reading of the negative cycle minima: `x + 1 = -2^a` is forced, so the
form `2^a + 1` is structural, while `a in {2,4}` both being powers of two (giving
`-5 = -F_1` and `-17 = -F_2`) is a coincidence on two data points with no
mechanism -- wallpaper by this laboratory's own standard.

What DID survive is not about primes: for even `a`,
`floor((2^a - 1)^(3/2)) = 2^(3a/2) - 3*2^(a/2 - 1)` with bits
`1^(a-1) 0 1 0^(a/2-1)`, and for odd `a` the Beatty form
`floor(sqrt 2 * (2^((3a-1)/2) - 3*2^((a-3)/2)))`. Those are recorded as
`J-repunit-floor-power-is-closed-form`, and their interest is that `2^a - 1` is
never a perfect power (Catalan, `mihailescu-2004-catalan`), so they are exact
values OFF the perfect-power locus.

Two further coincidences from the MathWorld entry, read 20 September, are killed
with them. The Mersenne numbers are a Fermat polynomial at `x = 1` and satisfy
`F_n = 3F_(n-1) - 2F_(n-2)`, whose coefficients are the `3` and `2` of the odd
step: NUMEROLOGY, because the characteristic polynomial is `(t-1)(t-2)`, so the
`3` is the trace `1 + 2` and the `2` is the determinant. And the run ends at
`3^n - 1`, of binary length `floor(n log2 3) + 1 = A020914(n)`, the laboratory's
distinguished word length: RESTATEMENT, since `A020914(n)` is by definition the
binary length of `3^n`, and the Mersenne word length `n + v_2(3^n - 1)` is
unrelated to it (4 against 5 at `n = 3`).

Do not reopen as: Mersenne or Fermat primality in either map, a search for prime
bases in the exact locus (the minimal realizers `2^(2^r)` and `3^(2^r)` have
prime bases because 2 and 3 are the smallest bases, which is not prime content),
a Fermat-number pattern in the negative cycles, the Fermat-polynomial
coefficients, or an A020914 coincidence in the Mersenne word.

One framing from the same page IS worth keeping, and it is not about Mersenne
primes: `M_n` is the Cunningham number `C^-(2,n)`, a one-base object, while the
cycle gap `3^o - 2^K` has two bases and two independently moving exponents. That
is the precise, citable reason classical primitive-divisor theory -- Zsigmondy,
Bang, Carmichael -- does not reach the gap, where the laboratory previously had
only the observation that it does not.

Dossier: [mersenne_floor_power](../problems/juggler_mersenne_floor_power.md).
