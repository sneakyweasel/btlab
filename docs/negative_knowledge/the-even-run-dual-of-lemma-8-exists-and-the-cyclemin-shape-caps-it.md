# The even-run dual of Lemma 8 exists, and the CycleMin shape caps it

Killed claim (20 September 2026): "Lemma 8 uses only the 2-adic valuation, read
off the odd runs; the multiplicative order of 2, read off the even runs, is a
second and independent floor that could reach where Lemma 8 goes slack".

Kind: `METHOD_OBSTRUCTION`, with two `EXACT` statements attached
(`J-even-run-dual-of-lemma-eight-is-capped-by-the-shape`). The dual is real: with
`R` the gcd of the nonzero halving runs of a cycle and `m | 2^R - 1` coprime to
`2^o - 3^o`, every odd element satisfies `x = -1 (mod m)`, because in `u = x + 1`
the correction `2^(r_i+1) - 2` vanishes mod `m` and the passage collapses to
`2 u_(i+1) = 3 u_i`. It is also subordinate wherever this laboratory works. On a
word whose proper prefixes are all non-contracting -- Paper A's CycleMin shape,
hence a negative Collatz cycle word at its minimum, a Juggler cycle word, and a
positive cycle word at its minimum -- the leading run of `a` odd letters is
followed by an E-run of length `r_1 >= 1`, non-contraction at its end forces
`3^a >= 2^(a + r_1)`, and `R | r_1` gives

    R <= floor((log2 3 - 1) a) = floor(0.58496 a),

so the dual floor `2^R` is below Lemma 8's `2^a` by `2^(0.41504 a)` and never
binds. The only exception is the circuit `O^a E^r`, which Steiner 1977 excludes
and where the dual still does not win. Measured: 0 dual-only kills against the
`neg_cycle_finance` ceiling over 2264815 shape words to length 26, and the cap is
attained, so it is sharp rather than a census artifact. All three known cycles of
the `Z` map have an E-run of length 1, so `R = 1` and the dual is vacuous at every
one of them -- the exact opposite of Lemma 8, which all three attain with equality.

The reason is structural and is this laboratory's own constraint: prefix
non-contraction forces the word to bunch its odd letters, which lengthens odd runs
and shortens even runs, so the two floors are anti-correlated by the very condition
that defines the family.

What survives as content rather than obstruction is the reduction. Modulo `2^R - 1`
the even steps are invisible and the orbit is the free recursion `u -> 3u/2`, which
is the Juggler's exponent transport on the perfect-power locus -- where no-cycle is
the pure exponent count `3^o != 2^o`, needing neither Catalan nor Baker. The
Mersenne modulus is exactly the reduction under which Collatz becomes the Juggler's
exponent dynamics, and the price is exactly that `3^o != 2^o` degrades from a
contradiction into `m | u`: an impossibility becomes a floor.

Novelty, settled the same day, and the first version of this paragraph was wrong --
it said the primary sources were unreachable. They were reached, through a public
GitHub mirror of converted PDFs: Hercher 2023, Simons-de Weger 2005,
Halbeisen-Hungerbuehler 1997, Brox 2000 and Lagarias's two annotated bibliographies,
in full. The answer splits three ways. The BLOCK EXPANSION IS KNOWN and is Brox's:
`brox-2000-collatz-cycles-few-descents` (Acta Arith. 92 (2000) 181-188) has it at
(3.1)/(3.2), his `F~_i = M(x_i+1)` being the same `u = x+1` conjugation and his
`2 sum_l 3^(n-1-l) 2^(k_1+...+k_l) (2^(k_(l+1)-1) - 1)` term for term the laboratory's
`evenCharge` expansion -- checked here on all 16382 words of length <= 14 beginning
with `O`, 0 differences -- and this laboratory had been presenting it as its own.
Brox takes no gcd; he uses the brackets only as a size bound for a Baker-Feldman
argument. Hercher's Lemma 8 uses no multiplicative order and no Mersenne number, now
verified at source rather than inferred. The gcd step and the congruence were searched
hard and NOT FOUND -- but they are one line from Brox's printed identity, and that has
to be said rather than left for a reader who knows Brox to notice. The bookkeeping is
not interchangeable: the same statement with the FULL halving counts in place of the
extra halvings is FALSE (`OE`: `k = (2)`, gcd 2, `u = 2`, `3` does not divide `2`; 79
failures against 0 holds to length 12), so it is Brox's exponent that carries it and
not Simons-de Weger's matrix equation. What stands as this branch's own content is the
SUBORDINATION, and nothing resembling that was found.

Do not reopen as: a floor from the even-run structure on any prefix-noncontracting
family; a Baker-free Steiner theorem from the gcd of the halving runs; a claim that
the Mersenne reduction transports the Juggler's no-cycle count as anything stronger
than a congruence.

Dossier: [even_run_mersenne_floor](../problems/juggler_even_run_mersenne_floor.md).

