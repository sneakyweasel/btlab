# Lemma 8 does transfer, and it lands on a density-zero locus

Killed claim, same day (19 September 2026): "the Juggler has no twin of Hercher's
Lemma 8, so the 2-adic place does nothing for it". It has one, it is exact, and
the laboratory proved it in August without noticing: conjugating the Collatz odd
step by `u = x + 1` gives `u -> 3u/2`, the Juggler's exact odd step on `n = a^e`
gives `e -> 3e/2` on the exponent, and both cost one unit of `v_2` per step
because 3 is a 2-adic unit. So `run(x) = v_2(x+1)` and `exactRun(n) = v_2(e(n))`
are one law -- the second being `HasPowTwoDepth` with the two depth-drop lemmas
and `power_bound_eq_implies_pow_two_depth` -- and both pointwise floors are
attained, `2^k - 1` against `3^(2^k)`.

Kind: `KNOWN` relocation with a `METHOD_OBSTRUCTION` attached. The obstruction is
the price, not the absence: Collatz pays `2^(-k)` in the density where the
Juggler pays `2^(-k)` in the *exponent* of the density,
`floor(N^(2^-k)) - 1` against `floor((N+1)/2^k)`, and an exact run is monochrome,
so the surviving fibre carries two words where Terras carries `2^k`. Worse for
any route through it, Hercher's hypothesis is `k` consecutive odd LETTERS, which
a cycle word supplies free, while the mirror's is `k` consecutive EXACT steps,
which no word implies.

Do not reopen as: a cycle exclusion, an `m`-cycle bound, a floor raise, a Lean
restatement of the depth lemmas in `v_2 e(n)` notation, or a route to the
odd-tower door. The entry above keeps its conclusion and gains a reason. On a
prime power the exponent IS a valuation -- `n = p^e` has `v_p(n) = e`, and the
Juggler sends `v_p` to `3 v_p / 2` on an odd prime and to `v_p / 2` at `p = 2`,
where Collatz sends the value `u = x + 1` to `3u/2`: the Juggler does to
valuations what Collatz does to values. Off the perfect powers there is no
exponent at all, and the conjugacy that produced one does not extend, since
`|2^y - 2^z|_2 = 2^(-min(y,z))` depends on the Archimedean size of the exponents
and not on `y - z` in the 2-adic metric. So the inexact odd-run bound is
Archimedean by structure, not by a gap in the machinery. The
hand-over is explicit: on the powers of two the first inexact parity is a binary
digit of `sqrt 2`. That is a placement and not a Mahler transfer; the
`{(3/2)^n}` cluster below is untouched.

Dossier: [exponent_valuation_mirror](../problems/juggler_exponent_valuation_mirror.md).

