# A realization law of FD type cannot give Juggler a Steiner theorem

Killed claim, raised and refuted the same day (19 September 2026): "a perfect
Juggler realization law -- an exact archimedean analogue of the 2-adic cycle
equation -- would deliver at most Collatz's cycle starting line, the bounded-`m`
exclusions and the Eliahou-type period lattice, by the same reasoning that FD
proved outright would deliver Terras 1976 and no further."

Kind: **REFUTED** as a category error. Collatz's bounded-`m` exclusions
(Steiner 1977 for `m = 1`, Simons-de Weger 2005, Hercher 2023 for `m <= 91`)
do not rest on how words are distributed over integers; they rest on a
*pointwise* 2-adic fact, Hercher's Lemma 8: `k` consecutive odd steps force
`x = -1 mod 2^k`, hence `x >= 2^k - 1`, which bounds cycle minima below in
terms of run lengths and lets Baker close each fixed `m`. A density statement
of FD type gives nothing pointwise. Termination is an average problem along
the orbit; no-cycle is an extreme-value problem, a lower bound on the minimum
realizer of a returning word.

Witness: the 1-cycle length `9809721694`, a Juggler-side convergent numerator
of `log 2 / log 3`, survives Paper A's finance at `N_0 = 3.5e8` with a bound of
`1.0e20` on `n log n` against a floor of `6.9e9`
(`J-paper-a-finance-transposed-reproduces-eliahou-and-hercher`). Collatz has
excluded every 1-cycle since 1977; Juggler has no floor-free exclusion of any
`m`-cycle for any `m`, and Theorem 3.31 (`e >= 8`) bounds even letters by a
census, not local minima by a Diophantine argument.

Do not reopen: FD, equidistribution along the orbit, or any averaging
statement as a route to bounded-`m` cycle exclusion. The Juggler twin of
Lemma 8 is the pointwise odd-run bound `run(n) <= C log n` -- the odd-tower
fragment -- and that is the door, if there is one. Dossier:
[collatz_finance_mirror](../problems/juggler_collatz_finance_mirror.md).
