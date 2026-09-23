# Lambda-recurrence is not an easier Collatz target, and the reason is density

The question was whether the first return to `lambda = 1` is a softer thing to
prove than convergence. It is not, and the obstruction is arithmetic rather
than dynamical.

**The event happens at the bottom.** Over odd starts to `1e6`, counting
Syracuse steps, the mean `log2` of the first `lambda = 1` value is flat at
about 4.39 across four decades --- the typical landing value is about 21
however large the start --- and the mean gap `collatz_time - lambda_time` is
flat at about 14.7 while the times themselves grow from 30.7 to 48.1. Five
values (11, 7, 23, 47, 31) take 71 per cent of all nontrivial landings below
`1e6`.

**Why, and it is not about Collatz.** The event needs `n + 1` to be 3-smooth,
and there are 142 such numbers below `1e6` and 306 below `1e9`, densities
`1.4e-4` and `3.1e-7`. An orbit of fifty Syracuse steps near `1e6` expects
0.007 hits and near `1e9` essentially none. The orbit must first descend into
the range where 3-smooth neighbours are common, so a proof of lambda-recurrence
would have to contain essentially a proof of descent.

Kind: `CLOSE` on the placement question. Lagarias's open problem (3) is
untouched and stays open; what is closed is the hope that it is the easier
target. Dossier:
[collatz_lambda_recurrence](../problems/collatz_lambda_recurrence.md).
