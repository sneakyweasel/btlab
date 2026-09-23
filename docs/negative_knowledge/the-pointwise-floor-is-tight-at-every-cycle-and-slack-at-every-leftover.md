# The pointwise floor is tight at every cycle, and slack at every leftover

Killed claim, same day (19 September 2026): "a pointwise Juggler odd-run bound
would move the cycle frontier". Priced on the mirror side, where the bound
exists in full, it does not.

Kind: `METHOD_OBSTRUCTION`, with two `EXACT` restatements attached. The floor is
sign-symmetric -- the Lemma 8 congruence holds over `Z`, giving `x >= 2^a - 1`
for `x >= 1` and `|x| >= 2^a + 1` for `x <= -2` -- and the LARGER floor sits on
the side that has cycles. Worse for any exclusion built on it, the floor is
attained with equality by every nontrivial cycle of the `Z` map: `1`, `-5`, `-17`
at `a = 1, 2, 4`, equivalently `x + 1 = -2^a`, equivalently the odd part of the
word's even-charge is `|2^K - 3^o|`. Paired with the kernel-checked
`neg_cycle_finance` the floor is a per-word window, empty exactly when
`2^(a+1) theta_J > e`, so a cycle word obeys `a <= log2(e / theta_J) - 1`. At
`K = 22` -- the first length Paper A Theorem 3.31's `e >= 8` admits, since that
bound forces `o >= 14` -- it removes 4787 of 17637 admissible words, 27.1 per
cent, exactly those with leading run at least 6. Along the leftovers the same cap
reads 8.02 at `L = 19`, 12.86 at 84, 16.59 at 569 and 22.09 at 1054, because
`theta_J` is a record near-convergent defect there and the ceiling carries
`1 / theta_J` while the floor does not.

Do not reopen as: a cycle exclusion at any `m` or any length, a Baker-free
Steiner theorem on either side, a route to the near-convergent leftovers, or a
claim that the negative Collatz cycles are newly constrained -- the laboratory's
rational-cycle census already settled every length to 24 by exhibiting them. The
entry above keeps its conclusion and gains a number: the door delivers the cycle
starting line and stops before the first leftover.

Dossier: [negative_lemma_eight_window](../problems/juggler_negative_lemma_eight_window.md).
