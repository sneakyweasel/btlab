# Depth-five productions need windows of length P^(5/32)

Parked claim: the actual `OOOEE` and `OOEOE` productions follow from the
depth-four machinery, lifting unconditional contagion from `5/8` toward the
depth-five ideal `0.7512` and the required failure rate from `3/8` toward `1/4`.
Park: a target-`m` fibre of a word with multiplier `rho` spans about
`P^(1-rho)` sources near `P = m^(1/rho)`; both depth-five words have
`rho = 27/32`, so their fibres are windows of length `P^(5/32)`, against
`P^(7/16)` for `OOEE`. The depth-four count used mixed-mode bounds
`O(P^(13/32))` for the nested pair on `P^(7/16)` windows, which are weaker than
trivial on `P^(5/32)` windows; `OOOEE` adds the doubly nested `floor(Y)^(3/2)`
with no slow coordinate. An averaged poor tail needs differenced depth-five mixed
sums with shifts up to `P^(5/32)`; Paper B's frozen gaps stop at `P^(1/8)` and its
depth-five sums are unshifted.
Kind: `PARK_STOP`.
Branch: [juggler_depth_five_production](../problems/juggler_depth_five_production.md).

Do not reopen as another depth-four transfer, a longer census of fibre counts,
or a sharper resonance tail. Reopen only with a mean-square bound for depth-five
parity sums on `P^(5/32)` windows, or differenced depth-five mixed sums with
shifts up to `P^(5/32)` and a power saving. The binding step in Paper B's route
is the bounded remainder of (C.17), `k h_1 h_2 <= P^(1/8)`; an exponent audit of
Appendix C at bounded frequencies with an outer shift `P^delta` decides whether
`delta = 5/32` is reachable.

**Revised 24 September 2026.** A first-pass exponent bookkeeping of Paper B's
Appendices A--C (dossier Result 5) finds that Theorem B.1's endpoint term allows
outer shifts `P^delta` for `delta < 1/6`, or `delta < 3/16` at bounded frequencies,
and that the `P^(1/8)` limits above are local and repairable. The parking reason is
therefore provisional for `OOOEE`: an independent audit decides it. `OOEOE` has not
been bookkept.
