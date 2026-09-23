# Pinned cubic-cell composition does not cover an actual cycle

[Absolute floor cells](../problems/juggler_cycle_absolute_cells.md) and
[rank curvature](../problems/juggler_cycle_rank_curvature.md),
11 September 2026, **CLOSE**. At the first walk-charge survivor
`(L,o,e)=(780239,492276,287963)` with `350000000<m<520000000`,
composing the already-proved height strip, Lean wrong-parity in that
strip, the sorted-grid oscillation, Lemma 6.3a, and Result 2 does
not exclude a cubic-band cycle and does not force the signed
comparison (UC6).

An actual cubic-band orbit satisfies `m^15<(m^3-M)^8`, so its
cube-gap is strictly larger than `m^{15/8}` (about `1.05e16` at
`m=350000001`). The Lean theorem `threshold_cycle_wrong_parity`
applies only when the gap is at most that size. The two regions
meet only on the excluded equality. The CB5 oscillation
`(1-1/L)Λ≈3.471e-6` leaves the largest-odd log-log coordinate
about `2.06e-6` above `log 2` and the first-even coordinate about
`3.47e-6` below it, so it does not locate the cut `m^2`. Result 2
only guarantees a gap of order `2m^{3/2}` (about `1.31e13`), which
sits below the strip. Lemma 6.3a's total envelope is
`<3.24e-13`. The counts are coprime, so interlacing is not an
escape. Do not reopen as a larger `m`-census, a sharper numerical
integration of the same envelopes, or another pairing of these
same statements. The uniform `B_b` intersection remains PARK.
Members: cycle_absolute_cells, cycle_rank_curvature.

The immediate follow-up, the orbit arc from the minimum to the
largest odd rank, is the same CLOSE. Paper A's pair formula
gives `k=301993` steps (`k/L≈0.387`), a modest gain on the
uniform oscillation and a slack ratio still about `8.5e5` short
of the height-strip cap on `u`. The length-`L-1` arc is the
only defect-tight pair and recovers the seam `c_o≥m^2`, not a
far-from-cube obstruction. Do not reopen as an arc census or
as a demand that most defects spend a fraction of `Λ`
(that kill would be a function of the surplus).

**UC6 is not an unproved estimate (CLOSE / REPARAMETERIZATION).**
The identity `s_R-s_Q=ε+χ` is exact, so Paper A's (UC6) is
identical to `0<c_2-2c_1+m<2`. On an actual cubic-band cycle
those three states are odd and the second difference is even,
so the open window is empty. Do not reopen (UC6) as a missing
inequality on unused capacities; eliminating the complements
recovers the existing transport, as already recorded in
J-cycle-rank-curvature-window.
