# Paper B: the `1/rho` jump law is the empty-window theorem

The prefactor cluster recorded, twice, that the ratio of consecutive jump
amplitudes of `psi` across a Sturmian zero is exactly `1/rho = 1.0352968376`.
The ratio is real and now known to `2.1e-12`. The finding is not.

`rho` and `theta` are the same number, `0.9659065532355213`, carried under two
names in the same cluster. A Sturmian zero is an even barrier letter; an even
letter kills no survivor and doubles the count exactly; dividing by the
normalisation `2 theta` leaves `1/theta`. The doubling is
`PaperBCertificateLengths` -- no minimal certificate exists at a length where no
power of three lies in the window -- seen from the amplitude side, and it is one
line of Lean (`PaperBJumpTransposition.total_stepEven_eq_two_mul`).

Kind: **REPARAMETERIZATION**. Do not re-derive it as an independent constant.
The useful residue is that the content of the spectrum lies entirely in the odd
letters, which is what produced
`J-paper-b-jump-spectrum-is-the-survivor-sequence`.

Second, and separate: **a global fit cannot reach the barrier-index constants
`C_j`.** The obstruction is structural, not statistical. The column a jump at
`frac(n beta)` contributes to any linear model is its own ramp minus its own
staircase, and that difference collapses toward zero as the jumps get fine, so
the design goes rank-deficient and the high-`n` amplitudes are unconstrained by
the data at any sample size. Free-amplitude fits are biased one-signed and the
bias grows with `j` in both the resolution and the depth. Do not attempt a
larger fit; the closed form is the route.
