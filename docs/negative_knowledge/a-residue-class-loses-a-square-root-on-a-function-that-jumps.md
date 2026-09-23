# A residue class loses a square root on a function that jumps

The laboratory fixes the rotation coordinate `frac(d beta)` by taking `d` in a
residue class modulo a convergent denominator `q`, then reads off `d`-dependence
within the class. That is sound when the target is Lipschitz in the coordinate:
the class pins it to `delta = |frac(q beta)|` and everything else moves by
`O(delta)`.

It is not sound for a jump function on a dense orbit. `psi`'s amplitudes satisfy
`sum_(n > 1/delta) a_n` about `17 sqrt(delta)`, so `psi` varies across the class
by the **square root** of what the method assumes. At `q = 485`, where the
coordinate looks fixed to a part in a thousand, `psi` still varies by `4.8%`.
Getting that below a tenth of a percent needs `delta < 4e-7`, and such a class
holds under one sample point in a run to `d = 1e6` -- so it is not a matter of
going deeper.

Kind: `REPARAMETERIZATION` of the method, not of any result.
`J-residue-classes-lose-a-square-root-on-jump-functions`. It is what produced
the withdrawn `b/a = 40.98` reading and the tension attached to it
(`J-paper-b-increment-tension-is-the-class-method`).

Before using a class to measure a `d`-dependence, check that the target is
continuous in the coordinate. If it is not, the honest bound on what the class
can resolve is `17 sqrt(|frac(q beta)|)`, not `|frac(q beta)|`.

