# Paper B: the jump amplitude is not fixed by a self-referential equation

The jump spectrum of the meander prefactor satisfies
`a_n = A psi(frac(n beta)) n^(-3/2)` asymptotically, with `A = 2 theta a_1`, and
`psi` is its own jump function plus the linear rise periodicity on the circle
forces. That looks like a bootstrap: `psi` determines the amplitudes and the
amplitudes determine `psi`, with `A` scale-invariant, so `A` should be pinned by
the equation rather than measured. It is not, and the scale invariance is exactly
why.

Written out the relation is

    psi = C*1 + A*L psi,   where L psi at x is sum_n psi(x_n) n^(-3/2) (x - 1{x_n <= x})

which is **affine** in `psi`, not an eigenvalue problem. For every `A` it has the
solution `C (I - A L)^(-1) [1]`, a one-parameter family in `C`. Solved on a
four-thousand-point grid with four hundred modelled jumps, a solution exists at
`A = 0.2, 0.5, 0.82, 1.5, 3, 8` alike, with `I - A L` well conditioned throughout
(condition number `3.3` to `384`). The equation selects nothing.
Kind: **REFUTED** route, `J-paper-b-jump-amplitude-is-not-a-fixed-point`.

The reason is that `psi` cannot be levered against itself: the equation relates
`psi` to `psi` and so fixes the shape and never the scale. Do not re-open this as
a bootstrap, an eigenvalue problem or a self-consistency condition.

**The pessimism this entry originally ended on was wrong, and is withdrawn the
same day.** It concluded that `a_1` is therefore a constant of the problem rather
than a consequence of its shape, on the grounds that `psihat_0 = kappa G(1)` is
the only Fourier coefficient in closed form without `a_1`. It is not the only
one. `psihat_k = Phihat_k G(e(-k beta))` holds for every `k`, the mean included,
and the ladder profile `Phi` behind the Spitzer identity is closed form, so
`a_1 = 1/(2 theta sqrt(2 pi beta (1-beta))) = 0.427956804`
(`J-paper-b-jump-amplitude-is-closed-form`). What is shut is this route, not the
question. The lesson is narrow and worth keeping: a self-referential relation
fixes shape, so an amplitude has to come from outside the function.
