# Block-minimum geometric weights lose their fixed-root prefactor

The [block-weight audit](../problems/collatz_fibre_block_weights.md),
23 September 2026, treats H_N=sum_(k<N) q^(N-1-k)*K_k for the complete signed
unit coefficients, with q^N bounded by the complete unit minimum of K_N.
At a fixed nonperiodic positive odd root a, K_d(a)=O_a(d+1), proved through
finite height budgets, actual endpoint uniqueness, the harmonic bound and
uniform affine distortion. Meanwhile max H_N >= (3/2)^(N-1), and the block
minimum is at most 3/4, forcing 1-q >= 1/(4N). Consequently

    (H_N(a)/max H_N)/(1-q) <= 4*A_a*N^3*(2/3)^(N-1) -> 0.

**CLOSE** this block-minimum construction as a source of the positive
prefactor required by the near-critical family criterion. All these bounds
and the limit are kernel-checked for both signs. The result does not refute
other periodic subsolutions, certifying a different rate for the same table,
or actual coefficient divergence. The negative fixed point one is excluded
by the nonperiodicity hypothesis and retains its exponential peak. Fifteen
exact controls cover the written block identity and actual finite endpoints.
Ledger: C-fibre-fixed-root-linear-bound, C-fibre-block-prefactor-collapse.
