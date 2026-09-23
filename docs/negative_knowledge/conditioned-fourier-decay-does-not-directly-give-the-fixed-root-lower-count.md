# Conditioned Fourier decay does not directly give the fixed-root lower count

The [conditioned-Syracuse audit](../problems/collatz_conditioned_syracuse.md),
23 September 2026, identifies actual depth-d unit ancestors with total halving
exponent H through two cells modulo 3^(d+1). Si's 2026 preprint, Theorem 5.1,
states conditional primitive Fourier decay O_A(d^(-A)) at this modulus in a
central H window. Its separate larger-frequency conjecture is not needed
just to reach that modulus.

**CLOSE** direct transfer using absolute-value Fourier inversion: the
coefficient normalization multiplies its error by 3^d, so this stated bound
provides no relative control at a specified root. Letting A depend on d
without uniform constants is not a repair. A lower bound for the coarse
cell is also missing. This refutes neither the preprint nor actual root
divergence; cancellation in the signed frequency sum and direct arithmetic
counting remain open. Four exact composition controls verify the signed
two-cell identification against actual inverse paths and budget increments.

The later [complete-halving comparison](../problems/collatz_fibre_unit_comparison.md)
does control the final unit loss after averaging over every H: its retained
fraction is between 5/21 and 20/21 of the coarse coefficient, uniformly in
positive depth. This uses the actual geometric fibres. The fixed-root coarse
lower count remains open; the direct Fourier-transfer closure above is unchanged.

