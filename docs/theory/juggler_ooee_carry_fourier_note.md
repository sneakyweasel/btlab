# The complete retained OOEE carry correlation

22 September 2026. This phase completes the fractional-part carry estimate
using finite Fejer smoothing and the actual perturbed cell phases.
It follows the [weighted smooth estimate](juggler_ooee_carry_cells_note.md)
and replaces the ordinary truncated-sawtooth step of the
[written argument](juggler_ooee_poor_fibre_tail_note.md) by an alternative
finite proof. It does not assume that truncated-series estimate.
Advisory statement coverage remains pending.

## Finite weighted smoothing

[FejerWeighted.lean](../../formal/BTCalculus/FejerWeighted.lean) uses the
committed [finite Fejer machinery](finite_fejer_box_note.md). Write
A_H=1+2*harmonic(H). For samples x_n, complex weights w_n of norm at most
one, and H>=3, suppose the nonzero frequencies |k|<=H satisfy

\[
 \left|\sum_{n<N}e(kx_n)\right|\le B,\qquad
 \left|\sum_{n<N}w_ne(kx_n)\right|\le E.
\]

Then `weighted_centered_fract_bound` proves

\[
 \left|\sum_{n<N}(\{x_n\}-\tfrac12)w_n\right|
 \le A_HE+\frac{5N}{\sqrt{H+1}}+2A_HB.
 \tag{1}
\]

The smoothing functions are actual convolutions. Their pointwise sandwich
includes boundary hits. Monotonicity bounds the sum of absolute smoothing
errors by the difference of the expanded and contracted convolutions plus
the kernel tail. Their Fourier expansions supply the two B terms.
The weighted expansion supplies E, with the zero mode separated exactly.
Finally, integration over the threshold of the half-open arc [t,1)
recovers the fractional part. Its mean is 1/2. This proves (1) for the
actual discontinuous function, including samples at integers.

## Actual perturbed phases

[OOEEFourierModes.lean](../../formal/Problems/Juggler/OOEEFourierModes.lean)
uses F_(G,epsilon) from the curvature note. Besides the previous conditions,
assume 32u<=P^(3/16), 0<=t<=2P and 1<=|r|<=P^(1/4).
On a genuine carry cell, the phase

\[
 F_{G,\epsilon}(x)+r(x+t)^{3/2}
\]

has curvature of the sign of r, with magnitude between
|r|*P^(-1/2)/8 and |r|*P^(-1/2).
The explicit dominance inequality follows uniformly from
h<=P^(1/16). The compiled second-derivative test therefore gives
(64L+16)*P^(5/16) on closed support with N<=L*P^(7/16).
For cells specified only at their sampled points, removing and restoring
the final term costs at most one. The pure power modes have the same
bound without that loss. Both frequency signs and translated powers are
included.

## Carry term and retained correlation

Put X=x^(3/2), Y=(x+2h)^(3/2), G=floor(Y-X), and

\[
 C_h(x)=(\{X\}-\{Y\})
       \bigl(e(F_{G,1}(x))-e(F_{G,0}(x))\bigr).
\]

Assume P>=1, [a,a+2N] contained in [P,2P], 1<=h<=P^(1/16),
P^(15/16)>=1024, u>0, |v|+|w|<=u*P^(3/4)/1024,
3<=P^(1/4), 32u<=P^(3/16), L>=0 and N<=L*P^(7/16).
Choose H=floor(P^(1/4)). The centered constants in (1) cancel in
the difference of fractional parts. Four applications of (1), followed
by the exact partition into at most 3L+2 actual carry levels, prove
`carry_contribution_log_bound`:

\[
 \left|\sum_{n<N}C_h(a+2n)\right|
 \le(3L+2)\bigl(12(3+2\log P)(64L+17)+20L\bigr)P^{5/16}.
 \tag{2}
\]

Here N/sqrt(H+1)<=L*P^(5/16), and A_H<=3+2log(P).
No count, smoothing-error, or cancellation premise remains in (2).

For g(x)=floor(Y)-floor(X), the retained phase is F_(g(x),0)(x).
The previous exact carry decomposition and smooth bound combine with (2).
Using log(P)<=16*P^(1/16), `retained_correlation_bound` proves

\[
 \left|\sum_{n<N}e(F_{g(a+2n),0}(a+2n))\right|
 \le (3L+2)\left[4\left(64L\sqrt u+\frac{16}{\sqrt u}+1\right)
                 +420(64L+17)+20L\right]P^{3/8}.
 \tag{3}
\]

All added size conditions hold eventually for fixed u>0,v,w,
uniformly in h and the cells. The empty sum is covered.
The application is in
[OOEECarryFourier.lean](../../formal/Problems/Juggler/OOEECarryFourier.lean).

## Scope and decision

The [dependency audit](../../formal/AxiomCheckOOEECarryFourier.lean)
selects all 29 theorems across the three new modules.
Each uses only propext, Classical.choice and Quot.sound. The full project
build passes (9073 jobs).
This completes the retained carry correlation. The
[subsequent mixed-mode proof](juggler_ooee_mixed_modes_note.md) now supplies
the original nested-floor linearization comparison and actual differencing.
Slow-mode handling, joint discrepancy, the poor-target inclusion and
production cutoffs remain open.

**Decision: PROMOTE.** This phase's next bounded question was to transfer (3) to
the original nested-floor correlation with its O(P^(1/4)) linearization
loss, and obtain the actual mixed-mode O(P^(13/32)) bound by differencing.
That application is now proved in the linked follow-up. This phase's
own result remains the retained correlation.

`OOEEProductionBound` remains explicit. The unconditional Lean contagion
exponent remains 100/203, while 5/8 requires that production bound.
The quantitative failure-rate estimate and universal termination remain open.
