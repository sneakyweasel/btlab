# Weighted smooth carry contribution on short OOEE intervals

22 September 2026. Kernel-checked in
[OOEECarryCells.lean](../../formal/Problems/Juggler/OOEECarryCells.lean)
and [PartialSummation.lean](../../formal/BTCalculus/PartialSummation.lean).
This closes the actual cell partition and weighted smooth contribution
in equations (10)--(14) of the
[written OOEE proof](juggler_ooee_poor_fibre_tail_note.md).
Advisory statement coverage remains pending.

## Exact hypotheses

Use the phase F_(G,epsilon) from the
[curvature note](juggler_ooee_curvature_note.md), and put
delta(x)=(x+2h)^(3/2)-x^(3/2), G(x)=floor(delta(x)), z(x)=fract(delta(x)).
The smooth contribution is

\[
 S_h(x)=(1-z(x))e(F_{G(x),0}(x))
                    +z(x)e(F_{G(x),1}(x)).
\]

Let N be natural, P,a,h,u,v,w,L real, and assume

\[
 P\ge1,\quad [a,a+2N]\subseteq[P,2P],\quad
 1\le h\le P^{1/16},\quad P^{15/16}\ge1024,\quad
 u>0,\quad |v|+|w|\le uP^{3/4}/1024,\quad
 L\ge0,\quad N\le LP^{7/16}.
\]

No cell partition, cancellation, or bounded-variation premise is assumed
in the final theorem. The previous module proves eventual validity of
the size conditions for each fixed u>0,v,w, uniformly in h.

## Partition, endpoint, and weight bounds

The mean-value theorem gives

\[
 0\le\delta(b)-\delta(a)
       \le \tfrac32hP^{-1/2}(b-a)\qquad(P\le a\le b).
\]

Thus the number of possible integer carry levels on the support is at
most 3L+2. Each occupied floor fibre is a consecutive block of sample
indices. Both claims concern the actual floor, including endpoint cells.

Write B=(64L*sqrt(u)+16/sqrt(u))*P^(3/8). If the sampled points have
one carry level, removing the final term lets the previous curvature
bound apply on a closed interval. Restoring that term costs at most one.
Every initial sum in that cell is therefore at most B+1.

The generic partial-summation theorem proves that a monotone real weight
in [0,1], applied to a sequence whose every initial sum is at most B0,
gives a sum of norm at most 2B0. It proves the variation bound by
telescoping and retains the last weighted term.
On an actual carry cell, z is increasing and 1-z decreasing.
Applying this theorem twice bounds its smooth contribution by 4(B+1).

Exact finite partition and the triangle inequality now prove
`smooth_contribution_bound` and `smooth_contribution_power_bound`:

\[
 \left|\sum_{n=0}^{N-1}S_h(a+2n)\right|
 \le4(3L+2)(B+1)
 \le4(3L+2)(64L\sqrt u+16/\sqrt u+1)P^{3/8}.
 \tag{1}
\]

This includes the empty sum. The shift need not be fixed as P grows.

## The term that remains

Let X=x^(3/2), Y=(x+2h)^(3/2), and g=floor(Y)-floor(X).
The theorem `carry_decomposition` proves exactly

\[
 e(F_{g,0}(x))=S_h(x)+
  (\{X\}-\{Y\})
    \bigl(e(F_{G(x),1}(x))-e(F_{G(x),0}(x))\bigr).
 \tag{2}
\]

This is the retained carry phase after the written linearization step;
it is not the complete original nested-floor correlation. Equation (1)
bounds the first term of (2). Bounding the second still requires the
pointwise truncated sawtooth approximation, its total short-interval
remainder O(P^(5/16)*log(P)), and the nonzero Fourier modes.
The linearization error, finite differencing, joint discrepancy, and
actual fibre cutoffs must then be assembled.

The [dependency audit](../../formal/AxiomCheckOOEECarryCells.lean)
selects all 13 theorems of the two modules. Each uses only
`propext`, `Classical.choice`, and `Quot.sound`. The full project build
passes (9066 jobs).

## Consequence for the termination attack

This is a completed ingredient of the written poor-fibre proof.
It does not yet discharge `OOEEProductionBound` in
[FateOEWeighted.lean](../../formal/Problems/Juggler/FateOEWeighted.lean).
The unconditional Lean contagion exponent remains 100/203;
5/8 remains conditional on that production bound, and yields the
sufficient Tao threshold e>3/8. The actual failure-rate estimate
remains open in either case. No escape trajectory follows.

**Decision: PROMOTE** the weighted smooth estimate. The next bounded
question remains the carry Fourier remainder on the actual short odd
intervals. This phase ends before that estimate.
