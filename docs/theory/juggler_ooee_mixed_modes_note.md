# Actual OOEE mixed-mode cancellation

22 September 2026. This phase connects the
[retained carry correlation](juggler_ooee_carry_fourier_note.md) to the
original nested-floor phase and applies finite differencing. It proves
the fixed mixed-mode estimate needed by the
[poor-fibre argument](juggler_ooee_poor_fibre_tail_note.md).
Advisory statement coverage remains pending.

## Statement

For real x, put M(x)=floor(x^(3/2)), Y(x)=M(x)^(3/2), and

\[
 f_{i,j,k}(x)=\frac i2 x^{3/2}+\frac j2Y(x)+\frac k2x^{9/8}.
\]

For each fixed integer triple (i,j,k) with (i,j) not both zero and
each fixed real L>=0, there are B>0 and P0 such that

\[
 \left|\sum_{n<N}e(f_{i,j,k}(a+2n))\right|\le B P^{13/32}
\]

whenever P>=P0, P<=a, a+2N<=2P, and N<=L*P^(7/16).
The starting point a may be real; in particular it may be an odd integer.
One B and P0 work for any fixed finite family of these triples.
No frequency cutoff growing with P is asserted. The pure slow modes
(0,0,k) remain outside the theorem.

The quantified statements are `fixed_mixed_mode` and
`finite_mixed_modes` in
[OOEEMixedModes.lean](../../formal/Problems/Juggler/OOEEMixedModes.lean).
`finite_mixed_modes_samples` also proves the version requiring only the
actual N sample points to lie in [P,2P]. It removes and restores the
final sample, adding one to the constant. Thus a half-open interval with
odd integer samples is covered by choosing a as its first odd sample
and N as their number; no unsampled endpoint condition remains.

## The original phase comparison

[OOEEPhaseComparison.lean](../../formal/Problems/Juggler/OOEEPhaseComparison.lean)
defines the actual first floor and the remainder

\[
 E(x)=Y(x)-\tfrac32 M(x)x^{3/4}+\tfrac12 x^{9/4}.
\]

It proves 0<=E(x)<=x^(-3/4) for every x>0. Set
a=sqrt(M(x)) and b=x^(3/4). The earlier exact factorization gives
E=(a-b)^2*(2a+b)/2, while

\[
 (b^2-a^2)^2-Eb=(a-b)^2(a^2+ab+b^2/2)\ge0.
\]

Since b^2-a^2 is the fractional part of x^(3/2), Eb<=1.
This proof needs no lower bound on M(x) beyond nonnegativity.

With u=j/2, v=i, w=k, the difference between the original shifted
phase and the retained phase is exactly

\[
 -\tfrac32u\{x^{3/2}\}\big((x+2h)^{3/4}-x^{3/4}\big)
       +u(E(x+2h)-E(x)).
\]

The mean-value bound and the phase Lipschitz inequality give the
finite comparison

\[
 \left|\sum_{n<N}e(f(a+2n+2h)-f(a+2n))
      -\sum_{n<N}e(F_h(a+2n))\right|
 \le10\pi |u| L P^{1/4}
\]

for P>=1, a>=P, 0<=h<=P^(1/16), and N<=L*P^(7/16).
The original floor discontinuities remain in this identity.
For u>0, adding the proved retained bound gives an actual correlation
bound C(u,L)*P^(3/8), with the explicit `correlationConstant` and the
same eventual size conditions as the retained theorem.

## Differencing and the remaining mixed modes

For u>0 choose H=floor(P^(1/16)). If N<H, the cardinality bound suffices.
Otherwise use the proved finite van der Corput inequality with exact
overlap lengths N-d. Since P^(1/16)<=2H,

\[
 |S|^2\le (4L^2+4LC(u,L))P^{13/16}.
\]

Thus `mixed_sum_positive` has explicit constant
sqrt(4L^2+4LC(u,L))+1. Conjugation covers negative u. The existence
of a common threshold follows from the previously proved eventual
size conditions, uniformly over all h below H.

If j=0 and i is nonzero, conjugation makes i>=1. The smooth phase has

\[
 f''(x)=\tfrac38 i x^{-1/2}+\tfrac9{128}k x^{-7/8}.
\]

For sufficiently large P its curvature is between i*P^(-1/2)/16 and
i*P^(-1/2)/2 on the support. The existing second-derivative test proves
(64L+16)*P^(5/16), which is stronger than the required P^(13/32).
[OOEESmoothModes.lean](../../formal/Problems/Juggler/OOEESmoothModes.lean)
proves this case. Finite induction takes maxima of constants and
thresholds to cover a fixed finite set of frequencies.

## Scope and decision

The original comparison and actual mixed-mode differencing are now
proved without an assumed correlation or cancellation bound.
The [dependency audit](../../formal/AxiomCheckOOEEMixedModes.lean)
covers every theorem in the three new modules.
The full build passes (9077 jobs); all 18 selected declarations use only
propext, Classical.choice and Quot.sound. The corrected targeted checks
pass (67 tests, four skips), including all failures from the initial
registration run. The commit's generated artifacts are checked separately
against its scoped source snapshot to exclude concurrent draft changes.

**Decision: PROMOTE.** This closes the fixed mixed-mode phase. The
[subsequent joint-parity proof](juggler_ooee_joint_parity_note.md) supplies
the actual square-root comparison, pure slow-mode resonance exclusions
and three-coordinate discrepancy with exact OOEE guard identification.
Target-fibre geometry, poor-target inclusion, reciprocal tail and physical
cutoffs must still be assembled before `OOEEProductionBound` is discharged.

The unconditional Lean contagion exponent remains 100/203. The stronger
5/8 result still has its explicit OOEE production hypothesis. The
failure-rate estimate and universal termination remain open.
