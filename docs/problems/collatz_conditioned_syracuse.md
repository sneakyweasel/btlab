# Conditioned Syracuse sums and the fixed-root inverse count

23 September 2026. Reading and applicability audit. No new analytic bound,
named theorem, conjecture or Lean module is introduced.

## Problem

Does recent Fourier analysis conditioned on the total halving exponent supply
the lower bound missing from the signed finite-height coefficient criterion?

## Exact statement

Fix sign s in {1,-1}, a positive odd target a coprime to three, depth d>=1,
and total halving exponent H>=d. For a positive composition k_1+...+k_d=H,
put H_j=k_1+...+k_j, H_0=0, and

\[
 Q(k)=\sum_{j=1}^d3^{d-j}2^{H_{j-1}},\qquad F_d(k)=Q(k)/2^H.
\]

The signed affine equation is 2^H*a=3^d*n+s*Q(k). Viewed modulo 3^(d+1),
the rational offset F_d is defined because two is invertible. This composition
is the actual valuation word of a positive odd unit ancestor n precisely when

\[
 F_d(k)\in A_{s,a,d}:=
 \{sa+3^d,\ sa+2\cdot3^d\}\pmod {3^{d+1}}.                 \tag{1}
\]

Indeed, divisibility by 3^d gives all successive integral inverse steps.
Starting from positive odd a, each such step is positive and odd. The numerator
is odd, so its quotient n is odd. The remaining requirement 3 does not divide n
removes exactly one of the three lifts modulo 3^(d+1), leaving (1).

Let p_(d,H) be the uniform-composition probability of (1). Every composition
has geometric-model probability 2^(-H), so the existing finite coefficient is

\[
 B^s_{d,b}(a)=3^d\sum_{H=d}^{b}
    {H-1\choose d-1}2^{-H}p_{d,H}.                         \tag{2}
\]

This is the same actual inverse quantity as the
[finite-height theorem](collatz_fibre_height_budget.md), not a new random-orbit
assumption. The two signs change the selected cells through sa. Reflection of
these finite congruences does not transfer a theorem at a positive integer
from one sign to the other.

## Current literature

`si-2026-microcanonical-affine` is a May 2026
[preprint](https://zenodo.org/records/20027097). Its Theorem 5.1 states conditional
primitive Fourier decay O_A(d^(-A)) at modulus 3^(d+h), for 1<=h<=K*log d
and |H-2d|<=L*sqrt(d*log d). Therefore h=1 reaches the modulus in (1).
Sections 6 and 11 give its composition encoding and a separate conjectural
larger-frequency range. That latter conjecture is not the missing hypothesis
for applying Theorem 5.1 at h=1. The relevant pages were read and the formulas
checked visually; this does not certify the complete preprint's analysis.

`kramer-2026`, [Theorem 1](https://arxiv.org/html/2607.10041v1#S3.SS4), gives
necessary residue-rate conditions for an infinite code realized by one fixed
positive integer. Its search is diagnostic and supplies no inverse-count
lower bound. The registry's title is corrected and its arXiv URL normalized.
The affine and composition identities here are **KNOWN**.

## Branch budget

- **Target:** extract a fixed-root lower bound from conditioned Fourier decay.
- **Novelty hypothesis:** conditioning on H may retain useful arithmetic information.
- **Falsifier:** the available error exceeds the selected cells' mass scale.
- **Already killed by?:** generic mixing is closed; this checks a specific
  estimate for the actual affine process, with its own hypotheses retained.
- **Existing machinery:** exact signed inverse paths and finite height budgets.
- **Maximum Phase-0 scope:** read the relevant theorem, identify the selected
  cells, and check the identity on small actual integer paths.
- **Promotion criterion:** a positive lower bound for the existing fixed-root quantity.
- **Stop criterion:** close direct transfer if only an oversized absolute error results.

## Balanced-ternary formulation

Ordinary ternary cylinders record the integrality and source-unit guard in
(1). Changing the digit convention does not improve a Fourier error estimate.

## Why BT may be relevant

The exact residue information matters. A mean density or approximate
probability without its modulus and normalization is insufficient.

## Candidate operations / invariants

Use the affine offset and the source-unit guard together. For example, at
plus target 7, d=1, H=2, the only composition is (2). Its coarse congruence
modulo three holds, but its predecessor is 9, which is sterile. The retained
two-cell probability is zero despite coarse-cell probability one.

## Experiments

Four new parameterized controls in
[test_fibre_height_budget.py](../../tests/research/collatz/test_fibre_height_budget.py)
enumerate every composition for d=1..4 and d<=H<=10, at targets (plus,1),
(plus,7), (minus,1), (minus,47). They compute the global affine offset, compare
the two-cell test with separate actual inverse-step reconstruction, and check
the exact layer against B_(d,H)-B_(d,H-1). All eleven tests in that file pass.
This finite control validates the identification, not an asymptotic lower bound.

## Conjectures

No new conjecture. The fixed-root depth-block lower bound remains open.

## Counterexamples

The sterile predecessor above prevents omitting the final unit guard. The
[coherent model](collatz_fibre_mixing.md) separately prevents deducing
pointwise positivity from general mixing properties. Neither refutes the
desired estimate for the actual signed recurrence.

## Formalization

The existing Lean finite-height theorem remains unchanged. Equation (1) and
the Fourier calculation below are written finite-arithmetic identities with
independent exact controls; no new formal proof is claimed. No conditional
Lean assembly is added in place of the missing analytic input.

## Results

Here is the precise loss in direct Fourier inversion. Let M=3^(d+1), let
phi_(d,H)(xi)=E[exp(2*pi*i*xi*F_d/M) | total=H], and let c_(d,H) be the
probability of F_d congruent to sa modulo 3^d. Character orthogonality gives

\[
 p_{d,H}-\tfrac23c_{d,H}
 =-\frac1M\sum_{\substack{\xi\bmod M\\3\nmid\xi}}
      \phi_{d,H}(\xi)e^{-2\pi i\xi sa/M}.                 \tag{3}
\]

To see this, the two selected lifts contribute two for characters divisible
by three and minus one for primitive characters. Subtracting two thirds of
the three-lift coarse cell cancels exactly the former characters.

Even granting the preprint's estimate, absolute values in (3) give only
|p-(2/3)c| <= (2/3)*C_A*d^(-A). After the coefficient normalization in (2),
the allowance is proportional to 3^d*C_A*d^(-A). It supplies no useful
relative control at the required cell-probability scale 3^(-d), for any
fixed A. The dependence of C_A on A is uncontrolled here; choosing A to
grow with d is not justified. The coarse-cell probability c itself also
needs a fixed-root lower bound.

The stated theorem covers a central H window. Positivity permits restricting
to that window when proving a lower bound, but no equivalence with the full
coefficient is asserted: an unconditional small tail probability need not
remain small after multiplication by 3^d at a specified root.

The needed new information could be cancellation in the signed Fourier sum
in (3), or direct lower counting of the compositions in (1). Uniform
superpolynomial decay of each individual coefficient is not that information.

## Open questions

Can direct arithmetic at one fixed ordinary integer lower-bound the actual
two-cell counts across enough depths to make the existing coefficient series
diverge? No such count or Juggler pressure estimate is obtained here.

## Decision

**CLOSE** direct transfer from Theorem 5.1 through absolute-value Fourier
inversion to the fixed-root lower bound. This is an applicability limitation,
not a refutation of the preprint or of the actual arithmetic target. Best
next question: can the phases in (3), with the same integer a at every depth,
be exploited instead of discarded? No new enumeration campaign is opened.

The subsequent [complete-halving comparison](collatz_fibre_unit_comparison.md)
answers the final-unit part of that question arithmetically: after averaging
over every H, the two-cell probability lies between 5/21 and 20/21 of the
coarse-cell probability at every positive depth. This does not validate the
direct Fourier argument or apply with H fixed. It leaves the fixed-root
coarse-cell lower bound as the remaining obligation.

## Publication assessment

Status: `STRUCTURAL`. A reading audit and precise statement of the missing
arithmetic information; not a new paper or a termination theorem.
