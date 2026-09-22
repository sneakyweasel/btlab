# Actual OOEE joint parity outside the slow resonance windows

22 September 2026. This phase joins the proved mixed modes to the actual
last square-root guard, proves the pure slow-mode bound, and applies
three-coordinate finite Fejer discrepancy to the actual Juggler map.
Advisory statement coverage is pending.

## Exact objects and the root error

Put X(x)=x^(3/2), M(x)=floor(X(x)), Y(x)=M(x)^(3/2),
V(x)=floor(Y(x)), and W(x)=sqrt(V(x)). The actual phase is

\[
 F_{i,j,k}(x)=\tfrac i2X(x)+\tfrac j2Y(x)+\tfrac k2W(x).
\]

[OOEERootPhase.lean](../../formal/Problems/Juggler/OOEERootPhase.lean)
proves, for every real x>=1,

\[
 0\le x^{9/8}-W(x)\le3x^{-3/8}.
\]

The existing one-sided remainder gives x^(9/4)-V(x)<=3x^(3/4).
Multiply the root difference by the larger root x^(9/8) and use the
difference of squares. Nonnegativity suffices; no positive lower bound
on either integer floor is needed. All square and integer boundaries
are included. On N<=L*P^(7/16) samples x=a+2n>=P>=1, the phase-sum
comparison costs at most 3*pi*abs(k)*L*P^(1/16).
Consequently the actual mixed modes retain O(P^(13/32)), uniformly
over every fixed finite frequency family with (i,j) not both zero.

## Explicit slow-mode bound

Let alpha(P)=(9/8)*P^(1/8). On P<=x<=P+D*P^(7/16), with P>0 and D>=0,

\[
 |(9k/8)x^{1/8}-k\alpha(P)|
       \le(9/64)D|k|P^{-7/16}.
\]

Suppose P>=1, C>0, C>=(9/32)D*abs(k), and
abs(k*alpha(P)-z)>=C*P^(-7/16) for every integer z.
The derivative stays between the adjacent integers, at distance at
least (C/2)*P^(-7/16). Both signs of k are covered. The proved finite
first-derivative bound and the actual root comparison give

\[
 \left|\sum_{n<N}e\bigl(\tfrac k2W(a+2n)\bigr)\right|
 \le\frac2C P^{7/16}+3\pi|k|D P^{1/16}+1.                 \tag{1}
\]

Only the actual sample points must lie in the source window. Removing
and restoring the last sample accounts for the final one.
[OOEESlowModes.lean](../../formal/Problems/Juggler/OOEESlowModes.lean)
also substitutes P=m^(16/9): the slope becomes (9/8)*m^(2/9), the
resonance width becomes C*m^(-7/9), and the root-error sum becomes
3*pi*abs(k)*D*m^(1/9). This is a conditional estimate outside explicit
windows, not an assertion that every target is nonresonant.

## Three-coordinate discrepancy with boundaries

[FejerBox3.lean](../../formal/BTCalculus/FejerBox3.lean) proves the following
generic finite estimate. For N>0 samples on the three-dimensional torus,
H>=3, and any product of three half-open circular arcs of lengths at
most one, suppose every nonzero Fourier mode with coordinates bounded
by H has normalized magnitude at most E>=0. Set A_H=1+2*harmonic(H).
Then

\[
 |\text{count}/N-\text{volume}|
 \le\frac{15}{\sqrt{H+1}}+(A_H^3+6A_H)E.                 \tag{2}
\]

This includes wrapped, empty and full arcs and actual boundary hits.
The finite expansion controls the product of the three concrete Fejer
smoothings with coefficient mass at most A_H^3. Telescoping the product
of indicators costs at most the sum of the three coordinate errors.
The already proved L1 arc estimates supply the 6*A_H*E term; their
smoothing losses are at most 15/sqrt(H+1). No new equidistribution,
smoothing or cancellation premise is introduced beyond the stated
finite mode bound. The constants are deliberately unoptimized.

## The actual OOEE count

[OOEEParity.lean](../../formal/Problems/Juggler/OOEEParity.lean) identifies
the half-open box [1/2,1) times [0,1/2) times [0,1/2) at the coordinates
(X(n)/2,Y(n)/2,W(n)/2) with `FateOOEEAssembly.ooeeGuard n` for odd natural n.
It proves the floor identities with the natural square roots and checks
each actual branch. Thus (2) counts the genuine OOEE guards, with main
share 1/8 among the odd candidates.

The covering theorem `nonresonant_guard_discrepancy` states: for fixed
integer H>=3 and real D>=0 there are B>0 and P0 such that, for all P>=P0,
odd natural a, N>0 and C>0, if every a+2n with n<N lies both in [P,2P]
and in [P,P+D*P^(7/16)], N<=D*P^(7/16), C>=(9/32)D*H, and every integer
0<abs(k)<=H satisfies the displayed nonresonance condition, then

\[
 \left|\frac{\#\{n<N:\mathrm{OOEE}(a+2n)\}}N-\frac18\right|
 \le\frac{15}{\sqrt{H+1}}+(A_H^3+6A_H)
 \frac{BP^{13/32}+(2/C)P^{7/16}+3\pi HDP^{1/16}+1}{N}.     \tag{3}
\]

Every Fourier bound in (3) is proved, not assumed. B and P0 are
independent of P,a,N,C. When N>=gamma*P^(7/16) for a fixed gamma>0,
the mixed and root errors divided by N tend to zero. Choose H first,
C second, then P large: (3) permits any fixed positive parity deficit.
The last observation explains the application; fibre endpoint geometry
and the resulting poor-target inclusion are the next formal obligations.

## Validation

The full Lean build passes (9082 jobs). The
[dependency audit](../../formal/AxiomCheckOOEEJointParity.lean) covers all
28 theorems in the four modules; every declaration uses only propext,
Classical.choice and Quot.sound. The main repository run passes 225 tests
with 15 skips. Two publication checks fail amid concurrent manuscript
edits; both pass on the committed-source scope plus this change. The
scoped Paper E and theorem-index rerun passes 15 tests after correcting
pytest's temporary-directory access. Following the host's publication
commit, the final live rerun passes 34 tests; the same two publication
checks still fail. Current Paper E, ledger and theorem-index checks pass.
The ledger retains kernel trust
and pending advisory coverage; no new external service was contacted.

## Decision and remaining boundary

**PROMOTE** the actual joint parity estimate. The [poor-fibre proof](juggler_ooee_poor_fibre_tail_note.md)
still needs the exact target fibres and candidate counts, the fixed-deficit
resonance inclusion, the reciprocal tail, weighted conversion and physical
source cutoffs assembled in Lean. `OOEEProductionBound` remains explicit
in the contagion theorem. The unconditional Lean exponent remains 100/203;
5/8 still depends on that production input. The actual failure-rate bound
and universal termination remain open.
