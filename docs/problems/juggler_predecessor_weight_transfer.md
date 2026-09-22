# Two odd-predecessor weights are already covered by Paper B

22 September 2026. **CLOSE** the proposed new frequency-averaging campaign
at depth two: the required weighted estimate follows from Paper B
Theorem 4.11. The exact reindexing is kernel-checked. The analytic
corollary inherits that manuscript's AI-assisted written proof and
outstanding independent review; it is not an analytic Lean theorem.

## Problem

Determine whether the first inverse-cell estimate can be extended to
two actual odd predecessors while retaining a quantitative Fourier bound.
The first task is to check the full existing mixed-mode theorem, not just
the four-letter counting consequence previously cited.

## Exact statement

Write O(n)=floor(n^(3/2)) for the formal odd branch on all natural n.
Let b_d(m) count positive n for which O^d(n)=m and all d+1 integers
n,O(n),...,O^d(n) are odd. This count is zero or one. In particular,
on odd m, b_1(m) is the exact first inverse-cell weight and b_2(m)
requires both actual odd predecessors. Put e(x)=exp(2*pi*i*x) and

\[
 W_{d,h}(I)=\sum_{m\in I\cap\mathbb N}b_d(m)e(hm^{3/2}/2).
\]

**Corollary of Paper B Theorem 4.11.** For every epsilon>0, uniformly
for M>=2, intervals I contained in (M,2M], and nonzero integers h,

\[
 |W_{2,h}(I)|\ll_\varepsilon M^{127/288+\varepsilon}+|h|^{24}.
 \tag{1}
\]

Consequently, for 1<=|h|<=M^(1/60),

\[
 |W_{2,h}(I)|\ll_\varepsilon M^{4/9-1/288+\varepsilon}.
 \tag{2}
\]

The parallel one-cell consequence is

\[
 |W_{1,h}(I)|\ll_\varepsilon M^{127/192+\varepsilon}+|h|^{24}.
 \tag{3}
\]

For 1<=|h|<=M^(1/40), (3) saves 1/192 before epsilon from the
source scale M^(2/3). Thus the earlier specialized cubic argument's
new retained object is its mixed unweighted sum, not the strongest
known first-cell weighted bound.

## Current literature

The input is [Paper B, Theorem 4.11 and Appendix C](../theory/juggler_parity_discrepancy_note.md),
not a new external theorem. Its full statement controls all nonzero
integer modes of X=n^(3/2), Y=O(n)^(3/2), Z=O^2(n)^(3/2), and
U=sqrt(O^3(n)), up to CP^(1/24), on odd n in (P,2P].
This is strictly more information than its already-recorded four-letter
counts. The transfer below is an **INHERITED COROLLARY**, with no
independent novelty claim.

## Branch budget

```text
Mathematical target     Transfer Paper B to two exact odd-predecessor weights.
Novelty hypothesis      The estimate is an unrecorded corollary of its full mixed modes.
Falsifier               A lost parity guard, unsupported frequency, or source-window gap.
Already killed by?      The fourth odd phase is unsupported; this uses the third phase.
Existing machinery      Paper B 4.11, odd-branch injectivity, finite fibre reindexing.
Maximum Phase-0 scope   Exact transport in Lean and the analytic frequency-tail budget.
Promotion criterion     Every guard and quantitative loss accounted for.
Stop criterion          Stop at the first phase absent from Paper B, without iteration.
```

## Balanced-ternary formulation

None is needed. All cell bounds use exact natural squares and cubes.

## Why BT may be relevant

No representation-specific gain is asserted.

## Candidate operations / invariants

For a finite target interval I, exact injectivity gives

\[
 W_{2,h}(I)=
 \sum_{\substack{n\ge1,\ n,O(n),O^2(n)\text{ odd}\\O^2(n)\in I}}
       e(hZ(n)/2).
 \tag{4}
\]

There is no approximation of either floor. The formal map O is strictly
increasing on natural integers and O(n)>=n. Hence the unrestricted
condition O^2(n) in I selects an integer interval before the parity
conditions are imposed. For n>=1 and m=O^2(n), the exact scale bounds are

\[
 m^4\le n^9<64(m+1)^4.
 \tag{5}
\]

Indeed, if a=O(n), then a^2<=n^3<(a+1)^2<=4a^2 and
m^2<=a^3<(m+1)^2. Raise the first inequalities to the third power and
the second to the second power. Thus this source interval lies on scale
N comparable to M^(4/9). The parity masks in (4) are exactly
floor(X) odd and floor(Y) odd, besides the original odd n.

## Experiments

No orbit enumeration. The exact map, injectivity, all-depth finite
reindexing, and depth-two scale inequalities are Lean proofs.

## Conjectures

None added. The growing-depth pressure premise remains open.

## Counterexamples

The statement that *no quantitative two-predecessor weighted estimate
has been established* is too strong: (1) follows from the existing full
theorem. The preceding cubic and polynomial-dual records were describing
what their own methods supplied, but their suggested next question
overlooked this available transfer.

No counterexample to growing-depth equidistribution is inferred.

## Formalization

[OddPredecessorTransport.lean](../../formal/Problems/Juggler/OddPredecessorTransport.lean)
defines `oddMap`, `oddChain`, `ancestors`, `weight`, and `sources`.
`chain_actual` identifies the formal chain with the actual Juggler
iterate under every original odd guard. `weight_le_one` and
`weighted_reindex` give the exact finite transport at every depth.
`two_step_scale` proves (5); `source_interval` checks order-convexity
of the source window. `exponent_budget` and `one_cell_budget` verify
the rational exponent arithmetic.

The general finite identity does not supply an estimate at general
depth. Paper B 4.11, Fourier approximation, dyadic summation, and (1)--(3)
remain written analytic arguments. Their ledger label is human proof;
the exact finite row records kernel trust pending advisory coverage.

## Results

### 1. Twisting a guarded Paper B block

Set H=floor(P^(1/24)). On a dyadic source block (P,2P], assume
1<=|h|<=P^(1/24). Approximate each of the two half-circle indicators
1_{floor(X) odd}, 1_{floor(Y) odd} by a bounded degree-H trigonometric
polynomial. Use the same endpoint-aware approximants as Paper B;
their nonconstant coefficients are O(1/|j|), their constant coefficients
are O(1), and each nonnegative error majorant has coefficients O(1/H).
The polynomials are uniformly bounded, so the product error is bounded
by a constant times the sum of the two error majorants.

After multiplying by e(hZ/2), every retained mode has vector (i,j,h,0).
It is nonzero even when i=j=0. Theorem 4.11 therefore bounds the
polynomial contribution by P^(127/128+epsilon) after absorbing two
logarithms. For the approximation errors, discard the twist using its
unit modulus. Their zero modes cost O(P/H); each remaining mode is an
X- or Y-axis instance of 4.11. Their total cost is

\[
 O(P^{23/24}+P^{127/128+\varepsilon}).
\]

Thus the fully guarded dyadic twisted sum is
O_epsilon(P^(127/128+epsilon)), uniformly in h in that range.
Integer and half-integer endpoints are retained by the majorants.

### 2. Arbitrary source intervals and moving h

For a prefix n<=N, decompose into halving blocks (P,2P]. Apply Result 1
only while P>=max(2,|h|^24). The remaining prefix contains
O(1+|h|^24) integers and is bounded trivially. The estimates over the
retained blocks form a geometric sum. Hence any source interval in
[1,N] has guarded twisted sum

\[
 O_\varepsilon(N^{127/128+\varepsilon}+|h|^{24}).
 \tag{6}
\]

Subtracting two prefix sums supplies arbitrary endpoints; it does not
assume a short-interval version of Paper B. This frequency-tail term
must be kept: the fixed-scale frequency allowance cannot simply be
reused on arbitrarily small dyadic blocks.

Apply (6) to the interval from (4)--(5), with N=O(M^(4/9)), to obtain
(1). The equality (4/9)*(127/128)=127/288 and 24/60<127/288 give (2).
For (3), use the single X-parity mask, modes (i,h,0,0), and source
scale M^(2/3). The same prefix argument gives its displayed tail.

### 3. Exact location of the remaining phase

For three predecessors the desired next-odd-phase sum becomes
e(h*O^3(n)^(3/2)/2), with three earlier guards. Paper B instead contains
the coordinate U=sqrt(O^3(n)). Although O^3(n)^(3/2)=O^3(n)*U,
the multiplier O^3(n) depends on the source and is far outside the
fixed Fourier range. It cannot be inserted as a mode of 4.11.
This is the already-recorded
[fourth-odd-phase transfer obstruction](juggler_pressure_external_average.md).
The present corollary neither removes that obstruction nor estimates
growing-depth live pressure.

## Open questions

The first unsupported next-odd-phase predecessor estimate is at depth
three, with source-count scale M^(8/27). Ultimately one needs control
through depths growing with log log M and the actual stopped weights,
not just another fixed-depth parity count.

## Decision

**CLOSE** the proposed new depth-two frequency-averaging campaign as
redundant. Retain (1)--(3) as explicit inherited corollaries and the exact
Lean transport. The correct next question is a quantitative saving for
the fourth odd phase after three actual predecessor restrictions.
Stop this phase without opening that attack.

## Publication assessment

Status: **STRUCTURAL**. Consolidation of an existing written theorem,
not a new analytic theorem, paper, cycle exclusion, or termination proof.
