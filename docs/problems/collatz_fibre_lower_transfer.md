# A fixed ternary class already transports lower bounds to every unit root

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Would proving a coefficient lower bound throughout one favorable fixed
ternary neighborhood offer a weaker intermediate target than a global bound?
The preceding recommendation identified fixed-root divergence but proved no
new lower count. This phase tests that particular proposed intermediate step.

## Exact statement

Let C_d^s=L_s^d 1 be the complete all-source inverse coefficient for sign
s in {1,-1}. For every r>=0, class b modulo 3^r, and positive odd target a
with 3 not dividing a, there is one positive odd predecessor m such that

    m = b (mod 3^r),    S_s(m)=a,
    3m+s=2^e a,        1<=e<=2*3^r.

The same m and e work at every later depth. Put q_r=3/2^(2*3^r)>0. Then

\[
 q_r C_d^s(m)\le\frac3{2^e}C_d^s(m)\le C_{d+1}^s(a)
 \qquad(d\ge0).                                      \tag{1}
\]

For any finite set I of depths, a bound

\[
 L\le\sum_{d\in I}C_d^s(m)
\]

valid at **every** positive odd m in the fixed class implies

\[
 q_r L\le\sum_{d\in I}C_{d+1}^s(a)
\]

at **every** positive odd unit a. This is a lower-bound transport, not a
two-sided comparison of arbitrary points in a neighborhood.

There is also an exact qualitative equivalence. For r>=1 and a unit class b,
divergence of sum_d C_d^s(m) at every nonperiodic positive odd m in that class
is equivalent to divergence at all nonperiodic positive odd unit roots.
No uniform constants are required for this equivalence. Neither side is
proved here; proving divergence at just one m does not satisfy the premise.

## Current literature

The signed affine inverse recurrence is **KNOWN**;
`tao-2019-almost-all-collatz`, Lemma 1.12. The lower-cell problem is discussed
in Tao's [2020 inverse-density note](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/).
That note's subexponential normalized-cell conjecture is not a proved input,
and would not alone imply nonsummability of the depth series.

Powers of two generate the units modulo powers of three, and positivity
transports lower bounds along a branch. Both are **KNOWN** methods. The
explicit signed integer realization, cost and formal implication are the
laboratory's application; no mathematical priority is claimed. The old
unfinished sibling-residue draft remains outside the active proof graph.

## Branch budget

- **Target:** determine whether a fixed-class lower bound is weaker than a global unit-root bound.
- **Novelty hypothesis:** a favorable class could offer an easier intermediate arithmetic obligation.
- **Falsifier:** one actual inverse step transports its lower bound globally at a fixed positive cost.
- **Already killed by?:** the local Harnack obstruction concerns two-sided comparison, not this question.
- **Existing machinery:** ternary unit coverage, actual predecessors and the complete coefficient operator.
- **Maximum Phase-0 scope:** bounded residue access, coefficient/block transport and the divergence consequence.
- **Promotion criterion:** a genuinely weaker local arithmetic obligation.
- **Stop criterion:** close the proposed shortcut if its bounds already imply global ones.

## Balanced-ternary formulation

A neighborhood is one ordinary residue class modulo 3^r. Balanced digits
rename its members without altering inverse divisibility or the cost q_r.

## Why BT may be relevant

The residue formulation makes the uniformity quantifier explicit. It also
distinguishes a single fixed integer from every integer in a fixed cylinder.

## Candidate operations / invariants

For a unit target a, solve 2^e*a=3b+s modulo 3^(r+1). The bounded
powers-of-two orbit provides e, and the existing actual-predecessor theorem
provides a positive odd integer m. Use one fixed branch for every depth;
do not choose a new target when the depth changes.

## Experiments

Six exact controls in
[test_fibre_lower_transfer.py](../../tests/research/collatz/test_fibre_lower_transfer.py)
cover both signs. For r=0..3 and every unit target class modulo 3^(r+1),
an ordinary positive odd representative has exactly one admissible exponent
per child residue within 1..2*3^r. The tests reconstruct actual children,
check their forward returns and exact valuations, and compare their weights
with the complete rational coefficient tables through depth four.

Separate controls compare uniform local minima of two-depth blocks with
the shifted global minima for every unit class modulo 3,9,27. False controls
retain target 3, which has no predecessors, and show that the transport
cost cannot in general be replaced by one. These bounded checks support
the implementation; the all-level statements are proved in Lean.

## Conjectures

No new conjecture. The actual fixed-root lower count remains open.

## Counterexamples

A target divisible by three has no signed odd predecessor. Also, local
lower bounds need a positive loss when transported: for plus, the coarse
depth-one value is two throughout the class 2 modulo 3, while some global
depth-two values are below two. The minus case has the reflected example.
The theorem asserts no loss-free comparison or actual asymptotic lower bound.

## Formalization

[FibreLocalBounds.lean](../../formal/Problems/Collatz/FibreLocalBounds.lean)
now exposes `exists_bounded_power_mul`, retaining the exponent bound from
the existing lifting-the-exponent proof. The transported-peak statements
are unchanged and reuse that strengthened arithmetic helper.

[FibreLowerTransfer.lean](../../formal/Problems/Collatz/FibreLowerTransfer.lean)
defines `stepCost` and proves its positivity, bounded actual predecessor
access, the individual branch inequality, simultaneous transport at all
depths, finite-block transport, conditional divergence propagation, and
`nonsummable_on_residue_iff`. Nonperiodicity is inherited by a predecessor
of a nonperiodic root; the summability argument retains that hypothesis.

The executable audits are
[local bounds](../../formal/AxiomCheckCollatzLocalBounds.lean) and
[lower transfer](../../formal/AxiomCheckCollatzLowerTransfer.lean), with
their saved [local dependencies](../../formal/AxiomCheckCollatzLocalBounds.expected)
and [transport dependencies](../../formal/AxiomCheckCollatzLowerTransfer.expected).
The active build passes all 9,025 jobs. The two audits cover the eight new
public theorems and the three existing transported-peak theorems; all report
only propext, Classical.choice and Quot.sound. Style reports zero new
violations. All six new controls and the selected existing fibre, ledger and
documentation-link checks pass in the shared worktree. All eight exact
ledger references resolve in formalpedia; that source lookup is separate
from the executed axiom audits. Advisory coverage remains pending; no
external statement request is sent.

## Results

The existing arithmetic proof enumerates all units modulo 3^(r+1) as
2^k, 0<=k<2*3^r. Apply it to the unit 2a and the residue 3b+s. It supplies
k in that range with 2^(k+1)*a=3b+s modulo 3^(r+1). Dividing the inverse
numerator by three gives the required ordinary integer m. Positivity and
oddness are checked, and oddness of a makes e=k+1 the exact halving valuation.

The complete recurrence contains the nonnegative summand
(3/2^e)*C_d^s(m). Since e<=2*3^r, its multiplier is at least q_r. This
proves (1) and the finite-block inequality without any distribution model.
If the root's coefficient series were summable, (1) would make the series
at this particular predecessor summable. A local divergence assumption
therefore propagates to the root. Conversely, a global divergence assertion
restricts to any unit class. This proves the stated equivalence.

**Written minimum consequence.** For a fixed unit class let ell_d be the
minimum of C_d over that class, and let g_d be its minimum over all positive
odd units. These minima exist because each table is finite and periodic.
Then g_d<=ell_d and q_r*ell_d<=g_(d+1). Their nonnegative series are summable
simultaneously. The finite-block version has the same one-depth shift.
Thus a nonsummable uniform minorant on one fixed neighborhood would already
give a global uniform minorant. This corollary is derived from the checked
transport; minima are not separately defined in the Lean module.

The result does not rule out either lower bound. It identifies the strength
of the local premise. If r grows with depth, q_r also changes and its loss
must be accounted for; the fixed-class conclusion cannot be reused without
that calculation. No mass bound at one chosen root, transfer between signs,
Juggler pressure estimate, termination proof or infinite escape follows.

## Open questions

Which constraint of actual integer inverse paths supplies a nonsummable
lower bound at one fixed nonperiodic root without assuming a uniform bound
on an entire ternary class?

## Decision

**CLOSE** the proposed fixed-neighborhood shortcut as a genuinely weaker
uniform lower-count target. The transport theorem is valid, but its local
premise already implies the global estimate. The qualitative class-wide
divergence statement is likewise equivalent to the global one. Retain the
checked reduction and stop this phase. The next question is the individual
fixed-integer arithmetic bound stated above.

## Publication assessment

Status: `STRUCTURAL`. A formal application of known residue and positivity
arguments, with no new lower count or manuscript revision.
