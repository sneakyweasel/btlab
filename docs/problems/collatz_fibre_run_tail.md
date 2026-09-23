# One free exponent followed by a one-halving run has summable fixed-root weight

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Can the actual one-halving peaks from the preceding phase contribute a
divergent coefficient sum when the ordinary integer root stays fixed?

## Exact statement

Fix sign s in {1,-1} and a positive odd target a. Read an inverse word from
the target outward. Its first halving exponent is k+1, with k>=0; all its
next d halving exponents equal one. Count only words realized by positive
odd integers. Sources divisible by three are allowed at the outer boundary.
Let R_d^s(a) sum their coefficients

\[
 \frac{3^{d+1}}{2^{k+d+1}}
   =\left(\frac32\right)^{d+1}2^{-k}
\]

over every k>=0, with no exponent cutoff. For s=1 at every positive root,
and for s=-1 at every positive root except a=1,

\[
 0\le R_d^s(a)\le\frac{3a}{2^{d+1}},\qquad
 \sum_{d\ge0}R_d^s(a)\le3a.                         \tag{1}
\]

The same upper bound applies when sterile sources are excluded. The
exception is real: R_d^-(1)>=(3/2)^(d+1), from the word with every exponent
equal to one. The result does not bound general exponent words or establish
the open divergence of the complete fixed-root coefficient series.

## Current literature

The affine itinerary identity and geometric exponent weights are **KNOWN**;
see `tao-2019-almost-all-collatz`, Section 1.4 and Lemma 1.12 in
[Tao's paper](https://arxiv.org/html/1909.03562#S1.SS4).
The laboratory already has the complete signed operator and the
[transported one-halving peaks](collatz_fibre_local_bounds.md).

The explicit fixed-root summable bound for this complete word family is
the **PROJECT-SPECIFIC** consequence here. Its proof is elementary
divisibility and a geometric tail. No mathematical priority is claimed.

## Branch budget

- **Target:** bound this complete word family at a fixed ordinary root.
- **Novelty hypothesis:** integrality forces a summable loss with run length.
- **Falsifier:** a realized word escapes the divisor or the exponent-tail bound.
- **Already killed by?:** local unboundedness allows roots to change with depth.
- **Existing machinery:** exact signed words, geometric sums and the transported spike.
- **Maximum Phase-0 scope:** both signs, every first exponent, and the fixed-point exception.
- **Promotion criterion:** an unconditional summable bound for the specified family.
- **Stop criterion:** stop before claiming a bound for general exponent words.

## Balanced-ternary formulation

The congruence modulo 3^(d+1) expresses ordinary integrality of the whole
word. Balanced digits do not change the divisor or the coefficient.

## Why BT may be relevant

This separates a congruence realized at a fixed integer from a changing
finite residue representative. The size of a nonzero ordinary integer
multiple supplies the new estimate.

## Candidate operations / invariants

Translate an inverse state x to x+s. Along a one-halving inverse step,
3*(next+s)=2*(current+s). This telescopes through the entire run. The
single free exponent remains completely summed, rather than conditioned
on a total exponent or capped in a numerical experiment.

## Experiments

Five controls in
[test_fibre_run_tail.py](../../tests/research/collatz/test_fibre_run_tail.py)
reconstruct actual integer words independently of the global congruence.
For both signs, roots 1,3,5,7,11,47 and run lengths 0..4, every exponent
in a full modular period and four further positions agrees with that
congruence. Each accepted step is checked against the actual odd return
and its exact halving exponent.

The infinite exponent sum is folded into its verified period 2*3^d and
computed with rational arithmetic. The geometric bound is checked through
run length four, partial totals through length five, and the negative
fixed point is retained as a false control for the unrestricted claim.
The all-depth result comes from Lean, not these finite checks.

## Conjectures

No new conjecture. The complete fixed-root lower count remains open.

## Counterexamples

At s=-1,a=1,k=0 every inverse state is one, so the coefficient is
(3/2)^(d+1). Already at d=2 it exceeds the proposed unrestricted upper
bound 3/8. Excluding this root is essential. Other negative periodic
roots are not excluded: this theorem bounds only the specified word family,
not repeated words describing their different cycles.

## Formalization

[FibreRunTail.lean](../../formal/Problems/Collatz/FibreRunTail.lean) defines
`RealizedRun` by positive odd integer states and the exact numerator
equations, and `runCoefficient` by the complete weighted exponent sum.

- `realizedRun_divisibility`: every realized word forces (2) below.
- `realizedRun_returns`: its outer state actually reaches the root in d+1 odd returns.
- `runCoefficient_bounds`: the nonnegative geometric bound (1).
- `runCoefficient_summable` and `total_runCoefficient_le`: summability and the total allowance 3a.
- `negative_fixed_point_lower`: the explicit exponentially growing exception.

The interpretation as a subfamily of the complete coefficient, and the
subtraction consequence below, are written consequences of these exact
word definitions and the existing complete predecessor bijection. They
are not additional declaration coverage.

The active Lean build passes all 9,024 jobs. The
[public audit](../../formal/AxiomCheckCollatzRunTail.lean) and
[saved dependencies](../../formal/AxiomCheckCollatzRunTail.expected) cover
all six theorems and report only propext, Classical.choice and Quot.sound.
The style gate reports no new violations. All five new exact controls and
the selected existing fibre, ledger and documentation-link checks pass in
the shared worktree. The eight public declaration references resolve in
formalpedia; this source lookup is separate from the executed axiom audit.
Advisory coverage remains pending; no external statement request is sent.

## Results

Write x_0 for the first inverse child and x_d for the outermost source.
The exact numerator equations give

    3*x_0+s = 2^(k+1)*a,
    3*(x_(j+1)+s) = 2*(x_j+s).

Multiplication and telescoping yield

\[
 3^{d+1}(x_d+s)=2^{d+1}(2^k a+s).
\]

Since powers of two and three are coprime,

\[
 q:=3^{d+1}\mid 2^k a+s.                             \tag{2}
\]

Under the stated root restriction the integer on the right is positive.
Thus q<=2^k*a+1. Since q>=3, we have 2^k*a>=2 and

    2*q <= 3*(2^k*a).

Consequently twice the coefficient of any valid first exponent is at
most 3a/2^(d+1). If any realized exponent exists, choose the least k_0.
The complete contribution is at most its coefficient multiplied by
sum_(j>=0) 2^(-j)=2. This includes every omitted exponent, whether or not
it realizes a word. If none exists the sum is zero. This proves (1),
and summing over d gives 3a.

**Written subtraction consequence.** For each depth d+1 these words form a
subfamily of the complete coarse coefficient C_(d+1)^s(a). Their sources
and intermediate states are fixed uniquely by a and the exponents; the
positive odd guards make the exponents exact valuations. Hence removing
their contribution preserves divergence or convergence of the depth sum
at every root covered by (1). The corresponding unit-source subfamily is
smaller and can also be removed with a summable loss.

This reconciles the preceding unbounded-peak theorem with the fixed-root
target. The transported peaks lie within this word family. Their moving
roots can grow, but at a fixed ordinary root their total contribution is
finite. A proof of fixed-root divergence must obtain it from other words.
No general local regularity or lower bound for the remaining words follows.

## Open questions

Can the remaining actual affine words supply a nonsummable lower bound at
one fixed nonperiodic ordinary integer in each full fate class? Neither
that bound nor a Juggler source-weight or pressure transfer is proved here.

## Decision

**PROMOTE** the explicit summable contribution bound and its genuine
fixed-point exception. This removes the specified peak-producing family
from the fixed-root divergence question at a finite cost. The next question
is the lower count for the remaining words above. This bounded phase stops
at the estimate, without opening another branch.

## Publication assessment

Status: `STRUCTURAL`. A checked fixed-root consequence of elementary signed
affine arithmetic. No paper revision or termination claim.

Continuation: the [fixed-block theorem](collatz_fibre_word_tail.md) extends
the summable-family argument to any repeated positive inverse block at a
nonperiodic root, retaining the exact cycle exception. The stronger
one-halving constants above remain unchanged. Both modules now share the
masked geometric-tail lemma in `BTCalculus.GeometricMask`.
