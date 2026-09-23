# Actual signed coefficient peaks defeat uniform local comparison

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Can a depth-independent comparison within a fixed ternary unit neighborhood
turn averaged coefficient control into a lower bound at one ordinary integer?

## Exact statement

Let K_d^s=L_s^d 1_units and C_d^s=L_s^d 1 be the existing complete signed
inverse coefficients. For either sign, every r>=0, and every unit residue a
modulo 3^(r+1), the following holds: for every real H and natural cutoffs D,B,
there are d>=D and an odd integer m>=max(1,B) with

    m = a (mod 3^(r+1)),       K_d^s(m) > H.

The same assertion holds for C_d^s. These are the actual coefficient
operators, not a substitute coherent probability model. Both d and m may
depend on the requested bound. In particular this is not divergence at one
fixed ordinary integer, nor construction of an infinite integer orbit.

The explicit mechanism is one transported word. For any fixed k>=0,
at the residue b_(d,k)=-s/2^k modulo 3^(d+2),

\[
 K_{d+1}^s(b_{d,k})\ge\frac3{2^{k+1}}\left(\frac32\right)^d.       \tag{1}
\]

For every fixed unit neighborhood, one k puts all sufficiently fine
b_(d,k) in that neighborhood. It stays fixed as d increases.

## Current literature

The signed operator and its probabilistic interpretation are **KNOWN**;
see `tao-2019-almost-all-collatz`, Lemma 1.12 and Remark 1.13 in
[Section 1.4](https://arxiv.org/html/1909.03562#S1.SS4).
The one-halving spike was already checked in the
[fibre dossier](collatz_fibre_mass.md). Powers of two generating the units
modulo powers of three is standard elementary number theory, proved here
using the lifting-the-exponent identity already available in Mathlib.

Transporting the peak into every fixed unit neighborhood and drawing the
local-comparison obstruction is the **PROJECT-SPECIFIC** consequence.
No mathematical priority is claimed. Tao's averaged fine-scale estimate
does not assert the uniform local comparison refuted here.

## Branch budget

- **Target:** a depth-independent local comparison for actual coefficients.
- **Novelty hypothesis:** local averages could control a specified root.
- **Falsifier:** actual coefficient peaks grow without bound in every unit neighborhood.
- **Already killed by?:** the artificial mixing example does not satisfy the signed recurrence.
- **Existing machinery:** parent branches, the one-halving spike and ternary residues.
- **Maximum Phase-0 scope:** transport the spike and decide local boundedness for both signs.
- **Promotion criterion:** a valid comparison yielding a fixed-root lower bound.
- **Stop criterion:** close this mechanism if transported actual words defeat it.

## Balanced-ternary formulation

Unit neighborhoods are ordinary residue classes modulo powers of three.
Balanced digits encode the same classes and do not change their weights.

## Why BT may be relevant

The finite ternary levels make the quantifiers and the distinction between
a fixed neighborhood and a fixed integer explicit. No representation change
supplies a coefficient lower bound.

## Candidate operations / invariants

The full signed transfer, positivity of its summands, the fixed exponent
branch, and the conserved finite-level mean. No bounded policy or assumed
stationary density is introduced.

## Experiments

Four controls in
[test_fibre_local_bounds.py](../../tests/research/collatz/test_fibre_local_bounds.py)
cover both signs and every unit class modulo 3,9,27, using transported
words of total depth at most three. They construct positive odd integer
representatives, reconstruct the word, and independently check every
forward odd return and exact halving valuation. Complete rational transfer
tables dominate the word's coefficient. Separate controls check the finite
mean and local-average allowance. These controls do not establish the
unbounded-depth theorem; Lean checks that statement.

## Conjectures

No new conjecture. Fixed-integer coefficient-series divergence stays open.

## Counterexamples

The residues b_(d,k) give an explicit family contradicting local boundedness
of the coefficient family. The infinite construction is valid for every
unit neighborhood, rather than only the original neighborhood of -s.
The accompanying ordinary integers are allowed to grow with d.

## Formalization

[FibreLocalBounds.lean](../../formal/Problems/Collatz/FibreLocalBounds.lean)
contains three public theorems:

- `shifted_spike_lower`: the explicit transported coefficient lower bound (1).
- `unit_unbounded`: the full neighborhood, depth and positive odd height quantifiers for K.
- `coarse_unbounded`: the same conclusion for C using the checked relative comparison.

Private lemmas prove powers-of-two coverage and compatibility of transported
residues across levels. The old unfinished sibling-residue draft remains
outside the active graph; no theorem from it is imported or assumed.
The local-average calculation and Harnack obstruction below are written
corollaries, not additional formal declaration coverage.

The active Lean build passes all 9,023 jobs. The
[public audit](../../formal/AxiomCheckCollatzLocalBounds.lean) and
[saved dependencies](../../formal/AxiomCheckCollatzLocalBounds.expected)
cover all three public theorems, using only propext, Classical.choice and
Quot.sound. The style gate reports no new violations. All four new controls
and the selected existing fibre, ledger and documentation-link checks pass.
The claim's exact declaration references resolve in formalpedia; that source
lookup is separate from the executed Lean audit. Advisory coverage remains
pending; no external statement request is sent in this phase.

## Results

**Arithmetic coverage.** The elementary valuation identity

    v_3(4^t-1)=1+v_3(t),       t>0,

shows that 4^i, 0<=i<3^r, are distinct modulo 3^(r+1). They exhaust the
residues congruent to one modulo three. Multiplication by two supplies the
other unit class. Multiplication by any unit a is a permutation, so some
fixed k satisfies 2^k*a=-s modulo 3^(r+1).

**Transport.** The already proved repeated one-halving word gives a
coefficient at least (3/2)^d at -s modulo 3^(d+1). The branch with exponent
k+1 maps this source residue to -s/2^k modulo 3^(d+2):

    (3*(-s)+s)/2^(k+1) = -s/2^k.

Its coefficient is 3/2^(k+1). Positivity of every other branch proves (1).
For d>=r its target lies in the prescribed neighborhood. Since k is fixed,
the lower bound grows without bound. The checked progression construction
provides arbitrarily large positive odd representatives of each fine residue.
Finally K_d<=(20/21)*C_d transfers unboundedness to C.

**Written local-average bound.** At depth d>=r, the level 3^(d+1) table has
total K-weight 2*3^d and total C-weight 3^(d+1). The fixed cylinder contains
3^(d-r) fine residues. Nonnegativity therefore bounds its average K-value
by 2*3^r, and its average C-value by 3^(r+1), independently of d.

Suppose a finite constant A compared any two values at the same depth in
this cylinder, f_d(x)<=A*f_d(y). Averaging over y would bound every f_d(x)
by A times the preceding constant. The unboundedness theorem contradicts
this. Thus this depth-independent local Harnack comparison fails for both
actual coefficient families, even on arbitrarily small fixed unit cylinders.

This does not exclude a local lower bound by itself, a comparison with
constants depending on depth, or an arithmetic argument specific to a fixed
ordinary integer. Nor does it refute pointwise divergence at that integer.

The [fixed-root run estimate](collatz_fibre_run_tail.md) now proves a
complementary bound: after fixing a positive ordinary root, all words with
one free exponent followed by a one-halving run have total coefficient at
most 3a, except at the negative fixed point a=1. This includes the transported
peak family. Thus those changing-root peaks do not themselves supply the
required fixed-root divergence.

## Open questions

Can exact affine-word counts at one fixed nonperiodic ordinary integer give
a divergent coefficient sum, without assuming uniform comparisons over its
ternary neighborhood? A lower bound c(a)/(j+1) on every sufficiently late
dyadic depth block would suffice; that arithmetic estimate is unproved.
The Juggler growing-depth pressure estimate also remains open.

## Decision

**CLOSE** depth-independent local Harnack comparison as the mechanism for
extracting a fixed-root lower count from local averages. Actual affine words
already defeat its required bound. The next question remains the fixed-root
arithmetic count above. This phase ends at the obstruction.

## Publication assessment

Status: `STRUCTURAL`. A checked consequence of known elementary arithmetic
and the existing operator; no paper edit or termination claim.
