# The coefficient-series criterion for actual Collatz ancestors

22 September 2026. Formal verification of the implication in Section 4 of
the [fibre dossier](../problems/collatz_fibre_mass.md). The divergence
premise remains open. Independent review and advisory statement coverage
remain pending.

## Exact statement

Let S(n)=(3n+1)/2^v2(3n+1) on positive odd integers. Let h be the indicator
of residues coprime to three modulo 3, and K_d=L_+^d h, where L_+ is the
complete homogeneous odd-return operator already defined in
[FibreMass.lean](../../formal/Problems/Collatz/FibreMass.lean).

For every positive odd target a and every d>=0, the actual depth-d unit
predecessors satisfy

\[
 \sum_{\substack{n\ge1,\ n\text{ odd},\ 3\nmid n\\S^d(n)=a}}
       \frac1n\ \ge\ \frac{K_d(a)}a.
\]

If a is nonperiodic, meaning S^j(a)!=a for every j>=1, then

\[
 \sum_{d\ge0}K_d(a)=\infty
 \quad\Longrightarrow\quad
 \sum_{\substack{n\ge1,\ n\text{ odd},\ 3\nmid n\\
                         \exists d\ge0:\ S^d(n)=a}}\frac1n=\infty.
\]

The final Lean theorem states this as nonsummability of ordinary real
reciprocal weights over natural integers. It assumes neither a model of
the actual preimages nor a finite value for the ancestor mass.

## Counting each ancestor once

[PreimageGenerations.lean](../../formal/BTCalculus/PreimageGenerations.lean)
is independent of Collatz and Juggler. For any map f and any extended
nonnegative weight, it defines the mass of each actual preimage generation
and the mass of the ancestor set.

`BTCalculus.PreimageGenerations.generationEquiv` partitions a depth-(d+1)
generation by the last predecessor of its target. The endpoint determines
that predecessor uniquely. `BTCalculus.PreimageGenerations.mass_succ`
therefore gives the exact recurrence, allowing either side to be infinite.

If f^i(x)=f^j(x)=a with i<j, then f^(j-i)(a)=a. Nonperiodicity therefore
makes the reaching depth unique. `BTCalculus.PreimageGenerations.ancestorEquiv`
identifies the disjoint union of all generations with the actual ancestor
set. `BTCalculus.PreimageGenerations.sum_mass` proves equality of their
weights. A periodic target would allow repeated ancestors, so that
hypothesis is essential to this argument.

## The concrete coefficient-to-mass bridge

[FibreGeneration.lean](../../formal/Problems/Collatz/FibreGeneration.lean)
restricts the existing accelerated map to positive odd integers, proves
agreement with its ordinary integer iterates, and reuses the complete
predecessor bijection from `FibreActual`.

`Problems.Collatz.FibreGeneration.kernel_succ` derives the coefficient
recurrence from the actual signed congruence operator. Its index contains
every admissible positive halving exponent exactly once. The coefficient
series is separately proved summable at each fixed depth, using the
existing finite-level operator convergence.

For a plus predecessor n=(2^k*a-1)/3, the exact affine identity gives
(3/2^k)*n=a-1/2^k<=a. Consequently, for every nonnegative v,

\[
 \frac{(3/2^k)v}{a}\le\frac vn.
\]

`Problems.Collatz.FibreGeneration.kernel_mass_le` applies this comparison
inductively through the exact generation recurrence. Extended nonnegative
sums justify each interchange even if an actual generation already has
infinite mass. Thus no convergence claim is used circularly.

`Problems.Collatz.FibreGeneration.ancestorMass_eq_top` then sums the lower
bounds over the disjoint generations. Finally,
`Problems.Collatz.FibreGeneration.ancestor_reciprocals_not_summable`
transfers the conclusion to the literal natural-number indicator of actual
positive odd unit ancestors. The open premise is ordinary real
nonsummability of d -> K_d(a), not an unproved equality of two models.

## What this changes

The coefficient series is now a rigorously connected arithmetic target.
Its divergence at a suitable nonperiodic root would imply harmonic
divergence for every fate class containing that root. The finite periodic
weight obstruction does not refute this implication: it concerns uniform
reproduction at fixed depth, whereas this criterion sums all depths at
one specified integer target.

No coefficient-series divergence is proved here. The existing written
argument that every full positive Collatz fate class contains a nonperiodic
odd unit is kept separate from this formal statement. Sibling residue
coverage and higher-depth actual affine error bounds also remain outside
this module.

The proof uses the plus sign essentially. For the minus predecessor
n=(2^k*a+1)/3 the elementary affine inequality reverses, so this proof
does not supply the same lower bound. The separate
[negative continuation](collatz_negative_generation_mass_lean_note.md)
now controls the cumulative affine loss by (d+1)^(1/6) at nonperiodic
targets. The generic generation-counting theorem itself is sign-independent.

No Juggler growing-depth pressure bound, termination theorem, infinite
escape trajectory or cycle exclusion follows. The Juggler sufficient
pressure margin remains r-eta>3/8.

## Validation

The [complete audit](../../formal/AxiomCheckCollatzGenerationMass.lean)
and its [saved output](../../formal/AxiomCheckCollatzGenerationMass.expected)
cover the generic counting lemmas and every theorem in the Collatz module.
All 17 public theorems use only propext, Classical.choice and Quot.sound.
The active Juggler/Collatz build passes 9,011 jobs, including the negative
continuation. The combined targeted run has 47 passes and three failures
from two concurrently deleted older ledger targets, outside this proof.
The mathematical checks, declaration resolution, generated artifacts and
documentation links pass; the missing shared-worktree targets are
`docs/literature_comparison.md` and `formal/Representation/Words.lean`.
The isolated source tree for this phase passes all 49 selected mathematical,
ledger, declaration and generated-artifact tests, preserving those older
files and excluding unrelated deletions.

## Decision

**PROMOTE** the complete formalization of the existing coefficient-series
implication. The arithmetic divergence question remains open. This phase
stops without substituting a finite-depth computation for that premise.
