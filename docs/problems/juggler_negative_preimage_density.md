# Signed Collatz preimage density: residue symmetry needs a height argument

Status: **PARK** (22 September 2026). The former assertion that the
Krasikov–Lagarias exponent transfers by residue relabelling alone is
withdrawn as unproved. The eventual 3n-1 bound is not refuted.

Branch of the [Collatz bridge](juggler_collatz_bridge.md). The exact
predecessor comparison is now kernel-checked in
[PreimageScale.lean](../../formal/Problems/Collatz/PreimageScale.lean).

## Problem

Does the known positive 3x+1 preimage-count exponent also follow for
the 3n-1 shortcut map from the residue program already implemented here?
The previous answer conflated its residue symmetry with validity of
the associated inequalities for actual height-truncated inverse trees.

## Exact statement

For g(n)=n/2 at even n and (3n-1)/2 at odd n, the proposed conclusion
is that every positive target a not divisible by 3 has at least
x^0.84 positive ancestors below x for all sufficiently large x.
This remains an unproved claim in this branch.

What is proved is the sign-dependent scale comparison. For a=1 mod 3,
the odd predecessor c=(2a+1)/3 satisfies

\[
c>2a/3,\qquad
\frac{x}{c}=\frac{(x/a)(3/2)}{1+1/(2a)}.
\]

For the plus map, a=2 mod 3 gives c=(2a-1)/3<2a/3. Thus the nominal
child cutoff (x/a)(3/2)c is below x for plus, but above x for minus.
The residue classes transpose; this Archimedean inequality reverses.

## Current literature

[Krasikov–Lagarias, 2003](https://arxiv.org/abs/math/0205002) prove the
x^0.84 bound for positive targets under 3x+1. Section 2 defines the
height-truncated count and its residue-class infimum. Proposition 2.1
supplies the difference inequalities; Theorem 2.2 uses their validity,
positivity, and monotonicity. Theorem 6.1 supplies the numerical exponent.
The published theorem does not directly cover positive 3n-1 targets.

Their Sections 3–5 remove advanced terms and transfer feasible solutions
to a derived system. Invoking that machinery for minus still requires
a proof that the actual minus-tree counting functions satisfy suitable
inequalities. Equality of two formal programs is not that proof.

## Branch budget

- **Target:** audit the scale inequalities behind the recorded transposition.
- **Novelty hypothesis:** residue symmetry omitted a signed height correction.
- **Falsifier:** a uniform justification of the same shifts in the source proof.
- **Already killed by?:** not the backward-mass obstruction, which concerns
  harmonic mass rather than this counting theorem.
- **Existing machinery:** the signed predecessor maps and original paper.
- **Maximum Phase-0 scope:** exact scale comparison, Lean proof, and claim correction.
- **Promotion criterion:** justified transfer or a precise verified missing premise.
- **Stop criterion:** no density conclusion from matching residues or solvers.

## Balanced-ternary formulation

Residues modulo 3^k describe integrality of backward branches. They do
not determine the height cutoff. No BT representation change is used.

## Why BT may be relevant

Only through ternary residue bookkeeping. No termination input follows.

## Candidate operations / invariants

Negation sends fertile classes 2 mod 3 to 1 mod 3 and permutes the
mod-9 classes 2,5,8 to 7,4,1. It also transposes the quotient indices
and the three lifts. The existing finite exact checks of this algebra
remain valid. The formal programs attach the same homogeneous shifts
to both signs; the missing premise is their application to actual counts.

## Experiments

`python -m research.juggler_sequence.negative_preimage_density` now
labels the minus outputs as **residue-model exponents**, and records
no established minus-map density exponent. The archived high-k model
values remain historical numerical results, not newly certified bounds.

The independent forward enumeration agrees with the backward BFS:

| Child target | Cutoff | Ancestors with whole path below cutoff |
|---|---:|---:|
| 13 | 103 | 12 |
| 13 | 105 | 13 |

The old wrong-sign regression had never tested its alleged identity:
for a=1 mod 3 its guard `(2*a-1) % 3 == 0` is always false. It now
reports that nonintegrality explicitly. The BFS also returns zero when
its root itself is outside the positive cutoff interval.

## Conjectures

`J-kl-preimage-density-transposes-to-3n-1` is now **CONJECTURE**.
This status concerns the missing proof here; no claim is made that
the asymptotic conclusion is false or unavailable by another method.

## Counterexamples

Take a=19, c=13, x=103. The copied homogeneous shift gives child
cutoff 4017/38, between 105 and 106. It includes the genuine path
104 -> 52 -> 26 -> 13, which is excluded at cutoff 103.
Also x>=4a, so this is inside the original y>=2 regime.
The target is nonperiodic: 19 -> 28 -> 14 -> 7 -> 10 -> 5 -> 7.
Both facts are kernel-checked.

This refutes the proposed pointwise cutoff inclusion. It does not
refute every possible difference inequality for the residue infima:
additional terms or another normalization might compensate, but that
requires a separate proof. In particular, the counterexample does not
refute an eventual x^0.84 lower bound.

## Formalization

`PreimageScale.lean`, imported by `Problems.lean`, proves the exact
odd predecessor equations for both signs, their opposite comparisons
with 2a/3, the correction factor, and the reversed nominal-budget
inequalities for every positive real cutoff. `excluded_ancestor`
checks the finite path and its location; `nineteen_not_periodic`
checks all positive return times by a finite forward invariant set.
The density exponent and the all-level residue-program isomorphism
are not claimed to be formalized.

Validation: full `lake build` passes (9028 jobs). The
[nine-declaration audit](../../formal/AxiomCheckCollatzPreimageScale.expected)
uses only `propext`, `Classical.choice`, and `Quot.sound`. The focused
probe tests plus integration and ledger gates give 152 passes and
14 skips. The regenerated probe preserves 366 exact finite tree splits,
and reports 366 nonintegral wrong-sign expressions explicitly.

## Results

The valid residue algebra is preserved. Its former promotion to a
counting theorem is withdrawn. The exact missing shift in the minus
odd branch is

\[
y+\log_2 3-1-\log_2(1+1/(2a)),
\]

with the same positive correction for the doubled odd branch, whose
nominal shift is y+log_2 3-2. Dropping this correction is unfavorable
to a lower bound. It tends to zero as a grows, but that observation
alone does not control repeated production steps or the infimum over
all targets in a residue class.

The known-cycle census means the three known cycles and their fifteen
members; it supplies no exhaustiveness theorem. Existing finite tree
split checks remain computational and must retain their noncycle scope.

## Open questions

Can the signed height corrections be absorbed uniformly in the finite
derived production system, while justifying its minimization and
deletion steps for the actual counting functions? This is the precise
missing proof, not an invitation to run a larger linear program.

Even a repaired x^0.84 lower bound would not supply Juggler's required
divergent harmonic-mass estimate or its growing-depth pressure bound.

## Decision

**PARK** the density transfer pending the height argument. The residue
symmetry is retained; the claim of automatic analytic transfer is
closed. No new cycle exclusion, termination theorem, or computation
floor follows, and neither Paper C nor Paper D requires modification.

## Publication assessment

Working correction only. Do not present the 3n-1 exponent as a corollary
of residue negation until the height step is supplied and reviewed.
