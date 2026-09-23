# Problems.Collatz

Collatz-only formalization. Generic balanced-ternary operator identities
live under `Operators/` and `Representation/`.

[BackwardMass.lean](BackwardMass.lean) proves that the same infinite
dyadic ray is backward-closed for both shortcut signs and has finite
reciprocal mass. It records the obstruction to transferring Juggler's
general backward-density theorem; the ray is not a fate class.

[PreimageScale.lean](PreimageScale.lean) proves that residue negation
reverses the odd-predecessor height comparison. It records the exact
minus-map scale correction and an actual ancestor excluded by the
parent cutoff, at a target proved nonperiodic. It does not establish
or refute the proposed asymptotic preimage-density exponent.

[PreimageCertificate12.lean](PreimageCertificate12.lean) completes the
separate strict-grid proof: every positive 3n-1 target coprime to three
has at least X^(21/25) positive ancestors up to every sufficiently large
natural X. The actual capped counts satisfy the same bound.

[PreimageBalance.lean](PreimageBalance.lean) proves the mean constraint
for both signs' finite residue tables, at every level. At the harmonic
rate it contradicts 2^79<3^50. Within the at-most-linear rate range,
its exact ceiling is mu<5069/5000, with mu^5000<2^99. This limits the
fixed grid certificate method, not actual ancestor counts or fate classes.

[FibreMass.lean](FibreMass.lean) proves the complete homogeneous odd-return
operator obstruction for both signs. It defines every positive halving
exponent through the exact signed congruence, proves summability and mean
conservation, and obtains a deficient unit residue for every finite ternary
weight table and every fixed positive grouping depth. The repeated
one-halving branch at residue -s supplies strict excess.

[FibreActual.lean](FibreActual.lean), [FibreMassError.lean](FibreMassError.lean)
and [FibreDeficit.lean](FibreDeficit.lean) identify every actual predecessor
without duplicate counting, bound the one-generation affine mass error,
and prove a persistent deficient odd progression with divergent reciprocal
mass. Deleting a globally finite reciprocal-mass set cannot repair uniform
reproduction. Higher-depth actual errors and fate-specific harmonic
divergence remain separate questions; see the
[proof map](../../../docs/theory/collatz_actual_fibre_mass_lean_note.md).

[FibreGeneration.lean](FibreGeneration.lean) proves the complete conditional
generation-series criterion for the plus map. The concrete residue operator
is bounded by actual reciprocal generation mass; nonperiodicity makes the
generations disjoint. Divergence of the coefficient series implies divergent
reciprocal mass of actual positive odd unit ancestors. The coefficient-series
divergence premise itself remains open; see the
[proof map](../../../docs/theory/collatz_generation_mass_lean_note.md).

[FibreDistortion.lean](FibreDistortion.lean) proves the negative-map counterpart
with a sixth-root depth loss. Distinct odd states on a path to a nonperiodic
target control the accumulated affine correction. The complete residue
coefficient equals the sum over actual paths, and divergence of the corrected
coefficient series implies divergent actual ancestor reciprocal mass. Its
arithmetic premise remains open; see the
[proof map](../../../docs/theory/collatz_negative_generation_mass_lean_note.md).
