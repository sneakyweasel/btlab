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

[SignedOrbitPacking.lean](SignedOrbitPacking.lean) extends the exact binary
moment and packing bound to both signs and finite nonrepeating paths.
[UniformFibreDistortion.lean](UniformFibreDistortion.lean) uses the summable
terminal-window correction to replace the sixth-root allowance with one
absolute constant, uniformly over all depths and nonperiodic targets.
Unweighted coefficient-series divergence suffices for both signs; that
premise remains open. See the
[proof map](../../../docs/theory/collatz_uniform_generation_mass_lean_note.md).

[FibreStopping.lean](FibreStopping.lean) proves that allowing a different
stopping depth on every inverse branch does not repair uniform coefficient
reproduction when all branches share one finite horizon. Its envelope is
attained and bounds every history-dependent policy, for both signs and every
finite periodic terminal weight positive at the one-halving residue. Unbounded
stopping and fixed-integer series divergence remain open; see the
[dossier](../../../docs/problems/collatz_bounded_fibre_stopping.md).

[FibreHeightBudget.lean](FibreHeightBudget.lean) approximates either complete
generation coefficient by finite actual inverse paths with total halving
exponent at most B, losing at most 6^d*(3/4)^B. Budgets B=8d lose at most
(19683/32768)^d and preserve coefficient-series divergence. At positive odd
targets, all retained sources are actual depth-d ancestors below m*256^d.
The conditional reciprocal-ancestor consequence is checked for both signs;
the required coefficient lower bound remains open. See the
[height-budget dossier](../../../docs/problems/collatz_fibre_height_budget.md).

[FibreMixing.lean](FibreMixing.lean) constructs artificial coherent ternary
densities with positive unit cells and uniform exponential refinement control,
but a summable density series at any prescribed ordinary unit integer. Both the
unit row `(0,1,1)` and Syracuse row `(0,1,2)` are covered. An explicit checked
inequality distinguishes the model from the actual signed coefficient operator.
This closes inference from mixing and coherence alone, not the fixed-root
Collatz lower bound; see the [dossier](../../../docs/problems/collatz_fibre_mixing.md).

[FibreUnitComparison.lean](FibreUnitComparison.lean) compares the complete unit
coefficient with the all-source coefficient at the same depth and root.
The retained fraction lies between 5/21 and 20/21 for both signs and every
positive depth. Their depth series, and the existing finite-budget series,
are summable simultaneously. The fixed-root coarse-count lower bound remains
open; see the [dossier](../../../docs/problems/collatz_fibre_unit_comparison.md).

[FibreLocalBounds.lean](FibreLocalBounds.lean) transports actual one-halving
peaks into every fixed ternary unit neighborhood, for both signs. Unit and
all-source coefficients exceed every bound at arbitrarily large depths and
positive odd targets in that neighborhood. The targets vary with depth;
fixed-integer divergence remains open. The bounded local averages therefore
cannot support a depth-independent local Harnack comparison. See the
[dossier](../../../docs/problems/collatz_fibre_local_bounds.md).

[FibreRunTail.lean](FibreRunTail.lean) bounds the complete coefficient of
one arbitrary first exponent followed by d one-halving steps at a fixed
positive root a. It is at most 3a/2^(d+1), with total allowance 3a across
all run lengths, for both signs except the negative fixed point one.
Exact integer words, actual returns and that growing exception are checked.
This family can be discarded with a summable loss; the remaining word count
is open. See the [dossier](../../../docs/problems/collatz_fibre_run_tail.md).

[FibreLowerTransfer.lean](FibreLowerTransfer.lean) reaches any fixed ternary
class from every positive odd unit root through one actual inverse step.
The exponent is at most 2*3^r. A uniform local coefficient or depth-block
lower bound therefore transfers globally at cost 3/2^(2*3^r) and one depth
shift. Divergence at every nonperiodic integer in a fixed unit class is
equivalent to divergence at all nonperiodic unit roots. Both premises remain
open; this does not establish a fixed-root lower count. See the
[dossier](../../../docs/problems/collatz_fibre_lower_transfer.md).

[FibreMinorants.lean](FibreMinorants.lean) turns a normalized periodic weight
with `L_s h >= q*h` into the complete bound `C_d(a) >= q^d*h(a)`. A family
with `q_i -> 1` forces coefficient-series divergence at a fixed positive root
if `h_i(a) >= c*(1-q_i)` for one positive constant c. The family is an open
premise. Eight exact Python certificates at levels one through four do not
establish this limit. See the
[dossier](../../../docs/problems/collatz_fibre_critical_minorants.md).
