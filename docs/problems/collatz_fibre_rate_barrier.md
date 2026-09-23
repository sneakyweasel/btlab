# Near-critical periodic weights already require a global cell bound

23 September 2026. **EXACT — HUMAN PROOF**, with kernel-checked declarations;
independent review and advisory statement coverage remain pending.

## Problem

Does evaluating the [greatest capped subsolution](collatz_fibre_subsolutions.md)
at a fixed integer make its near-critical rate family a local arithmetic
target? This audit checks the strength of that premise before spending
another campaign on finite tables or on the proposed rate 1-1/r.

## Exact statement

Write C_d^s for the complete all-source signed inverse coefficient. Suppose
h is a periodic subsolution modulo 3^r, with 0<=h<=1, zero at nonunits,
L_s h>=q h and q>=0. For any coordinate b and every positive odd unit a,

\[
 C_{d+1}^s(a)\ \ge\ \kappa_r h(b)q^d,
 \qquad \kappa_r=\frac3{2^{2\cdot3^r}}>0,
 \qquad d\ge0.                                          \tag{1}
\]

The same constant works for every such a and every d. Only h(b)>0 is
needed to make it positive; positivity at the other coordinates is not
assumed.

Consequently, if nonzero periodic subsolutions exist at nonnegative rates
q_i tending to one, at possibly varying levels and with possibly varying
positive coordinates, then

\[
 \forall\,0<t<1\quad\exists c_t>0\quad
 \forall d\ge0\quad\forall a\in2\mathbb N+1,\ 3\nmid a:
 \quad C_{d+1}^s(a)\ge c_t t^d.                          \tag{2}
\]

In particular, nonzeroness of H_(r_i,q_i) at just one prescribed ordinary
integer already implies (2). No lower bound relative to 1-q_i is required
for this implication. Such a prefactor bound would be an additional
requirement for the previously checked divergence theorem.

Neither (2) nor a near-critical family is established here. The conclusion
is a necessary-condition audit, not a refutation of either statement.

## Current literature

Tao's [2020 inverse-density note](https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/),
registered as `tao-2020-syracuse-preimage-density`, defines the smallest
Syracuse atom c_n and conjectures c_n=3^(-n+o(n)). Its Proposition 3 assumes
that conjecture to obtain ancestor counts X^(1-o(1)). That proposition
does not itself establish reciprocal-mass divergence.

For plus, the existing coarse-cell identification is
min_a C_n^+(a)=3^n c_n. Statement (2) is the geometric form of the same
subexponential lower requirement: for every fixed t<1 it supplies a
positive constant multiplying t^(n-1). Conversely the subexponential
asymptotic supplies such constants, using positivity for the finitely
many initial depths. The elementary unit-class mean bound min C_n<=3/2
gives the matching upper exponential rate. This translation to the
published notation is a written interpretation of the existing cell
identification; the new Lean statements use the exact coefficient C.

The one-step transport and geometric comparison are **KNOWN** mechanisms,
already formalized separately in the laboratory. This phase records their
consequence for the newly proposed family. It is not a new proof of Tao's
conjecture or a claim that the general fixed-root divergence problem is
equivalent to it.

## Branch budget

- **Target:** do nonzero periodic weights with rates approaching one already force uniform subexponential cell bounds?
- **Novelty hypothesis:** capping might weaken the uniform arithmetic requirement.
- **Falsifier:** one-step residue transport preserves every certified exponential rate globally.
- **Already killed by?:** fixed-class transport is known; its consequence for varying-level subsolutions has not been made explicit.
- **Existing machinery:** actual predecessor transport and the checked geometric minorant theorem.
- **Maximum Phase-0 scope:** prove the explicit transport bound and its near-critical consequence; no larger residue census.
- **Promotion criterion:** a route that avoids the global minimum-cell premise.
- **Stop criterion:** close that interpretation if the global premise is unavoidable.

## Balanced-ternary formulation

A nonzero table coordinate is a whole cylinder modulo 3^r. Its value is
the same at every ordinary integer in that cylinder. Evaluating the table
at a fixed root does not remove this periodicity.

## Why BT may be relevant

The ternary modulus determines the explicit access cost kappa_r. That
cost can be extremely small, but at a fixed chosen level it does not
depend on later inverse depth. This distinction is essential when taking
an exponential rate in depth.

## Candidate operations / invariants

Fix b with h(b)>0. For each positive odd unit target a, the existing
bounded residue-access theorem supplies an actual one-step predecessor
m congruent to b modulo 3^r, with halving exponent at most 2*3^r. Hence

\[
 C_{d+1}^s(a)\ge\kappa_r C_d^s(m)
             \ge\kappa_r h(b)q^d.
\]

The chosen predecessor is valid at every later depth. To obtain (2), fix
t<1 first, choose one i with q_i>t, and keep that level, table and constant
fixed while d varies. This order of quantifiers avoids any unjustified
uniform bound on kappa_(r_i) as the levels increase.

## Experiments

No new numerical campaign. The statement follows from actual predecessor
identities and an all-depth Lean inequality. The earlier finite tables
remain valid evidence at their stated rates; they supply no sequence of
rates tending to one.

## Conjectures

No new registered conjecture. The proposed H_(r,1-1/r)(a)>=c_a/r would
imply (2) even if the quantitative lower bound were weakened merely to
eventual strict positivity. It therefore carries the global rate problem
as a prerequisite.

## Counterexamples

A subexponential floor is not enough for nonsummability. The positive
scalar sequence f_d=1/(d+1)^2 is summable but has a lower bound c_t*t^d
for every fixed t<1 and some c_t>0. For example, putting p=sqrt(t), the
geometric-series bound (d+1)*p^d<=1/(1-p) gives
f_d>=(1-p)^2*t^d. This written scalar example is not a Collatz trajectory
or a counterexample to actual coefficient divergence. It explains why
(2) cannot replace the prefactor condition in the earlier criterion.

## Formalization

[FibreRateBarrier.lean](../../formal/Problems/Collatz/FibreRateBarrier.lean)
proves `global_lower_of_subsolution` with the explicit kappa_r in (1),
and `exists_global_lower` when the selected coordinate is positive.
`UniformSubcriticalLower` defines (2).
`uniform_lower_of_nearcritical_weights` proves it for any nonzero family
whose rates tend to one; `uniform_lower_of_maximal_weights` specializes
that result to the greatest capped tables.

The proof reuses `exists_coarse_lower_transport` and
`coarse_geometric_lower`; it does not duplicate the residue-access proof
or assume random parity, spectral mixing, or a lower-count estimate.
The [executable audit](../../formal/AxiomCheckCollatzRateBarrier.lean) and
[expected dependencies](../../formal/AxiomCheckCollatzRateBarrier.expected)
cover all four public theorems. The published-cell translation and scalar
separation example above are written arguments, not new Lean declarations.

The full active build passes 9,030 jobs, and the style gate reports no new
violations. All four audit results use only propext, Classical.choice and
Quot.sound. Existing exact controls for actual class transport and finite
subcritical certificates exercise the reused arithmetic inputs; no numerical
test is treated as evidence for the all-level rate-family conclusion.

## Results

The capped construction retains a finite optimization advantage, but its
rate-family existence is not a weaker local replacement for the uniform
Syracuse-cell problem. The proposed 1-1/r scale is an ambitious arithmetic
hypothesis, not a consequence of the finite improvements. Moreover, a
positive fixed-root-to-deficit ratio would still be needed after obtaining
near-critical rates.

This corrects the priority assigned to that scale in the preceding phase.
No actual coefficient lower count, divergence, Juggler pressure estimate,
termination or infinite escape is proved.

## Open questions

Can actual inverse words at a prescribed nonperiodic positive odd unit
root a give a nonsummable lower bound directly, for example a constant
lower bound on the dyadic-depth sums
sum_(2^j<=d<2^(j+1)) C_d^s(a), for all sufficiently large j? Such a bound
must concern that ordinary integer, without periodic extension to every
integer in its residue class. This remains an unproved target; no new
word-count experiment is opened in this phase.

## Decision

**CLOSE** interpreting the capped near-critical family as an easier local
route around the global minimum-cell problem. Retain the finite certificates
and conditional divergence theorem. The next best question is the direct
fixed-integer depth-block lower bound above, with arithmetic congruence and
actual realization retained.

## Publication assessment

Status: `STRUCTURAL`. A checked necessity implication clarifies the strength
of the remaining premise. No paper or publication claim is changed.
