# Paper E: reviewer packet and living review record

Version 0.7.0, 22 September 2026. Canonical manuscript:
[The Juggler Map and the 3n±1 Maps](juggler_signed_collatz_note.md).
Build and updates: [PAPER_E_BUILD.md](PAPER_E_BUILD.md).

## Review order

1. Read Theorem 3.2 with its actual-periodicity hypothesis. Compare it
   with CollatzPadic.periodic_bridge and the monotone-fibre argument.
2. Read Theorem 5.1 and Lemmas 5.2-5.4 as one proof. In particular check
   the sign-dependent height budget, subtree disjointness at nonperiodic
   roots, the closed domain, and dyadic interpolation.
3. Independently run the exact certificate verifier and inspect its
   corruption test. The numerical weight search is not a premise.
4. Read Theorem 6.1 at the stated fixed grid and at-most-linear rate.
   It bounds certificate exponents, not actual ancestor exponents.
5. Audit Theorem 4.1's fixed-parameter equidistribution argument and
   the distinction between a periodic-word code and an actual orbit code.
6. Check the known/new distinction against the cited primary sources.

## Claims and source map

| Paper item | Evidence | Review limitation |
| --- | --- | --- |
| 2.1, 2.3 | CollatzPadic; PaperECompletion series and frequency theorems | No new distribution estimate |
| 3.1, 3.2 | CollatzPadic order and return-time proofs | Original start must be periodic |
| 4.1 | PaperERecurrence.theorem41, with proved BoxRecurrence and exact construction | Fixed parameters; no shrinking-target or growing-depth bound |
| 4.2 | PaperECorollaries.return_starts_asymptotic, returnStarts_actual, return_in_multiplicative_interval | Counts the explicit family; fixed relative intervals only |
| 4.3 | PaperECorollaries.signature_parameter_density, modular_return_of_signature, signature_returns_infinite | Fixed residues and modulus; parameter density |
| 5.1-5.4 | PreimageGrid, Domain, Growth, Density, Certificate12 | Human prose-to-statement review pending |
| 6.1 | PreimageBalance | Fixed shifts only; no actual-count upper bound |
| 7.1 | BackwardMass | Backward closure is weaker than fate closure |
| 7.2 | CollatzMoments; PaperECompletion direct word sums | Bounded identities do not justify unbounded equality |

The machine-readable [validation record](paper_e_validation.json) pins
the local Lean dependency closure and records the finite checks.

## Formal coverage completed in 0.2.0

The new PaperECompletion module proves six manuscript-facing statements:

- The compatible-residue code has the sum in (2.4), indexed by precisely
  the odd times. The exponent index equals the number of earlier odd times.
  A telescoping remainder has norm at most 2^(-k), so convergence is proved
  without a termination hypothesis, including finite or empty odd-time sets.
- The limiting-frequency equivalence is proved for every finite word and
  corresponding residue, by equality of finite-source counts.
- The ordinary ancestor result is stated with the real exponent 21/25.
- The fixed-grid hypotheses imply the logarithmic exponent ceiling 99/100.
- Both masses equal one on every finite full binary prefix tree.
- Proposition 7.2 is proved directly on minimal stopping words. A proved
  equivalence regroups this type by length; summability is established
  before regrouping.

The 0.2.0 audit selected 28 declarations. The local statement check
also confirms that Theorem 5.1 covers every positive target prime to three,
all sufficiently large natural cutoffs, distinct starts rather than paths,
and both capped and ordinary ancestor counts. Independent review remains
separate from this local check.

## Theorem 4.1: exact construction completed in 0.3.0

PaperEModularReturn proves the initial odd perfect-power run, arbitrary
depth integer-root cells, equality with the real-power floors, and the
fractional-part box implications for every branch parity and endpoint
residue. Each box visit with s at least 2^(2^(b+1)) gives a genuine
expanding O^a E^b prefix, with every intermediate state at least its start.

The reduced rational denominator is exactly (4.2). Its unboundedness
is unconditional and has the explicit sufficient threshold
a >= 2*(2^b+(Q+1)*(2^b-1)) for q_(a,b) > Q.

The Lean declaration theorem41_of_box_recurrence assembles the full
conclusion with an explicit BoxRecurrence premise: for every T, some
parameter t >= T belongs to the simultaneous box. It proves infinitude
of distinct starts above every B, not just existence of one parameter.

The 0.3.0 selected audit had 32 declarations, including this conditional
assembly and three other new results. Standard logical dependencies
do not remove explicit theorem hypotheses. The assembly is not an
unconditional formalization of Theorem 4.1.

## Theorem 4.1: analytic completion in 0.4.0

PaperERecurrence.box_recurrence proves simultaneous visits of the fixed
power vector along s=1+2Mt. Every exponent 3^a/2^(j+1) is positive and
noninteger, and different depths have distinct exponents. The exact
coordinate scalings and box endpoints are checked, including M=1.

The analytic proof uses the classical first-derivative estimate and
van der Corput induction on actual shifted differences. All derivative
asymptotics, lower-order terms, nonzero modes, and positive affine
progressions are proved. Mathlib's uniform density of Fourier monomials
then gives convergence for continuous functions. A nonnegative continuous
function supported inside an open box has positive Haar integral and
forces arbitrarily late visits. This avoids importing Boshernitzan's
Hardy-field theorem as an assumption; its citation remains a separate
written justification of the same fixed-function input.

PaperERecurrence.theorem41 applies that recurrence proof to the exact
construction, with only a,b,M>0 and the expanding-word inequality as
hypotheses. The 0.4.0 selected audit covers 37 declarations, including
the unconditional assembly and its main analytic interfaces.

The local completion check compares each numbered mathematical statement
with the declarations in Appendix B, retaining the original target,
cutoff, and infinitude quantifiers. Independent statement coverage and
specialist review remain separate from this kernel-checked completion.

## Counting and residue corollaries in 0.5.0

Corollary 4.2 counts the explicitly constructed starts, with constant
1/(2^(b+2)*M^2) and exponent 1/2^(a-1). It also supplies a witness
in every sufficiently large fixed relative interval. Corollary 4.3
prescribes every even source residue and the exit residue, with exact
parameter density (2*M)^(-(b+1)). The expansion threshold removes
only finitely many parameters. All orbit guards remain proved.

The analytic extension passes from continuous Fourier averages to
weak convergence of empirical measures and half-open boxes with
Haar-null boundaries, including zero endpoints. The cutoff conversion
counts distinct starts, using the strict increase of (1+2*M*t)^d.
The selected paper audit now covers 56 declarations, including Theorem 4.4. A separate audit
covers all public theorems in the three new modules.

These are fixed-parameter consequences of classical equidistribution.
External novelty remains unclaimed. These qualitative corollaries do not
provide a first-witness bound; the separate Theorem 4.4 now supplies one
for OOE uniformly in the modulus. No infinite concatenation is asserted.

## Prior-art boundaries

Terras's parity classes and stopping combinatorics, Bernstein-Lagarias
coding, and the positive Krasikov-Lagarias exponent are explicitly
attributed. Sharpe's grid table and root-induction method are attributed
and carry the original MIT notice. The paper does not call those methods
new. The signed adaptation, the actual-period refinement, and the
isolated obstruction statements require a focused specialist priority
review before a strong external novelty claim.

The author should verify the original Prasad-Prasad preprint citation
and its precise overlap when preparing a journal submission. The present
text treats it as background and imports no proof from it.

## Remaining publication review

- Pending: independent prose-to-Lean statement coverage, especially the
  capped-tree count versus ordinary ancestors and all target quantifiers.
- Pending: independent review of Theorem 4.1's prose, its alternative
  classical reference, and its now-complete derivative/Fourier formal proof.
- Pending: specialist novelty comparison for the signed exponent and
  obstruction statements. No claim of literature priority is certified.
- Pending: journal selection and adaptation to its submission rules.
- Pending: author decision to deposit; no DOI or publication date assigned.

Local build, exact checks, and the combined Lean audit are reproducible
using the build guide. These review items cannot be discharged by
re-running the typesetter.

## Quantitative extension and review boundary

Theorem 4.4 and Appendix C reproduce the effective OOE proof and explicit
constants. Review the derivative sign on both frequency axes, real dyadic
endpoints, finite initial segment, saturated Fejer arcs and half-open
box boundaries. The selected 56-declaration Lean audit now includes
both errors, the exact predicate, positive count, and actual bounded
witness. OOEEffectiveReturn's separate audit checks all 23 theorems.
The formal derivative route proves sufficient estimates independently
of the precise external formula used in the written proof. Independent
mathematical review remains pending. The OOE word
has denominator one, so this does not quantify the large-denominator
construction.

## Version history

### 0.7.0 - 22 September 2026

Completed the quantitative Lean proof of Theorem 4.4, from finite
derivative tests to the exact OOE count and bounded actual witness.
Expanded the selected audit from 49 to 56 declarations, added the
23-theorem assembly audit, and archived the full analytic dependency
chain. All constants and theorem numbers are unchanged.

### 0.6.0 - 22 September 2026

Added Theorem 4.4 and its full quantitative proof in Appendix C, including
the uniform counting error and first-witness bound. Preserved all earlier
theorem numbers and the selected qualitative Lean audit.


### 0.5.0 - 22 September 2026

Added Corollaries 4.2 and 4.3 with complete written and Lean proofs:
exact counting of the constructed family, witnesses in fixed relative
intervals, and prescribed residues throughout the even run. Expanded
the selected audit to 49 declarations and rebuilt the publication kit.

### 0.4.0 - 22 September 2026

Completed Theorem 4.1 in Lean, including mixed-power cancellation,
the Fourier-to-box criterion, the precise exponent-vector specialization,
and the unconditional infinitude assembly. Expanded the selected audit
to 37 declarations. Updated the proof-status text and publication package;
the theorem numbers and mathematical conclusions are unchanged.

### 0.3.0 - 22 September 2026

Formalized Theorem 4.1's exact construction and reduced-denominator
arithmetic, including explicit growth thresholds. Added an infinitude
assembly conditional on BoxRecurrence. The missing analytic proof is
isolated and remains open in Lean. Expanded the selected audit to 32
declarations; the original theorem's quantifiers are unchanged.

### 0.2.0 - 22 September 2026

Closed the series-identification, frequency-limit, exponent-notation,
direct word-sum, and finite prefix-tree gaps in Lean. Expanded the selected
audit from 22 to 28 declarations and documented Theorem 4.1's remaining
analytic prerequisites. The mathematical claims and theorem numbers are
unchanged.

### 0.1.0 - 22 September 2026

First complete living manuscript: exact orbit code and period theorem,
actual modular-return family, signed 21/25 ancestor bound with its proof,
fixed-grid ceiling, mass and stopping counterexamples, formalization map,
references, AI disclosure, and reproducible source/deposit package.
The older exploratory bridge assessment predates these completed results.
No new arithmetic attack is opened by the publication work.
