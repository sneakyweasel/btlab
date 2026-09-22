# Paper E: reviewer packet and living review record

Version 0.2.0, 22 September 2026. Canonical manuscript:
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
| 4.1 | Written proof in manuscript and denominator dossier | External equidistribution; no Lean coverage |
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

The combined audit now selects 28 declarations. The local statement check
also confirms that Theorem 5.1 covers every positive target prime to three,
all sufficiently large natural cutoffs, distinct starts rather than paths,
and both capped and ordinary ancestor counts. Independent review remains
separate from this local check.

## Remaining Lean project: Theorem 4.1

Theorem 4.1 is still a written proof. A source search of the installed
Mathlib found no applicable Weyl, van der Corput, or Boshernitzan
equidistribution theorem. Closing it requires the fixed-parameter joint
equidistribution of the displayed power vector, positive-box visits, and
their translation into actual nested-floor branches and modular returns.
The word-denominator calculation and its unboundedness must also be
connected to those prefixes. The finite witnesses do not establish this.

The present completion phase stops at that analytic prerequisite. No
placeholder, extra assumption, or conditional theorem is substituted for
the claimed unconditional result. Formalizing the needed power-function
equidistribution is a separate substantial project; no assertion that all
of Paper E is Lean-verified is made.

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
- Pending: independent review of the written Theorem 4.1 and its use
  of Boshernitzan's criterion.
- Pending: specialist novelty comparison for the signed exponent and
  obstruction statements. No claim of literature priority is certified.
- Pending: journal selection and adaptation to its submission rules.
- Pending: author decision to deposit; no DOI or publication date assigned.

Local build, exact checks, and the combined Lean audit are reproducible
using the build guide. These review items cannot be discharged by
re-running the typesetter.

## Version history

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
