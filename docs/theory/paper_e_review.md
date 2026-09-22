# Paper E: reviewer packet and living review record

Version 0.1.0, 22 September 2026. Canonical manuscript:
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
| 2.1, 2.3 | Classical Bernstein-Lagarias coding; CollatzPadic | No new distribution estimate |
| 3.1, 3.2 | CollatzPadic order and return-time proofs | Original start must be periodic |
| 4.1 | Written proof in manuscript and denominator dossier | External equidistribution; no Lean coverage |
| 5.1-5.4 | PreimageGrid, Domain, Growth, Density, Certificate12 | Human prose-to-statement review pending |
| 6.1 | PreimageBalance | Fixed shifts only; no actual-count upper bound |
| 7.1 | BackwardMass | Backward closure is weaker than fate closure |
| 7.2 | CollatzMoments | Bounded identities do not justify unbounded equality |

The machine-readable [validation record](paper_e_validation.json) pins
the local Lean dependency closure and records the finite checks.

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

### 0.1.0 - 22 September 2026

First complete living manuscript: exact orbit code and period theorem,
actual modular-return family, signed 21/25 ancestor bound with its proof,
fixed-grid ceiling, mass and stopping counterexamples, formalization map,
references, AI disclosure, and reproducible source/deposit package.
The older exploratory bridge assessment predates these completed results.
No new arithmetic attack is opened by the publication work.
