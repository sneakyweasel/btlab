# Paper B: small-shift and partition repairs

Status: **PROMOTE**, 9 September 2026.

## Problem

Repair the proof gaps identified in the publication review of Paper B.

## Exact statement

For fixed \(C\), the mixed sums in Paper B Theorem 4.5 are \(O_C(P^{23/24})\), uniformly for nonzero integer triples of size at most \(CP^{1/24}\). Corollary 4.6 and Theorem 5.2 give unconditional four-step certificate density 13/16 with error \(O(N^{23/24}(\log(2N))^3)\). The general decorated kernel is not asserted.

## Current literature

The second-derivative and discrepancy tools are classical (Graham–Kolesnik and Kuipers–Niederreiter, references 2–3 in Paper B). This is a repaired proof for the paper's concrete nested-floor family; no literature-wide priority claim is made.

## Branch budget

- **Target:** repair the nested estimate actually required for four-step descent.
- **Novelty hypothesis:** a smaller frequency-and-shift range suffices without the general kernel.
- **Falsifier:** an omitted floor or partition cost consumes the power saving.
- **Already killed by?:** the recorded wider-kernel barriers do not resolve this restricted proof audit; no growing-depth or universal-termination claim is introduced.
- **Existing machinery:** exact carry identities, finite Fourier truncation, second-derivative bounds, and the power-envelope certificate list.
- **Maximum Phase-0 scope:** prove the restricted estimate and its parity transfer; address the collision model directly if a partition-aware estimate can be proved.
- **Promotion criterion:** complete uniform estimates with all cell and truncation costs present.
- **Stop criterion:** keep any unclosed analytic implication conditional.

## Balanced-ternary formulation

No representation change is used. The arguments concern positive integers, exact floors, and rational exponent comparisons.

## Why BT may be relevant

The laboratory supplies the certificate definitions and existing exact validation. Balanced ternary is not claimed to supply cancellation.

## Candidate operations / invariants

EXACT — HUMAN PROOF, in the repository's written-proof sense: the small-shift carry expansion, the restricted mixed-sum bound, and the partition-aware curvature estimate.

## Experiments

The publication validators are tools/validate_paper_b.py and tools/validate_paper_b_repairs.py. The latter checks 1,920 endpoint identities, 2,000 carry expansions, and 40 exponent comparisons with exact rational arithmetic. Neither validator proves asymptotic cancellation.

## Conjectures

No new conjecture. The general kernel and two five-letter correlation hypotheses remain unproved.

## Counterexamples

No counterexample to the desired kernel estimate is claimed. The historical global-to-local rescaling remains unjustified.

## Formalization

No new Lean formalization. Existing Lean modules do not verify the analytic repairs.

## Results

See [Paper B](../theory/juggler_parity_discrepancy_note.md), Proposition 3.2, Lemmas 4.3–4.4, Theorem 4.5, Corollary 4.6, Theorem 5.2, and Lemma 7.5 / Proposition 7.6. The [repair report](../theory/paper_b_repair_report.md) states their scope.

## Open questions

The weighted assembly for all decorated kernel phases, the claimed local-kernel threshold, the five-step correlations, and universal termination remain open here.

## Decision

**PROMOTE** the completed restricted proof and basic collision-model estimate. Best next question: can every decorated phase and coefficient family satisfy Lemma 7.5's hypotheses with an adequate total weighted bound?

## Publication assessment

Status: **PAPER_CANDIDATE**. The repaired manuscript proves unconditional four-step certificate density 13/16; the higher results retain explicit hypotheses. Author and independent mathematical review remain distinct from the included automated checks.
