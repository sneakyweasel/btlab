# Paper B: the OOEOE fifth-letter repair

Status: **PROMOTE**, 9 September 2026.

## Problem

Prove the OOEOE fifth-letter count after auditing the repaired four-step proof.

## Exact statement

Paper B Corollary 4.10 gives OOEOE(N) = N/32 + O(N^(47/48)).
Theorem 5.3 gives a specified five-step certificate subfamily of
density 27/32. The full five-step density 7/8 still requires OOOEE.

## Current literature

The exponential-sum and discrepancy tools are classical, as cited in
Paper B references 2–3. This revision supplies a new centering argument
for its concrete floor composition; no literature-wide priority claim
is made. The historical proof is not used as an analytic black box.

## Branch budget

- **Target:** count OOEOE with error o(N).
- **Novelty hypothesis:** smooth centering cancels the growing first-floor coefficient.
- **Falsifier:** interval boundaries or Fourier errors consume the saving.
- **Already killed by?:** the recorded inverse-fiber localization obstruction concerns another interval problem; this is a summed full-block estimate.
- **Existing machinery:** exact carries, the repaired four-step proof, classical second-derivative estimates, and exact validators.
- **Maximum Phase-0 scope:** audit 13/16, prove or block OOEOE, and give the general kernel a bounded feasibility assessment.
- **Promotion criterion:** every mixed mode, truncation error, and partition boundary is controlled.
- **Stop criterion:** record an unresolved estimate and retain explicit hypotheses.

## Balanced-ternary formulation

No representation change is used; the argument concerns exact floors of positive integers.

## Why BT may be relevant

The laboratory supplies the certificate definitions and exact arithmetic.
Balanced ternary is not claimed to produce analytic cancellation.

## Candidate operations / invariants

EXACT — HUMAN PROOF in the repository's written-proof sense:
the centered coefficient identity (4.19), summed interval estimate
(4.14), four-coordinate bound (4.16), and the 27/32 subfamily.

## Experiments

Publication validator: tools/validate_paper_b_ooeoe.py.
It checks 1,275 exact centering identities, the frozen-frequency
curvature coefficient, five squared-sum exponents, ten strict exponent
comparisons, and the certificate fractions. The two earlier validators
also pass. These tests do not prove asymptotic cancellation.

## Conjectures

No new conjecture. The OOOEE correlation and general decorated kernel remain open.

## Counterexamples

No counterexample to the desired kernel is asserted. Its historical
D2 frequency-support accounting has an unresolved continuous-part tail;
the bounded assessment is recorded in the report.

## Formalization

No new Lean formalization or independent peer review.

## Results

See [Paper B](../theory/juggler_parity_discrepancy_note.md), Lemmas
4.7–4.8, Theorem 4.9, Corollary 4.10, and Theorems 5.3–5.4.
The [OOEOE report](../theory/paper_b_ooeoe_report.md) records the
four-step audit, all new costs, and the remaining kernel work.

## Open questions

The OOOEE correlation, full D2 Fourier-error accounting, general
decorated kernel, short-interval extension, and universal termination
remain unproved here.

## Decision

**PROMOTE** the OOEOE split and the 27/32 certificate subfamily.
Best next question: does the complete D2 expansion retain a positive
saving sufficient to prove the remaining OOOEE correlation?

## Publication assessment

Status: **PAPER_CANDIDATE**. The manuscript contains written proofs
for the stated results and explicit hypotheses for the remaining
extensions. The finite checks do not provide independent analytic validation.
