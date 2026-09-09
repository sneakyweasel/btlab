# Paper B: D2 expansion and signed-wave assembly

Status: **PROMOTE**, 9 September 2026.

## Problem

Determine whether the two identified D2 errors consume the kernel's
remaining power saving.

## Exact statement

On the fixed carry-label extensions and parameter ranges in the
[D2 report](../theory/paper_b_d2_report.md), the factor
e(-Delta_(2h)(c floor(F(m)))) has a centered Fourier expansion with
total absolute error O(P^(15/16) log P). On each refined interval
the coefficient mass plus total variation is O(log P).
Every retained mode has second derivative
O(P^(-3/16) u h P^(-3/4)) for u>=1/2.
These are reduction and perturbation bounds; they are not an
exponential-sum estimate for the assembled signed phase.

## Current literature

The Fourier expansion and van der Corput tools are classical,
with sources in the report and Paper B. The specific contribution
is the error accounting for this floor composition.
Novelty: PROJECT-SPECIFIC; no literature-wide priority claim.

## Branch budget

- **Target:** does complete D2 error accounting retain a positive saving?
- **Novelty hypothesis:** center the coefficient and count actual floor crossings.
- **Falsifier:** a necessary majorant or partition cost reaches order P.
- **Already killed by?:** the inverse-fiber localization obstruction concerns another interval problem. This is a full-block fixed-label reduction and does not reopen that route.
- **Existing machinery:** exact carries, the repaired centered Fourier lemma, and the basic collision model.
- **Maximum Phase-0 scope:** repair the two D2 losses, propagate them conditionally, and identify the first remaining assembly gap.
- **Promotion criterion:** a written reduction with every error and new boundary charged.
- **Stop criterion:** stop at an uncontrolled combined signed phase; do not restore the kernel from conditional exponent arithmetic.

## Balanced-ternary formulation

The proof uses real powers and exact integer floors. No representation
change is required.

## Why BT may be relevant

The laboratory provides the certificate definitions and exact controls.
Balanced ternary is not claimed to supply analytic cancellation.

## Candidate operations / invariants

EXACT — HUMAN PROOF in the repository's written-proof sense:
the monotone slow-variable count, floor-crossing reduction, centered
D2 expansion, and its curvature comparison. The largest-individual-wave
dominance inference is REFUTED by an exact signed cancellation.

## Experiments

[Exact validator](../../tools/validate_paper_b_d2.py):
2,989 centering cases; 8,649 floor-product differences; 1,331
sequence triples for signed cancellation; four derivative coefficients;
twelve positive error exponents; four curvature-ratio exponents;
two conditional differencing chains; and near-integer controls.
Results: [validation record](../theory/paper_b_d2_validation.json).
These checks do not prove the asymptotic estimates.

## Conjectures

No new distribution conjecture. The general kernel and OOOEE
correlation remain unproved.

## Counterexamples

With h_1=h_2=1 and u'=-u, the two differenced waves cancel
identically although their individual scales can greatly exceed
the anchor scale. With h_2=2h_1 and u'=-u/2, they combine into a
second difference. This refutes the historical dominance inference,
not the target kernel bound. See the report's Section 8 and
[negative knowledge](../negative_knowledge.md).

## Formalization

No new Lean formalization or independent mathematical review.

## Results

The literal continuous-part tail costs O(P^(47/48)).
The centered D2 reduction improves its complete absolute-error
budget to O(P^(15/16) log P), using direct floor-crossing counts
instead of individual near-integer carry majorants.
Additional run/window endpoint costs are at most O(P^(11/12))
where the complete phase has curvature comparable to the base wave.

If all remaining inner sums meet the same budget, three differencing
stages would give a kernel exponent 127/128, up to epsilon.
That antecedent is unproved. There is no new OOOEE count or density.

## Open questions

Control the zero-offset anchor and both signed differenced waves
together, including their Fourier weights and all run boundaries.

## Decision

**PROMOTE** the D2 reduction and its complete error accounting.
Best next question: does the combined signed zero-offset family,
after the D2 reduction, admit a uniform power-saving bound including
equal-shift and leading-cancellation cases?
This pass stops before opening that follow-up.

## Publication assessment

Status: **STRUCTURAL**. This is a research supplement.
The manuscript, PDF, and Zenodo package retain the existing 27/32
result and the explicit OOOEE hypothesis.

