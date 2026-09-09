# Paper B: the combined signed zero-offset family

Status: **PROMOTE**, 9 September 2026.

## Problem

Bound the zero-offset anchor and both signed differenced waves
without inferring dominance from the largest individual coefficient.

## Exact statement

Under (S1) in the [signed-wave report](../theory/paper_b_signed_waves_report.md),
the odd-input sum on Delta_1 Delta_2 m=0 of
e(c_d {Delta_1 Delta_2 Y}+u Delta_1 Y+u' Delta_2 Y+psi)
is O_epsilon(P^(31/32+epsilon)).
Here 1<=k,h_1,h_2<=P^(1/24), |u|h_1,|u'|h_2<=P^(1/2),
and psi has |psi''|<=C P^(-3/4) on a partition with local cell
count C(1+LP^(-3/8)).
Both signs and zero values of u,u' are allowed.
The specified slow modes and a fixed number of the prior D2
factors fit the same bound.

## Current literature

The derivative and Fourier tools are classical, as cited in
Paper B and the report. The specific contribution is a combined
signed-phase estimate with the original floor partitions.
Novelty: PROJECT-SPECIFIC; no literature-wide priority claim.

## Branch budget

- **Target:** does the combined zero-offset family retain a uniform power saving?
- **Novelty hypothesis:** retain the anchor and use the signed coefficient u h_1+u' h_2, with frequency weights near cancellation.
- **Falsifier:** Fourier errors or partition boundaries consume the saving.
- **Already killed by?:** the largest-individual-term inference is refuted. This proof estimates the combined phase directly and does not reopen inverse-fiber localization.
- **Existing machinery:** D2 reduction, exact carry arcs, centered Fourier expansion, and partition counting.
- **Maximum Phase-0 scope:** prove or block this signed family, verify D2 compatibility, and audit the scope of the conclusion.
- **Promotion criterion:** uniform treatment of both signs, zero modes, and every run/window boundary.
- **Stop criterion:** stop before claiming an unverified transfer to the full kernel or the OOOEE mixed modes.

## Balanced-ternary formulation

No representation change. The variables use exact integer floors
and real power functions.

## Why BT may be relevant

The laboratory supplies certificate definitions and exact controls.
Balanced ternary is not asserted to create analytic cancellation.

## Candidate operations / invariants

EXACT — HUMAN PROOF in the written-proof sense:
the quadratic partition estimate (S4), signed zero-offset bound
(S2), and its compatibility with the stated D2 factors.

## Experiments

[Exact validator](../../tools/validate_paper_b_signed_waves.py):
3,375 cancellation triples; 4,300 wave-only centering cases;
1,710 quadratic interpolation and coordinate-change cases;
196 coefficient-convolution controls; eight curvature coefficients;
and 22 error, partition, and regime exponents.
Results: [validation record](../theory/paper_b_signed_waves_validation.json).
The controls do not independently validate asymptotic cancellation.

## Conjectures

No new conjecture. The general kernel, its mixed-mode transfer,
and the OOOEE correlation remain open.

## Counterexamples

The earlier cancellation witnesses remain valid counterexamples
to the largest-individual-wave dominance inference.
The new proof includes those cases.
Centering the anchor coefficient as part of a moving center can
erase its leading curvature in an attempted global comparison;
the new proof centers only the wave coefficient.

## Formalization

No new Lean formalization or independent mathematical review.

## Results

Put A=|u h_1+u' h_2|P^(-1/4).
For A<=P^(1/32), a quadratic sublevel bound gives
O(P^(15/16) log(P)^C) per frequency window and at most
O(P^(1/32)) windows.
For larger A, only O(1) combined frequencies per window can
have small curvature, and their coefficient mass is O(log(P)/A).
Their total cost is O(P log(P)/A); the other terms are smaller.
Together these give exponent 31/32, up to epsilon.

The D2 phases have curvature O(P^(-15/16)) and partitions within
the permitted density. Their coefficient variation and absolute
errors fit this proof. This verifies that particular transfer.

## Open questions

Audit the wave-bearing family with nonzero total Y frequency,
including widened D1 decorations, weights, and boundaries.
The nonzero-offset anchor family and OOOEE mixed-mode transfer
also remain to be verified.

## Decision

**PROMOTE** the combined signed zero-offset estimate.
Best next question: can the wave-bearing family with nonzero
total Y frequency, including its widened D1 decorations, be
proved uniformly with a positive power saving?
This pass stops at that separate assembly requirement.

## Publication assessment

Status: **THEOREM**, in the repository's written-proof sense.
This is a research supplement awaiting independent mathematical
review. The 27/32 manuscript, PDF, and Zenodo package are unchanged.

