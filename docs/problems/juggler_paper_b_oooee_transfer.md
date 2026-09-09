# Paper B: the OOOEE mixed-mode transfer

## Problem

Transfer the repaired dyadic methods to the exact four-coordinate
formal chain needed for OOOEE, including all mixed signs and zero
coordinates, and infer only its justified counting consequences.

## Exact statement

For X=n^(3/2), m=floor X, Y=m^(3/2), v=floor Y, Z=v^(3/2),
w=floor Z, and U=sqrt(w), every nonzero integer quadruple
(i,j,k,l) with maximum absolute value at most C P^(1/24) satisfies
the odd dyadic bound
sum e((iX+jY+kZ+lU)/2) = O_(C,epsilon)(P^(127/128+epsilon)).
Consequently OOOEE has count N/32+O_epsilon(N^(127/128+epsilon)),
and the full five-step power-envelope certificate class has
count 7N/8 with the same error. The
[proof](../theory/paper_b_oooee_transfer_report.md) states all
quantifiers and distinguishes formal signs from actual itineraries.

## Current literature

**Extended:** the local dyadic kernel and wave-bearing repairs.
The new phase includes k m^(9/4)/2 and l m^(9/8)/2; its composite
curvatures must be recomputed. Classical differencing and Fourier
discrepancy tools are used as in Graham and Kolesnik (1991), linked
in the report. No literature-wide priority claim is made.

## Branch budget

This records the triage announced before implementation.

- **Target:** prove every mixed mode required for OOOEE.
- **Novelty hypothesis:** difference the full phase, retain both
  powers of m, and recompute the combined curvature.
- **Falsifier:** a mode, floor error, or partition cost removes
  the claimed power saving.
- **Already killed by?:** this is a dyadic mixed-mode estimate,
  not localization to the rejected short fibers in
  [negative knowledge](../negative_knowledge.md).
- **Existing machinery:** kernel inventory, wave-bearing theorem,
  exact carries, and frozen-branch Taylor expansions.
- **Maximum Phase-0 scope:** prove or block the OOOEE transfer
  and its count.
- **Promotion criterion:** cover all signs, zero coordinates,
  coefficients, errors, and cuts.
- **Stop criterion:** keep any uncontrolled mode explicit;
  no automatic publication or further research branch.

## Balanced-ternary formulation

The floors and carries can be represented exactly in balanced
ternary. The real-power cancellation argument is radix-independent.

## Why BT may be relevant

Balanced ternary supports the laboratory's integer bookkeeping.
No additional cancellation is attributed to it here.

## Candidate operations / invariants

- Retain the fifth-coordinate power of m until after differencing.
- Conjugate the kernel master inventory, retaining negative centers
  and the original half-integer slow D frequency.
- Combine the pure power and fractional anchor before centering.
- Use the actual negative moving centers at zero offset.
- Apply discrepancy separately on each dyadic scale.

## Experiments

Runner: tools/validate_paper_b_oooee_transfer.py, optionally with
--output <json path>. The
[exact control record](../theory/paper_b_oooee_transfer_validation.json)
passes 3750 negative centered-master cases, 475 half-integer
frequency cases, 15 frozen-coefficient controls, 8 fifth-coordinate
derivative-exponent controls, and 49 rational exponent controls.
It also checks 10000 exact odd formal chains, 20000 certificate
union cases, and all 15 nonempty sign products, and reruns the
earlier exact kernel controls.

These finite checks do not establish asymptotic cancellation.
The integer census is a consistency check of the counted class.

## Conjectures

H(OOOEE;delta) is discharged by the written proof for every
0<delta<1/128. The historical 95/96 kernel target, arbitrary
decorations, localization, deeper counts, and all-depth fair-share
hypotheses remain unresolved.

## Counterexamples

No new refutation. The individual-wave dominance failure, omitted
integer-floor curvature term, and localization obstruction remain
valid. The present proof retains the full signed curvature and
charges positive errors globally.

## Formalization

No Lean theorem or independent mathematical review is claimed.
The repository's EXACT — HUMAN PROOF tag is used in its written-proof
sense; the work here is AI-assisted.

## Results

The report proves the mixed-mode estimate (T1), the OOOEE count
(T2), and the full five-step certificate count (T3).
The new composite coefficients are -243/512 on nonzero-offset
branches and 3645/2048 at zero offset after the negative moving
centers. The double correlation has exponent 31/32; the two
outer A-processes give 63/64 and 127/128. Both diagonals fit.
The k=0 modes and all other zero-coordinate cases are included.

The density 7/8 concerns the certificate class. It is not an exact
count of every start that descends in five steps, nor a termination
theorem.

## Open questions

Independent review of the analytic dependency chain is outstanding.
The next bounded step is manuscript consolidation and a fresh proof
audit before rebuilding the Zenodo release. No new exploratory
attack is needed for this specific five-step counting objective.

## Decision

**PROMOTE** the precise OOOEE mixed-mode theorem and its counting
consequences as written research results. All modes, errors,
coefficient masses, and partitions fit the displayed exponent.
This branch stops at that result.

## Publication assessment

Status: **THEOREM** at the level of an AI-assisted written proof,
with independent review outstanding. Keep the supplement available
for review; the current 27/32 manuscript, PDF, metadata, and deposit
package remain unchanged. Publication integration is the next
bounded step, not an automatic consequence of this branch decision.

