# Paper B: the nonzero-offset anchor

## Problem

Bound the nonzero-offset anchor family at zero total undifferenced
Y frequency, with the signed decorations required by Paper B.

## Exact statement

For every fixed C,M and epsilon>0, the actual branch sum (O4) in
[the report](../theory/paper_b_offset_anchor_report.md) satisfies
O_(C,M,epsilon)(P^(23/24+epsilon)).
The positive integers k,h_1,h_2 and decoration shifts are O_C(P^(1/24)),
j is a nonzero integer with |j|<=2, and each signed wave coefficient
obeys |a_b|r_b<=CP^(1/2). The input partition has local cell count
C(1+L P^(-1/4)); the coefficients are constant there,
|psi''|<=CP^(-1/4), and eta has bounded sup norm plus variation per cell.
The permitted slow modes and already-differenced D2 factors are
specified in Section 7 of the report. Arbitrary undifferenced floor
anchors are not included in that extension.

## Current literature

**Extended:** this is the next local repair after the D2, signed
zero-offset, and wave-bearing supplements. It uses standard centered
Fourier expansions and second-derivative bounds as in Graham and
Kolesnik, Van der Corput's Method of Exponential Sums (1991), linked
in the report. No literature-wide priority claim is made.
The historical Step 5(a) coefficient is corrected below.
No independent mathematical review or new literature id.

## Branch budget

This records the triage announced before writing the proof.

- **Target:** bound the nonzero-offset anchor at zero total Y frequency.
- **Novelty hypothesis:** center the large anchor coefficient and use a
  shorter Fourier cutoff to preserve curvature dominance.
- **Falsifier:** the frozen-floor subtraction or partition costs remove
  the claimed saving.
- **Already killed by?:** the individual-wave dominance failure in
  [negative knowledge](../negative_knowledge.md) does not apply;
  the present argument bounds the sum of all wave curvatures against
  a larger anchor scale.
- **Existing machinery:** exact carries, centered Fourier expansions,
  monotone floor crossing counts, and second-derivative bounds.
- **Maximum Phase-0 scope:** prove or block this family with signed
  decorations over its specified ranges.
- **Promotion criterion:** verify the full phase, coefficient ranges,
  and every original, input, floor, and frequency cut.
- **Stop criterion:** leave kernel assembly for a separate audit.

## Balanced-ternary formulation

The source and its floor images admit canonical balanced-ternary
representations. This proof uses exact integer carry differences
and real frozen-branch functions, independently of the radix.

## Why BT may be relevant

Balanced ternary remains a tool for exact integer bookkeeping in
the laboratory. No cancellation estimate here depends on it.

## Candidate operations / invariants

- **EXACT — HUMAN PROOF**, J-paper-b-offset-anchor-sums:
  center B_*=(9/16)kj x^(3/8)+(9/4)alpha x^(-1/4), retain residual
  frequencies at P^(5/16), and keep the full frozen-floor subtraction.
- **REFUTED**, J-paper-b-offset-composite-729:
  the historical coefficient 729/512 is not the coefficient of the
  full anchor-plus-center curvature. The corrected coefficient is 81/64.
  This does not refute a power-saving estimate.

The written-proof label does not mean independent review.

## Experiments

Runner: tools/validate_paper_b_offset_anchor.py, optionally with
--output <json path>. The
[validation record](../theory/paper_b_offset_anchor_validation.json)
contains 13 frozen coefficient/correction controls, 6612 signed
centering cases, 1155 carry/endpoint cases, 1792 branch-decomposition
cases, and 36 rational exponent controls. All pass.
These finite controls do not independently prove analytic cancellation.

## Conjectures

No new conjecture is registered. The complete kernel and OOOEE
transfer remain open.

## Counterexamples

The exact coefficient audit is
945/512 - 81/512 - 216/512 = 81/64.
The historical 729/512 omits c''J at leading order, with
J=floor(G)=G+O(1). The discrepancy is exactly 81/512.
This is an algebraic refutation of a displayed identity, not a
numerical orbit counterexample; its regression control is the named
validator above and its permanent entry is in negative knowledge.
The archival source is preserved.

## Formalization

No Lean module is claimed. This is an AI-assisted written proof
with exact rational controls; independent review is outstanding.

## Results

The full proof is in the [report](../theory/paper_b_offset_anchor_report.md).

1. The corrected anchor-plus-center curvature is
   (81/64)kj x^(-1/8)+O_(C,M)(P^(-3/16)).
2. Every retained mode has one-signed curvature comparable to
   k|j|P^(-1/8), uniformly for both signs and the widened decorations.
3. All floor-level, input, carry, and center cuts number O_(C,M)(P^(3/4)).
4. Summing second-derivative bounds gives O_epsilon(P^(23/24+epsilon)).
   The permitted already-differenced D2 errors and modes fit this bound.

No new kernel theorem, OOOEE count, certificate density, or release.

## Open questions

Verify every twice-differenced kernel term against the exact
hypotheses of the three family estimates, including coefficient
mass, exceptional sets, and partition requirements. The later
OOOEE mixed-mode transfer remains a separate requirement.

## Decision

**PROMOTE** the stated nonzero-offset estimate and coefficient
correction. The retained Fourier frequencies are below the
curvature-cancellation range and all partition costs fit the bound.
The best next question is: does every term in the twice-differenced
kernel decomposition fit a proved family, with all coefficient and
exceptional-set costs counted? This branch stops here.

## Publication assessment

Status: **THEOREM** (AI-assisted written proof; independent review
outstanding). Keep as a research supplement pending the kernel and
mixed-mode audits. The 27/32 manuscript, PDF, metadata, and existing
Zenodo deposit package are unchanged.

