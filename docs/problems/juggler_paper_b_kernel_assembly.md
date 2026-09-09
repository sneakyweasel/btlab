# Paper B: dyadic kernel assembly

## Problem

Assemble the repaired phase families into a uniform dyadic monomial
kernel estimate without assuming the OOOEE transfer.

## Exact statement

For every epsilon>0, uniformly over integers 1<=k<=P^(1/24),
the sum over odd P<n<=2P of
e((3k/4)n^(9/8){floor(n^(3/2))^(3/2)})
is O_epsilon(P^(127/128+epsilon)).
The [report](../theory/paper_b_kernel_assembly_report.md) proves
the doubly differenced bound P^(31/32+epsilon) at
h_1<=P^(1/48), h_2<=P^(1/24), then checks both outer diagonal terms.
All constants are implicit. The historical 95/96 exponent,
arbitrary mixed decorations, short intervals, and OOOEE remain open.

## Current literature

**Extended:** the local D2, wave-bearing, and offset-anchor repairs
are assembled with a new specialization for the actual moving
zero-offset coefficients. Standard Fourier discrepancy and van der
Corput bounds are used as in Graham and Kolesnik (1991), linked in
the report. No literature-wide priority claim or new literature id.
The statement is an undecorated monomial kernel bound with a weaker
exponent than the historical research target.

## Branch budget

This transcribes the triage announced before writing the proof.

- **Target:** assemble the doubly differenced kernel uniformly in k.
- **Novelty hypothesis:** center the two growing coefficients at a
  short cutoff, then use the actual frequency and shift ranges.
- **Falsifier:** an error term or retained phase falls outside the
  proved derivative and partition bounds.
- **Already killed by?:** this is the dyadic kernel, not the rejected
  localization in [negative knowledge](../negative_knowledge.md).
  Signed cancellation and the frozen-floor correction are retained.
- **Existing machinery:** the three family estimates, exact carry
  identities, monotone counts, and classical derivative estimates.
- **Maximum Phase-0 scope:** prove or block this kernel assembly;
  leave the OOOEE mixed-mode transfer.
- **Promotion criterion:** account for every mode, coefficient weight,
  positive error, and partition boundary.
- **Stop criterion:** state the exact remaining gap if a term cannot
  be bounded. Do not auto-open the transfer question.

## Balanced-ternary formulation

The source integers and nested floors admit canonical balanced
ternary representations. The analytic proof uses real power functions
and exact integer carries, independently of the radix.

## Why BT may be relevant

Balanced ternary supplies integer bookkeeping elsewhere in the
laboratory; no cancellation in this proof is attributed to the radix.

## Candidate operations / invariants

- **EXACT — HUMAN PROOF**, J-paper-b-ddy-positive-majorant:
  approximate Delta_1 Delta_2Y as a value by one of four global
  smooth functions, then count the positive endpoint errors globally.
- **EXACT — HUMAN PROOF**, J-paper-b-kernel-moving-zero-offset:
  retain the moving M2/M3 centers in the phase and use their actual
  ranges to separate zero and nonzero integer Fourier modes.
- **EXACT — HUMAN PROOF**, J-paper-b-dyadic-kernel-127:
  sum the complete weighted inventory and both outer A-processes.

These tags denote AI-assisted written proofs, not independent review.

## Experiments

Runner: tools/validate_paper_b_kernel_assembly.py, optionally with
--output <json path>. The
[validation record](../theory/paper_b_kernel_assembly_validation.json)
contains 2500 exact master-identity cases, 2500 binary exponential
polynomial cases, 3567 centering cases, 7776 carry-inventory vertex
cases, 1875 four-corner telescope cases, 972 positive-envelope
stability cases, 517 curvature/product controls, and 34 rational
exponent controls. All pass.

The inventory checks include all five carry factors, mixed signs,
zero total Y frequency, and every argument in the exact basis
(Y,W_1,W_2,D). Finite algebra checks do not prove analytic cancellation.

## Conjectures

J-kernel-cancellation remains CONJECTURE at its original exponent
95/96. The new exponent 127/128 is a separate weaker theorem.
No new OOOEE correlation, mixed-mode theorem, or density is claimed.

## Counterexamples

No new refutation. The recorded individual-wave dominance failure,
incorrect offset coefficient, and localization obstruction remain
valid. This assembly avoids those inferences.

## Formalization

No Lean module is claimed. Independent mathematical review remains
outstanding. The written proofs and exact controls are the present
evidence.

## Results

The [proof](../theory/paper_b_kernel_assembly_report.md) establishes:
1. Positive errors E_J(Y), E_J(W_i), and E_J(Delta_1 Delta_2Y)
   total O(P^(23/24) log^C(P)) at J=P^(1/24).
2. Every retained phase has form (K10), with total coefficient mass
   O(log^7(P)) and explicitly bounded variation per center cell.
3. Nonzero total Y modes fit the wave-bearing theorem; nonzero
   offsets at t=0 fit the corrected offset-anchor theorem.
4. The actual moving-center zero-offset family has bound
   O_epsilon(P^(29/32+epsilon)), using coefficient -1215/256.
5. T_2 has exponent 31/32, T_1 has 63/64, and the dyadic kernel
   has 127/128. Both outer diagonal terms fit.

## Open questions

The OOOEE mixed-mode transfer must be proved separately. The stronger
95/96 kernel exponent, arbitrary decorations, and short intervals
are also unproved.

## Decision

**PROMOTE** the weaker dyadic kernel estimate and its auxiliary
assembly results. The complete inventory, error bounds, and partition
costs fit the stated exponent. The best next question is: what exact
mixed-mode family is needed for OOOEE, and does its phase reduce to
a controlled kernel family? This branch stops here.

## Publication assessment

Status: **THEOREM** (AI-assisted written proof; independent review
outstanding). Keep as a research supplement while the remaining
transfer and review are unresolved. The 27/32 manuscript, PDF,
metadata, and deposit package remain unchanged.

