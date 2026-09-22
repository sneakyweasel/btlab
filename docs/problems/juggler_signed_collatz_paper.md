# Paper E: Juggler and the signed Collatz maps

## Problem

Consolidate the completed comparison into a living publication with reproducible
proof data and explicit review boundaries.

## Exact statement

No new mathematical statement is introduced by this packaging branch.
The [manuscript](../theory/juggler_signed_collatz_note.md) states the global
orbit code, preservation of actual periods, modular-return counterfamily,
signed ancestor exponent 21/25, and the fixed-grid ceiling below 99/100.

## Current literature

Classical inputs: terras-1976-stopping-time,
bernstein-lagarias-1996-conjugacy-map,
krasikov-lagarias-2003-difference-inequalities,
boshernitzan-1994-hardy-fields, and the attributed M. Sharpe grid method.
The paper distinguishes these inputs from the signed adaptation and isolated
obstructions. Specialist priority review remains pending.

## Branch budget

- **Target:** a complete first manuscript and publication package.
- **Novelty hypothesis:** a coherent comparative presentation of completed results.
- **Falsifier:** a headline exceeding its proof or duplicating prior work.
- **Already killed by?:** coding alone as an arithmetic attack is closed;
  this publication documents that limitation and opens no replacement attack.
- **Existing machinery:** Papers A-D, existing Lean proofs, exact certificate.
- **Maximum Phase-0 scope:** manuscript, proof map, audit, typesetting, release kit.
- **Promotion criterion:** proofs mapped, local checks and visual review pass.
- **Stop criterion:** list outstanding independent review; do not open a branch.

## Balanced-ternary formulation

Not used. The comparison concerns parity coding and ordinary height.

## Why BT may be relevant

The laboratory hosts the work; no representation advantage is asserted.

## Candidate operations / invariants

The existing code, period, divisibility, capped ancestor counts, and reciprocal mass.
No theorem-ledger claim is duplicated merely because it enters a manuscript.

## Experiments

tools/check_paper_e.py checks the exact table, grid, small-orbit barrier,
rational code examples, and modular-return witnesses.
tools/build_paper_e.py builds and hashes the publication package.

## Conjectures

No new conjecture. Integer realization, growing-depth distribution, and fate-class
harmonic mass retain the open status stated in their source dossiers.

## Counterexamples

The manuscript includes H(3)=83/27, H(4)=H(6), the signed height-budget
counterexample, modular returns, the backward ray, and stopped moment loss.

## Formalization

Problems.JugglerCollatzPaper imports the existing modules.
AxiomCheckJugglerCollatzPaper audits 32 selected declarations.
PaperECompletion identifies the odd-time series with the residue-limit code,
proves the limiting-frequency and real-exponent statements, and proves both
finite full-tree identities and direct sums over minimal stopping words.
PaperEModularReturn proves Theorem 4.1's exact construction, denominator
formula, and unboundedness. The infinitude assembly is conditional on
BoxRecurrence, whose written equidistribution proof is not formalized.

The subsequent analytic-foundation phase adds
[WeylCancellation.lean](../../formal/BTCalculus/WeylCancellation.lean),
built on the finite inequality from the concurrent OOEE formalization.
It proves qualitative van der Corput for bounded complex sequences,
including the full-sum/overlap boundary conversion and the phase-difference
specialization. Its separate nine-theorem audit does not enlarge the
version 0.3.0 paper audit. The
[proof note](../theory/qualitative_weyl_cancellation_note.md) records the
precise hypotheses and remaining analytic obligations.

The first-derivative phase adds
[KusminLandau.lean](../../formal/BTCalculus/KusminLandau.lean) and
[SublinearPowerCancellation.lean](../../formal/BTCalculus/SublinearPowerCancellation.lean).
They prove the finite 1/delta estimate from monotone increments, its
continuous derivative form, and unconditional cancellation of averages
of exp(2*pi*i*c*n^theta) for every real c!=0 and 0<theta<1. All 25 theorems
have a separate dependency audit. The
[proof note](../theory/first_derivative_power_cancellation_note.md) maps
the argument and distinguishes this base case from the full mixed-power
family needed by Theorem 4.1.

## Results

Version 0.3.0 has a canonical manuscript, full proof narrative, bibliography,
author metadata, AI disclosure, formalization map, reviewer packet, version
policy, exact validation report, PDF/TeX build, and local deposit kit with
source-and-certificate archive.

The formal completion phase adds six audited statements with no new
mathematical conjecture. The series proof includes finite or empty odd-time
sets; the direct stopping-word sums are regrouped only after proving
summability. Local comparison confirms the target and cutoff quantifiers of
the signed ancestor theorem.

The Theorem 4.1 construction phase adds four audited results. It proves
all orbit conclusions for a sufficiently large box visit and proves
infinitely many distinct starts above every bound from BoxRecurrence.
The denominator results are unconditional. A complete formalization
still needs a proof of BoxRecurrence; no applicable equidistribution
theorem was found in the installed Mathlib. The conditional assembly
is recorded separately from the original unconditional theorem.

Qualitative cancellation now follows formally from vanishing averages of
every positive fixed-shift correlation. This removes the generic
differencing lemma from the remaining analytic work. Cancellation for
the full mixed-power family required by Theorem 4.1 and the passage to
simultaneous box visits are still unproved in Lean. The sublinear
single-power base case is now unconditional, including negative
coefficients and removal of a finite initial segment. The first-derivative
estimate itself retains no assumed variation or exponential-sum bound.

## Open questions

Independent statement coverage, written-proof review, and literature priority.
Prove simultaneous-box recurrence for the fixed rational-power vector.
Publication venue and deposit remain author decisions.

## Decision

**PROMOTE** the living paper and its reproducible publication package.
The notation-completion phase is also **PROMOTE**; it closes the four
smaller coverage categories. The exact-construction phase for Theorem 4.1
is also **PROMOTE**, with its analytic recurrence input explicitly open.
The qualitative-cancellation foundation is **PROMOTE** as formalization
progress on a classical input, with no new number-theoretic claim.
The first-derivative and sublinear-power phase is also **PROMOTE** as a
completed analytic formalization milestone. Higher powers, mixed phases,
and simultaneous recurrence remain the next proof obligations.
Best next question: can the required fixed-power simultaneous-box recurrence
be proved in Lean? No new arithmetic attack is opened.

## Publication assessment

**PAPER_CANDIDATE.** First complete preprint prepared locally, not deposited.
See the [build guide](../theory/PAPER_E_BUILD.md) and
[review record](../theory/paper_e_review.md).
